//! A basic user VP supports both non-validator and validator accounts.
//!
//! This VP currently provides a signature verification against a public key for
//! sending tokens (receiving tokens is permissive).
//!
//! It allows to bond, unbond and withdraw tokens to and from PoS system with a
//! valid signature(s).
//!
//! For validator a tx to change a validator's commission rate or metadata
//! requires a valid signature(s) only from the validator.
//!
//! Any other storage key changes are allowed only with a valid signature.

use namada_vp_prelude::storage::KeySeg;
use namada_vp_prelude::*;
use once_cell::unsync::Lazy;
use proof_of_stake::storage::{read_pos_params, validator_state_handle};
use proof_of_stake::storage_key::{
    is_bond_key, is_pos_key, is_unbond_key, is_validator_commission_rate_key,
    is_validator_metadata_key, is_validator_state_key,
};
use proof_of_stake::types::ValidatorState;

enum KeyType<'a> {
    Token { owner: &'a Address },
    PoS,
    Vp(&'a Address),
    Masp,
    PgfStward(&'a Address),
    GovernanceVote(&'a Address),
    Unknown,
}

impl<'a> From<&'a storage::Key> for KeyType<'a> {
    fn from(key: &'a storage::Key) -> KeyType<'a> {
        if let Some([_, owner]) = token::is_any_token_balance_key(key) {
            Self::Token { owner }
        } else if is_pos_key(key) {
            Self::PoS
        } else if gov_storage::keys::is_vote_key(key) {
            let voter_address = gov_storage::keys::get_voter_address(key);
            if let Some(address) = voter_address {
                Self::GovernanceVote(address)
            } else {
                Self::Unknown
            }
        } else if let Some(address) = pgf_storage::keys::is_stewards_key(key) {
            Self::PgfStward(address)
        } else if let Some(address) = key.is_validity_predicate() {
            Self::Vp(address)
        } else if token::is_masp_key(key) {
            Self::Masp
        } else {
            Self::Unknown
        }
    }
}

#[validity_predicate(gas = 137325)]
fn validate_tx(
    ctx: &Ctx,
    tx_data: Tx,
    addr: Address,
    keys_changed: BTreeSet<storage::Key>,
    verifiers: BTreeSet<Address>,
) -> VpResult {
    debug_log!(
        "vp_user called with user addr: {}, key_changed: {:?}, verifiers: {:?}",
        addr,
        keys_changed,
        verifiers
    );

    let valid_sig = Lazy::new(|| {
        matches!(verify_signatures(ctx, &tx_data, &addr), Ok(true))
    });

    if !is_valid_tx(ctx, &tx_data)? {
        return reject();
    }

    for key in keys_changed.iter() {
        let key_type: KeyType = key.into();
        let is_valid = match key_type {
            KeyType::Token { owner, .. } => {
                if owner == &addr {
                    let pre: token::Amount =
                        ctx.read_pre(key)?.unwrap_or_default();
                    let post: token::Amount =
                        ctx.read_post(key)?.unwrap_or_default();
                    let change = post.change() - pre.change();
                    // debit has to signed, credit doesn't
                    let valid = change.non_negative() || *valid_sig;
                    debug_log!(
                        "token key: {}, change: {:?}, valid_sig: {}, valid \
                         modification: {}",
                        key,
                        change,
                        *valid_sig,
                        valid
                    );
                    valid
                } else {
                    debug_log!(
                        "This address ({}) is not of owner ({}) of token key: \
                         {}",
                        addr,
                        owner,
                        key
                    );
                    // If this is not the owner, allow any change
                    true
                }
            }
            KeyType::PoS => {
                // Bond or unbond
                let bond_id =
                    is_bond_key(key).map(|(bond_id, _)| bond_id).or_else(
                        || is_unbond_key(key).map(|(bond_id, _, _)| bond_id),
                    );
                let valid_bond_or_unbond_change = match bond_id {
                    Some(bond_id) => {
                        // Bonds and unbonds changes for this address
                        // must be signed
                        bond_id.source != addr || *valid_sig
                    }
                    None => {
                        // Any other PoS changes are allowed without signature
                        true
                    }
                };
                // Commission rate changes must be signed by the validator
                let comm = is_validator_commission_rate_key(key);
                let valid_commission_rate_change = match comm {
                    Some((validator, _epoch)) => {
                        *validator == addr && *valid_sig
                    }
                    None => true,
                };
                // Metadata changes must be signed by the validator whose
                // metadata is manipulated
                let metadata = is_validator_metadata_key(key);
                let valid_metadata_change = match metadata {
                    Some(address) => *address == addr && *valid_sig,
                    None => true,
                };

                // Changes due to unjailing, deactivating, and reactivating are
                // marked by changes in validator state
                let state_change = is_validator_state_key(key);
                let valid_state_change =
                    match state_change {
                        Some((address, epoch)) => {
                            let params_pre = read_pos_params(&ctx.pre())?;
                            let state_pre = validator_state_handle(address)
                                .get(&ctx.pre(), epoch, &params_pre)?;

                            let params_post = read_pos_params(&ctx.post())?;
                            let state_post = validator_state_handle(address)
                                .get(&ctx.post(), epoch, &params_post)?;

                            match (state_pre, state_post) {
                                (Some(pre), Some(post)) => {
                                    if
                                    // Deactivation case
                                    (matches!(
                                    pre,
                                    ValidatorState::Consensus
                                        | ValidatorState::BelowCapacity
                                        | ValidatorState::BelowThreshold
                                ) && post == ValidatorState::Inactive)
                                // Reactivation case
                                || pre == ValidatorState::Inactive
                                    && post != ValidatorState::Inactive
                                // Unjail case
                                || pre == ValidatorState::Jailed
                                    && matches!(
                                        post,
                                        ValidatorState::Consensus
                                            | ValidatorState::BelowCapacity
                                            | ValidatorState::BelowThreshold
                                    ) {
                                        *address == addr && *valid_sig
                                    } else {
                                        true
                                    }
                                }
                                (None, Some(_post)) => {
                                    // Becoming a validator must be authorized
                                    *valid_sig
                                }
                                _ => true,
                            }
                        }
                        None => true,
                    };

                valid_bond_or_unbond_change
                    && valid_commission_rate_change
                    && valid_state_change
                    && valid_metadata_change
            }
            KeyType::GovernanceVote(voter) => {
                if voter == &addr {
                    *valid_sig
                } else {
                    true
                }
            }
            KeyType::PgfStward(address) => {
                if address == &addr {
                    *valid_sig
                } else {
                    true
                }
            }
            KeyType::Vp(owner) => {
                let has_post: bool = ctx.has_key_post(key)?;
                if owner == &addr {
                    if has_post {
                        let vp_hash: Vec<u8> =
                            ctx.read_bytes_post(key)?.unwrap();
                        *valid_sig && is_vp_whitelisted(ctx, &vp_hash)?
                    } else {
                        false
                    }
                } else {
                    let vp_hash: Vec<u8> = ctx.read_bytes_post(key)?.unwrap();
                    is_vp_whitelisted(ctx, &vp_hash)?
                }
            }
            KeyType::Masp => true,
            KeyType::Unknown => {
                if key.segments.get(0) == Some(&addr.to_db_key()) {
                    // Unknown changes to this address space require a valid
                    // signature
                    *valid_sig
                } else {
                    // Unknown changes anywhere else are permitted
                    true
                }
            }
        };
        if !is_valid {
            debug_log!("key {} modification failed vp", key);
            return reject();
        }
    }

    accept()
}

#[cfg(test)]
mod tests {
    use address::testing::arb_non_internal_address;
    use namada::ledger::pos::{GenesisValidator, PosParams};
    use namada::proto::{Code, Data, Signature};
    use namada::types::dec::Dec;
    use namada::types::storage::Epoch;
    use namada::types::transaction::{self, TxType};
    use namada_test_utils::TestWasms;
    // Use this as `#[test]` annotation to enable logging
    use namada_tests::log::test;
    use namada_tests::native_vp::pos::init_pos;
    use namada_tests::tx::{self, tx_host_env, TestTxEnv};
    use namada_tests::vp::vp_host_env::storage::Key;
    use namada_tests::vp::*;
    use namada_tx_prelude::{StorageWrite, TxEnv};
    use namada_vp_prelude::account::AccountPublicKeysMap;
    use namada_vp_prelude::key::RefTo;
    use proptest::prelude::*;
    use storage::testing::arb_account_storage_key_no_vp;

    use super::*;

    /// Test that no-op transaction (i.e. no storage modifications) accepted.
    #[test]
    fn test_no_op_transaction() {
        let mut tx_data = Tx::from_type(TxType::Raw);
        tx_data.set_data(Data::new(vec![]));
        let addr: Address = address::testing::established_address_1();
        let keys_changed: BTreeSet<storage::Key> = BTreeSet::default();
        let verifiers: BTreeSet<Address> = BTreeSet::default();

        // The VP env must be initialized before calling `validate_tx`
        vp_host_env::init();

        assert!(
            validate_tx(&CTX, tx_data, addr, keys_changed, verifiers).unwrap()
        );
    }

    /// Test that a credit transfer is accepted.
    #[test]
    fn test_credit_transfer_accepted() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();

        let vp_owner = address::testing::established_address_1();
        let source = address::testing::established_address_2();
        let token = address::nam();
        let amount = token::Amount::from_uint(10_098_123, 0).unwrap();

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner, &source, &token]);

        // Credit the tokens to the source before running the transaction to be
        // able to transfer from it
        tx_env.credit_tokens(&source, &token, amount);
        // write the denomination of NAM into storage
        storage_api::token::write_denom(
            &mut tx_env.wl_storage,
            &token,
            token::NATIVE_MAX_DECIMAL_PLACES.into(),
        )
        .unwrap();

        let amount = token::DenominatedAmount {
            amount,
            denom: token::NATIVE_MAX_DECIMAL_PLACES.into(),
        };
        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            // Apply transfer in a transaction
            tx_host_env::token::transfer(
                tx::ctx(),
                &source,
                address,
                &token,
                amount,
            )
            .unwrap();
        });

        let vp_env = vp_host_env::take();
        let mut tx_data = Tx::from_type(TxType::Raw);
        tx_data.set_data(Data::new(vec![]));
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            validate_tx(&CTX, tx_data, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a debit transfer without a valid signature is rejected.
    #[test]
    fn test_unsigned_debit_transfer_rejected() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();

        let vp_owner = address::testing::established_address_1();
        let target = address::testing::established_address_2();
        let token = address::nam();
        let amount = token::Amount::from_uint(10_098_123, 0).unwrap();

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner, &target, &token]);
        // write the denomination of NAM into storage
        storage_api::token::write_denom(
            &mut tx_env.wl_storage,
            &token,
            token::NATIVE_MAX_DECIMAL_PLACES.into(),
        )
        .unwrap();

        // Credit the tokens to the VP owner before running the transaction to
        // be able to transfer from it
        tx_env.credit_tokens(&vp_owner, &token, amount);

        let amount = token::DenominatedAmount {
            amount,
            denom: token::NATIVE_MAX_DECIMAL_PLACES.into(),
        };
        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            // Apply transfer in a transaction
            tx_host_env::token::transfer(
                tx::ctx(),
                address,
                &target,
                &token,
                amount,
            )
            .unwrap();
        });

        let vp_env = vp_host_env::take();
        let mut tx_data = Tx::from_type(TxType::Raw);
        tx_data.set_data(Data::new(vec![]));
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            !validate_tx(&CTX, tx_data, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a debit transfer with a valid signature is accepted.
    #[test]
    fn test_signed_debit_transfer_accepted() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();

        let vp_owner = address::testing::established_address_1();
        let keypair = key::testing::keypair_1();
        let public_key = keypair.ref_to();
        let target = address::testing::established_address_2();
        let token = address::nam();
        let amount = token::Amount::from_uint(10_098_123, 0).unwrap();

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner, &target, &token]);
        tx_env.init_account_storage(&vp_owner, vec![public_key.clone()], 1);

        // Credit the tokens to the VP owner before running the transaction to
        // be able to transfer from it
        tx_env.credit_tokens(&vp_owner, &token, amount);
        // write the denomination of NAM into storage
        storage_api::token::write_denom(
            &mut tx_env.wl_storage,
            &token,
            token::NATIVE_MAX_DECIMAL_PLACES.into(),
        )
        .unwrap();

        let amount = token::DenominatedAmount {
            amount,
            denom: token::NATIVE_MAX_DECIMAL_PLACES.into(),
        };

        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            // Apply transfer in a transaction
            tx_host_env::token::transfer(
                tx::ctx(),
                address,
                &target,
                &token,
                amount,
            )
            .unwrap();
        });

        let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

        let mut vp_env = vp_host_env::take();
        let mut tx = vp_env.tx.clone();
        tx.set_data(Data::new(vec![]));
        tx.set_code(Code::new(vec![], None));
        tx.add_section(Section::Signature(Signature::new(
            vec![tx.raw_header_hash()],
            pks_map.index_secret_keys(vec![keypair]),
            None,
        )));
        let signed_tx = tx.clone();
        vp_env.tx = signed_tx.clone();
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            validate_tx(&CTX, signed_tx, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a non-validator PoS action that must be authorized is rejected
    /// without a valid signature.
    #[test]
    fn test_unsigned_non_validator_pos_action_rejected() {
        // Init PoS genesis
        let pos_params = PosParams::default();
        let validator = address::testing::established_address_3();
        let initial_stake = token::Amount::from_uint(10_098_123, 0).unwrap();
        let consensus_key = key::testing::keypair_2().ref_to();
        let protocol_key = key::testing::keypair_1().ref_to();
        let eth_cold_key = key::testing::keypair_3().ref_to();
        let eth_hot_key = key::testing::keypair_4().ref_to();
        let commission_rate = Dec::new(5, 2).unwrap();
        let max_commission_rate_change = Dec::new(1, 2).unwrap();

        let genesis_validators = [GenesisValidator {
            address: validator.clone(),
            tokens: initial_stake,
            consensus_key,
            protocol_key,
            commission_rate,
            max_commission_rate_change,
            eth_hot_key,
            eth_cold_key,
            metadata: Default::default(),
        }];

        init_pos(&genesis_validators[..], &pos_params, Epoch(0));

        // Initialize a tx environment
        let mut tx_env = tx_host_env::take();

        let secret_key = key::testing::keypair_1();
        let public_key = secret_key.ref_to();
        let vp_owner: Address = address::testing::established_address_2();
        let target = address::testing::established_address_3();
        let token = address::nam();
        let amount = token::Amount::from_uint(10_098_123, 0).unwrap();
        let bond_amount = token::Amount::from_uint(5_098_123, 0).unwrap();
        let unbond_amount = token::Amount::from_uint(3_098_123, 0).unwrap();

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&target, &token]);
        tx_env.init_account_storage(&vp_owner, vec![public_key], 1);
        // write the denomination of NAM into storage
        storage_api::token::write_denom(
            &mut tx_env.wl_storage,
            &token,
            token::NATIVE_MAX_DECIMAL_PLACES.into(),
        )
        .unwrap();

        // Credit the tokens to the VP owner before running the transaction to
        // be able to transfer from it
        tx_env.credit_tokens(&vp_owner, &token, amount);

        // Initialize VP environment from non-validator PoS actions
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |_address| {
            // Bond the tokens, then unbond some of them
            tx::ctx()
                .bond_tokens(Some(&vp_owner), &validator, bond_amount)
                .unwrap();
            tx::ctx()
                .unbond_tokens(Some(&vp_owner), &validator, unbond_amount)
                .unwrap();
        });

        let vp_env = vp_host_env::take();
        let mut tx_data = Tx::from_type(TxType::Raw);
        tx_data.set_data(Data::new(vec![]));
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            !validate_tx(&CTX, tx_data, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a PoS action to become validator that must be authorized is
    /// rejected without a valid signature.
    #[test]
    fn test_unsigned_become_validator_pos_action_rejected() {
        // Init PoS genesis
        let pos_params = PosParams::default();
        let validator = address::testing::established_address_3();
        let initial_stake = token::Amount::from_uint(10_098_123, 0).unwrap();
        let consensus_key = key::testing::keypair_2().ref_to();
        let protocol_key = key::testing::keypair_1().ref_to();
        let eth_cold_key = key::testing::keypair_3().ref_to();
        let eth_hot_key = key::testing::keypair_4().ref_to();
        let commission_rate = Dec::new(5, 2).unwrap();
        let max_commission_rate_change = Dec::new(1, 2).unwrap();

        let genesis_validators = [GenesisValidator {
            address: validator,
            tokens: initial_stake,
            consensus_key,
            protocol_key,
            commission_rate,
            max_commission_rate_change,
            eth_hot_key,
            eth_cold_key,
            metadata: Default::default(),
        }];

        init_pos(&genesis_validators[..], &pos_params, Epoch(0));

        // Initialize a tx environment
        let mut tx_env = tx_host_env::take();

        let secret_key = key::testing::keypair_1();
        let public_key = secret_key.ref_to();
        let vp_owner: Address = address::testing::established_address_2();

        // Spawn the accounts to be able to modify their storage
        tx_env.init_account_storage(&vp_owner, vec![public_key], 1);

        // Initialize VP environment from PoS action to become a validator
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            let consensus_key = key::common::PublicKey::Ed25519(
                key::testing::gen_keypair::<key::ed25519::SigScheme>().ref_to(),
            );
            let protocol_key = key::common::PublicKey::Ed25519(
                key::testing::gen_keypair::<key::ed25519::SigScheme>().ref_to(),
            );
            let eth_cold_key =
                key::testing::gen_keypair::<key::secp256k1::SigScheme>()
                    .ref_to();
            let eth_hot_key =
                key::testing::gen_keypair::<key::secp256k1::SigScheme>()
                    .ref_to();
            let commission_rate = Dec::new(5, 2).unwrap();
            let max_commission_rate_change = Dec::new(1, 2).unwrap();
            let args = transaction::pos::BecomeValidator {
                address: address.clone(),
                consensus_key,
                eth_cold_key,
                eth_hot_key,
                protocol_key,
                commission_rate,
                max_commission_rate_change,
                email: "cucumber@tastes.good".to_string(),
                description: None,
                website: None,
                discord_handle: None,
            };
            tx::ctx().become_validator(args).unwrap();
        });

        let vp_env = vp_host_env::take();
        let mut tx_data = Tx::from_type(TxType::Raw);
        tx_data.set_data(Data::new(vec![]));
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            !validate_tx(&CTX, tx_data, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a validator PoS action that must be authorized is rejected
    /// without a valid signature.
    #[test]
    fn test_unsigned_validator_pos_action_rejected() {
        // Init PoS genesis
        let pos_params = PosParams::default();
        let validator = address::testing::established_address_3();
        let initial_stake = token::Amount::from_uint(10_098_123, 0).unwrap();
        let consensus_key = key::testing::keypair_2().ref_to();
        let protocol_key = key::testing::keypair_1().ref_to();
        let eth_cold_key = key::testing::keypair_3().ref_to();
        let eth_hot_key = key::testing::keypair_4().ref_to();
        let commission_rate = Dec::new(5, 2).unwrap();
        let max_commission_rate_change = Dec::new(1, 2).unwrap();

        let genesis_validators = [GenesisValidator {
            address: validator.clone(),
            tokens: initial_stake,
            consensus_key,
            protocol_key,
            commission_rate,
            max_commission_rate_change,
            eth_hot_key,
            eth_cold_key,
            metadata: Default::default(),
        }];

        init_pos(&genesis_validators[..], &pos_params, Epoch(0));

        // Initialize a tx environment
        let mut tx_env = tx_host_env::take();

        let secret_key = key::testing::keypair_1();
        let public_key = secret_key.ref_to();
        let target = address::testing::established_address_3();
        let token = address::nam();
        let amount = token::Amount::from_uint(10_098_123, 0).unwrap();
        let bond_amount = token::Amount::from_uint(5_098_123, 0).unwrap();
        let unbond_amount = token::Amount::from_uint(3_098_123, 0).unwrap();

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&target, &token]);
        tx_env.init_account_storage(&validator, vec![public_key], 1);
        // write the denomination of NAM into storage
        storage_api::token::write_denom(
            &mut tx_env.wl_storage,
            &token,
            token::NATIVE_MAX_DECIMAL_PLACES.into(),
        )
        .unwrap();

        // Credit the tokens to the validator before running the transaction to
        // be able to transfer from it
        tx_env.credit_tokens(&validator, &token, amount);

        // Validator PoS actions
        vp_host_env::init_from_tx(validator.clone(), tx_env, |_address| {
            // Bond the tokens, then unbond some of them
            tx::ctx()
                .bond_tokens(Some(&validator), &validator, bond_amount)
                .unwrap();
            tx::ctx()
                .unbond_tokens(Some(&validator), &validator, unbond_amount)
                .unwrap();
            tx::ctx().deactivate_validator(&validator).unwrap();
            tx::ctx()
                .change_validator_metadata(
                    &validator,
                    Some("email".to_owned()),
                    Some("desc".to_owned()),
                    Some("website".to_owned()),
                    Some("discord".to_owned()),
                    Some(Dec::new(6, 2).unwrap()),
                )
                .unwrap();
        });

        let vp_env = vp_host_env::take();
        let mut tx_data = Tx::from_type(TxType::Raw);
        tx_data.set_data(Data::new(vec![]));
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            !validate_tx(&CTX, tx_data, validator, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a non-validator PoS action that must be authorized is accepted
    /// with a valid signature.
    #[test]
    fn test_signed_non_validator_pos_action_accepted() {
        // Init PoS genesis
        let pos_params = PosParams::default();
        let validator = address::testing::established_address_3();
        let initial_stake = token::Amount::from_uint(10_098_123, 0).unwrap();
        let consensus_key = key::testing::keypair_2().ref_to();
        let protocol_key = key::testing::keypair_1().ref_to();
        let commission_rate = Dec::new(5, 2).unwrap();
        let max_commission_rate_change = Dec::new(1, 2).unwrap();

        let genesis_validators = [GenesisValidator {
            address: validator.clone(),
            tokens: initial_stake,
            consensus_key,
            protocol_key,
            commission_rate,
            max_commission_rate_change,
            eth_hot_key: key::common::PublicKey::Secp256k1(
                key::testing::gen_keypair::<key::secp256k1::SigScheme>()
                    .ref_to(),
            ),
            eth_cold_key: key::common::PublicKey::Secp256k1(
                key::testing::gen_keypair::<key::secp256k1::SigScheme>()
                    .ref_to(),
            ),
            metadata: Default::default(),
        }];

        init_pos(&genesis_validators[..], &pos_params, Epoch(0));

        // Initialize a tx environment
        let mut tx_env = tx_host_env::take();

        let secret_key = key::testing::keypair_1();
        let public_key = secret_key.ref_to();
        let vp_owner: Address = address::testing::established_address_2();
        let target = address::testing::established_address_3();
        let token = address::nam();
        let amount = token::Amount::from_uint(10_098_123, 0).unwrap();
        let bond_amount = token::Amount::from_uint(5_098_123, 0).unwrap();
        let unbond_amount = token::Amount::from_uint(3_098_123, 0).unwrap();

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&target, &token]);
        tx_env.init_account_storage(&vp_owner, vec![public_key.clone()], 1);

        // write the denomination of NAM into storage
        storage_api::token::write_denom(
            &mut tx_env.wl_storage,
            &token,
            token::NATIVE_MAX_DECIMAL_PLACES.into(),
        )
        .unwrap();

        // Credit the tokens to the VP owner before running the transaction to
        // be able to transfer from it
        tx_env.credit_tokens(&vp_owner, &token, amount);

        // Initialize VP environment from non-validator PoS actions
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |_address| {
            // Bond the tokens, then unbond some of them
            tx::ctx()
                .bond_tokens(Some(&vp_owner), &validator, bond_amount)
                .unwrap();
            tx::ctx()
                .unbond_tokens(Some(&vp_owner), &validator, unbond_amount)
                .unwrap();
        });

        let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

        let mut vp_env = vp_host_env::take();
        let mut tx = vp_env.tx.clone();
        tx.set_data(Data::new(vec![]));
        tx.set_code(Code::new(vec![], None));
        tx.add_section(Section::Signature(Signature::new(
            vec![tx.raw_header_hash()],
            pks_map.index_secret_keys(vec![secret_key]),
            None,
        )));
        let signed_tx = tx.clone();
        vp_env.tx = signed_tx.clone();
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            validate_tx(&CTX, signed_tx, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a signed PoS action to become validator that must be
    /// authorized is accepted with a valid signature.
    #[test]
    fn test_signed_become_validator_pos_action_accepted() {
        // Init PoS genesis
        let pos_params = PosParams::default();
        let validator = address::testing::established_address_3();
        let initial_stake = token::Amount::from_uint(10_098_123, 0).unwrap();
        let consensus_key = key::testing::keypair_2().ref_to();
        let protocol_key = key::testing::keypair_1().ref_to();
        let eth_cold_key = key::testing::keypair_3().ref_to();
        let eth_hot_key = key::testing::keypair_4().ref_to();
        let commission_rate = Dec::new(5, 2).unwrap();
        let max_commission_rate_change = Dec::new(1, 2).unwrap();

        let genesis_validators = [GenesisValidator {
            address: validator,
            tokens: initial_stake,
            consensus_key,
            protocol_key,
            commission_rate,
            max_commission_rate_change,
            eth_hot_key,
            eth_cold_key,
            metadata: Default::default(),
        }];

        init_pos(&genesis_validators[..], &pos_params, Epoch(0));

        // Initialize a tx environment
        let mut tx_env = tx_host_env::take();

        let secret_key = key::testing::keypair_1();
        let public_key = secret_key.ref_to();
        let vp_owner: Address = address::testing::established_address_2();

        // Spawn the accounts to be able to modify their storage
        tx_env.init_account_storage(&vp_owner, vec![public_key.clone()], 1);

        // Initialize VP environment from PoS action to become a validator
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            let consensus_key = key::common::PublicKey::Ed25519(
                key::testing::gen_keypair::<key::ed25519::SigScheme>().ref_to(),
            );
            let protocol_key = key::common::PublicKey::Ed25519(
                key::testing::gen_keypair::<key::ed25519::SigScheme>().ref_to(),
            );
            let eth_cold_key =
                key::testing::gen_keypair::<key::secp256k1::SigScheme>()
                    .ref_to();
            let eth_hot_key =
                key::testing::gen_keypair::<key::secp256k1::SigScheme>()
                    .ref_to();
            let commission_rate = Dec::new(5, 2).unwrap();
            let max_commission_rate_change = Dec::new(1, 2).unwrap();
            let args = transaction::pos::BecomeValidator {
                address: address.clone(),
                consensus_key,
                eth_cold_key,
                eth_hot_key,
                protocol_key,
                commission_rate,
                max_commission_rate_change,
                email: "cucumber@tastes.good".to_string(),
                description: None,
                website: None,
                discord_handle: None,
            };
            tx::ctx().become_validator(args).unwrap();
        });

        let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

        let mut vp_env = vp_host_env::take();
        let mut tx = vp_env.tx.clone();
        tx.set_data(Data::new(vec![]));
        tx.set_code(Code::new(vec![], None));
        tx.add_section(Section::Signature(Signature::new(
            vec![tx.raw_header_hash()],
            pks_map.index_secret_keys(vec![secret_key]),
            None,
        )));
        let signed_tx = tx.clone();
        vp_env.tx = signed_tx.clone();
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            validate_tx(&CTX, signed_tx, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a validator PoS action that must be authorized is accepted
    /// with a valid signature.
    #[test]
    fn test_signed_validator_pos_action_accepted() {
        // Init PoS genesis
        let pos_params = PosParams::default();
        let validator = address::testing::established_address_3();
        let initial_stake = token::Amount::from_uint(10_098_123, 0).unwrap();
        let consensus_key = key::testing::keypair_2().ref_to();
        let protocol_key = key::testing::keypair_1().ref_to();
        let commission_rate = Dec::new(5, 2).unwrap();
        let max_commission_rate_change = Dec::new(1, 2).unwrap();

        let genesis_validators = [GenesisValidator {
            address: validator.clone(),
            tokens: initial_stake,
            consensus_key,
            protocol_key,
            commission_rate,
            max_commission_rate_change,
            eth_hot_key: key::common::PublicKey::Secp256k1(
                key::testing::gen_keypair::<key::secp256k1::SigScheme>()
                    .ref_to(),
            ),
            eth_cold_key: key::common::PublicKey::Secp256k1(
                key::testing::gen_keypair::<key::secp256k1::SigScheme>()
                    .ref_to(),
            ),
            metadata: Default::default(),
        }];

        init_pos(&genesis_validators[..], &pos_params, Epoch(0));

        // Initialize a tx environment
        let mut tx_env = tx_host_env::take();

        let secret_key = key::testing::keypair_1();
        let public_key = secret_key.ref_to();
        let target = address::testing::established_address_3();
        let token = address::nam();
        let amount = token::Amount::from_uint(10_098_123, 0).unwrap();
        let bond_amount = token::Amount::from_uint(5_098_123, 0).unwrap();
        let unbond_amount = token::Amount::from_uint(3_098_123, 0).unwrap();

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&target, &token]);
        tx_env.init_account_storage(&validator, vec![public_key.clone()], 1);

        // write the denomination of NAM into storage
        storage_api::token::write_denom(
            &mut tx_env.wl_storage,
            &token,
            token::NATIVE_MAX_DECIMAL_PLACES.into(),
        )
        .unwrap();

        // Credit the tokens to the VP owner before running the transaction to
        // be able to transfer from it
        tx_env.credit_tokens(&validator, &token, amount);

        // Validator PoS actions
        vp_host_env::init_from_tx(validator.clone(), tx_env, |_address| {
            // Bond the tokens, then unbond some of them
            tx::ctx()
                .bond_tokens(Some(&validator), &validator, bond_amount)
                .unwrap();
            tx::ctx()
                .unbond_tokens(Some(&validator), &validator, unbond_amount)
                .unwrap();
            tx::ctx().deactivate_validator(&validator).unwrap();
            tx::ctx()
                .change_validator_metadata(
                    &validator,
                    Some("email".to_owned()),
                    Some("desc".to_owned()),
                    Some("website".to_owned()),
                    Some("discord".to_owned()),
                    Some(Dec::new(6, 2).unwrap()),
                )
                .unwrap();
        });

        let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

        let mut vp_env = vp_host_env::take();
        let mut tx = vp_env.tx.clone();
        tx.set_data(Data::new(vec![]));
        tx.set_code(Code::new(vec![], None));
        tx.add_section(Section::Signature(Signature::new(
            vec![tx.raw_header_hash()],
            pks_map.index_secret_keys(vec![secret_key]),
            None,
        )));
        let signed_tx = tx.clone();
        vp_env.tx = signed_tx.clone();
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            validate_tx(&CTX, signed_tx, validator, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a transfer on with accounts other than self is accepted.
    #[test]
    fn test_transfer_between_other_parties_accepted() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();

        let vp_owner = address::testing::established_address_1();
        let source = address::testing::established_address_2();
        let target = address::testing::established_address_3();
        let token = address::nam();
        let amount = token::Amount::from_uint(10_098_123, 0).unwrap();

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner, &source, &target, &token]);

        // Credit the tokens to the VP owner before running the transaction to
        // be able to transfer from it
        tx_env.credit_tokens(&source, &token, amount);

        let amount = token::DenominatedAmount {
            amount,
            denom: token::NATIVE_MAX_DECIMAL_PLACES.into(),
        };

        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            tx::ctx().insert_verifier(address).unwrap();
            // Apply transfer in a transaction
            tx_host_env::token::transfer(
                tx::ctx(),
                &source,
                &target,
                &token,
                amount,
            )
            .unwrap();
        });

        let vp_env = vp_host_env::take();
        let mut tx_data = Tx::from_type(TxType::Raw);
        tx_data.set_data(Data::new(vec![]));
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            validate_tx(&CTX, tx_data, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    prop_compose! {
        /// Generates an account address and a storage key inside its storage.
        fn arb_account_storage_subspace_key()
            // Generate an address
            (address in arb_non_internal_address())
            // Generate a storage key other than its VP key (VP cannot be
            // modified directly via `write`, it has to be modified via
            // `tx::update_validity_predicate`.
            (storage_key in arb_account_storage_key_no_vp(address.clone()),
            // Use the generated address too
            address in Just(address))
        -> (Address, Key) {
            (address, storage_key)
        }
    }

    proptest! {
        /// Test that an unsigned tx that performs arbitrary storage writes or
        /// deletes to  the account is rejected.
        #[test]
        fn test_unsigned_arb_storage_write_rejected(
            (vp_owner, storage_key) in arb_account_storage_subspace_key(),
            // Generate bytes to write. If `None`, delete from the key instead
            storage_value in any::<Option<Vec<u8>>>(),
        ) {
            // Initialize a tx environment
            let mut tx_env = TestTxEnv::default();

            // Spawn all the accounts in the storage key to be able to modify
            // their storage
            let storage_key_addresses = storage_key.find_addresses();
            tx_env.spawn_accounts(storage_key_addresses);

            // Initialize VP environment from a transaction
            vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |_address| {
                // Write or delete some data in the transaction
                if let Some(value) = &storage_value {
                    tx::ctx().write(&storage_key, value).unwrap();
                } else {
                    tx::ctx().delete(&storage_key).unwrap();
                }
            });

            let vp_env = vp_host_env::take();
            let mut tx_data = Tx::from_type(TxType::Raw);
            tx_data.set_data(Data::new(vec![]));
            let keys_changed: BTreeSet<storage::Key> =
                vp_env.all_touched_storage_keys();
            let verifiers: BTreeSet<Address> = BTreeSet::default();
            vp_host_env::set(vp_env);
            assert!(!validate_tx(&CTX, tx_data, vp_owner, keys_changed, verifiers).unwrap());
        }
    }

    proptest! {
            /// Test that a signed tx that performs arbitrary storage writes or
            /// deletes to the account is accepted.
            #[test]
            fn test_signed_arb_storage_write(
                (vp_owner, storage_key) in arb_account_storage_subspace_key(),
                // Generate bytes to write. If `None`, delete from the key instead
                storage_value in any::<Option<Vec<u8>>>(),
            ) {
                // Initialize a tx environment
                let mut tx_env = TestTxEnv::default();

                let keypair = key::testing::keypair_1();
                let public_key = keypair.ref_to();

                // Spawn all the accounts in the storage key to be able to modify
                // their storage
                let storage_key_addresses = storage_key.find_addresses();
                tx_env.spawn_accounts(storage_key_addresses);
                tx_env.init_account_storage(&vp_owner, vec![public_key.clone()], 1);

                // Initialize VP environment from a transaction
                vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |_address| {
                    // Write or delete some data in the transaction
                    if let Some(value) = &storage_value {
                        tx::ctx().write(&storage_key, value).unwrap();
                    } else {
                        tx::ctx().delete(&storage_key).unwrap();
                    }
                });

                let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

                let mut vp_env = vp_host_env::take();
                let mut tx = vp_env.tx.clone();
                tx.set_code(Code::new(vec![], None));
                tx.set_data(Data::new(vec![]));
                tx.add_section(Section::Signature(Signature::new(
    vec![                tx.raw_header_hash()],
                    pks_map.index_secret_keys(vec![keypair]),
                    None,
                )));
                let signed_tx = tx.clone();
                vp_env.tx = signed_tx.clone();
                let keys_changed: BTreeSet<storage::Key> =
                vp_env.all_touched_storage_keys();
                let verifiers: BTreeSet<Address> = BTreeSet::default();
                vp_host_env::set(vp_env);
                assert!(validate_tx(&CTX, signed_tx, vp_owner, keys_changed, verifiers).unwrap());
            }
        }

    /// Test that a validity predicate update without a valid signature is
    /// rejected.
    #[test]
    fn test_unsigned_vp_update_rejected() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();

        let vp_owner = address::testing::established_address_1();
        let vp_code = TestWasms::VpAlwaysTrue.read_bytes();
        let vp_hash = sha256(&vp_code);
        // for the update
        tx_env.store_wasm_code(vp_code);

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner]);

        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            // Update VP in a transaction
            tx::ctx()
                .update_validity_predicate(address, vp_hash, &None)
                .unwrap();
        });

        let vp_env = vp_host_env::take();
        let mut tx_data = Tx::from_type(TxType::Raw);
        tx_data.set_data(Data::new(vec![]));
        tx_data.set_code(Code::new(vec![], None));
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            !validate_tx(&CTX, tx_data, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a validity predicate update with a valid signature is
    /// accepted.
    #[test]
    fn test_signed_vp_update_accepted() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();
        tx_env.init_parameters(None, None, None, None);

        let vp_owner = address::testing::established_address_1();
        let keypair = key::testing::keypair_1();
        let public_key = keypair.ref_to();
        let vp_code = TestWasms::VpAlwaysTrue.read_bytes();
        let vp_hash = sha256(&vp_code);
        // for the update
        tx_env.store_wasm_code(vp_code);

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner]);
        tx_env.init_account_storage(&vp_owner, vec![public_key.clone()], 1);

        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            // Update VP in a transaction
            tx::ctx()
                .update_validity_predicate(address, vp_hash, &None)
                .unwrap();
        });

        let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

        let mut vp_env = vp_host_env::take();
        let mut tx = vp_env.tx.clone();
        tx.set_data(Data::new(vec![]));
        tx.set_code(Code::new(vec![], None));
        tx.add_section(Section::Signature(Signature::new(
            vec![tx.raw_header_hash()],
            pks_map.index_secret_keys(vec![keypair]),
            None,
        )));
        let signed_tx = tx.clone();
        vp_env.tx = signed_tx.clone();
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            validate_tx(&CTX, signed_tx, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a validity predicate update is rejected if not whitelisted
    #[test]
    fn test_signed_vp_update_not_whitelisted_rejected() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();
        tx_env.init_parameters(
            None,
            Some(vec!["some_hash".to_string()]),
            None,
            None,
        );

        let vp_owner = address::testing::established_address_1();
        let keypair = key::testing::keypair_1();
        let public_key = keypair.ref_to();
        let vp_code = TestWasms::VpAlwaysTrue.read_bytes();
        let vp_hash = sha256(&vp_code);
        // for the update
        tx_env.store_wasm_code(vp_code);

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner]);
        tx_env.init_account_storage(&vp_owner, vec![public_key.clone()], 1);

        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            // Update VP in a transaction
            tx::ctx()
                .update_validity_predicate(address, vp_hash, &None)
                .unwrap();
        });

        let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

        let mut vp_env = vp_host_env::take();
        let mut tx = vp_env.tx.clone();
        tx.set_data(Data::new(vec![]));
        tx.set_code(Code::new(vec![], None));
        tx.add_section(Section::Signature(Signature::new(
            vec![tx.raw_header_hash()],
            pks_map.index_secret_keys(vec![keypair]),
            None,
        )));
        let signed_tx = tx.clone();
        vp_env.tx = signed_tx.clone();
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            !validate_tx(&CTX, signed_tx, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a validity predicate update is accepted if whitelisted
    #[test]
    fn test_signed_vp_update_whitelisted_accepted() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();

        let vp_owner = address::testing::established_address_1();
        let keypair = key::testing::keypair_1();
        let public_key = keypair.ref_to();
        let vp_code = TestWasms::VpAlwaysTrue.read_bytes();
        let vp_hash = sha256(&vp_code);
        // for the update
        tx_env.store_wasm_code(vp_code);

        tx_env.init_parameters(
            None,
            Some(vec![vp_hash.to_string()]),
            None,
            None,
        );

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner]);
        tx_env.init_account_storage(&vp_owner, vec![public_key.clone()], 1);

        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            // Update VP in a transaction
            tx::ctx()
                .update_validity_predicate(address, vp_hash, &None)
                .unwrap();
        });

        let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

        let mut vp_env = vp_host_env::take();
        let mut tx = vp_env.tx.clone();
        tx.set_data(Data::new(vec![]));
        tx.set_code(Code::new(vec![], None));
        tx.add_section(Section::Signature(Signature::new(
            vec![tx.raw_header_hash()],
            pks_map.index_secret_keys(vec![keypair]),
            None,
        )));
        let signed_tx = tx.clone();
        vp_env.tx = signed_tx.clone();
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            validate_tx(&CTX, signed_tx, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    /// Test that a tx is rejected if not whitelisted
    #[test]
    fn test_tx_not_whitelisted_rejected() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();

        let vp_owner = address::testing::established_address_1();
        let keypair = key::testing::keypair_1();
        let public_key = keypair.ref_to();
        let vp_code = TestWasms::VpAlwaysTrue.read_bytes();
        let vp_hash = sha256(&vp_code);
        // for the update
        tx_env.store_wasm_code(vp_code);

        tx_env.init_parameters(
            None,
            Some(vec![vp_hash.to_string()]),
            Some(vec!["some_hash".to_string()]),
            None,
        );

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner]);
        tx_env.init_account_storage(&vp_owner, vec![public_key.clone()], 1);

        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            // Update VP in a transaction
            tx::ctx()
                .update_validity_predicate(address, vp_hash, &None)
                .unwrap();
        });

        let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

        let mut vp_env = vp_host_env::take();
        let mut tx = vp_env.tx.clone();
        tx.set_data(Data::new(vec![]));
        tx.set_code(Code::new(vec![], None));
        tx.add_section(Section::Signature(Signature::new(
            vec![tx.raw_header_hash()],
            pks_map.index_secret_keys(vec![keypair]),
            None,
        )));
        let signed_tx = tx.clone();
        vp_env.tx = signed_tx.clone();
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            !validate_tx(&CTX, signed_tx, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }

    #[test]
    fn test_tx_whitelisted_accepted() {
        // Initialize a tx environment
        let mut tx_env = TestTxEnv::default();

        let vp_owner = address::testing::established_address_1();
        let keypair = key::testing::keypair_1();
        let public_key = keypair.ref_to();
        let vp_code = TestWasms::VpAlwaysTrue.read_bytes();
        let vp_hash = sha256(&vp_code);
        // for the update
        tx_env.store_wasm_code(vp_code);

        // hardcoded hash of VP_ALWAYS_TRUE_WASM
        tx_env.init_parameters(
            None,
            Some(vec![vp_hash.to_string()]),
            None,
            None,
        );

        // Spawn the accounts to be able to modify their storage
        tx_env.spawn_accounts([&vp_owner]);
        tx_env.init_account_storage(&vp_owner, vec![public_key.clone()], 1);

        // Initialize VP environment from a transaction
        vp_host_env::init_from_tx(vp_owner.clone(), tx_env, |address| {
            // Update VP in a transaction
            tx::ctx()
                .update_validity_predicate(address, vp_hash, &None)
                .unwrap();
        });

        let pks_map = AccountPublicKeysMap::from_iter(vec![public_key]);

        let mut vp_env = vp_host_env::take();
        let mut tx = vp_env.tx.clone();
        tx.set_code(Code::new(vec![], None));
        tx.set_data(Data::new(vec![]));
        tx.add_section(Section::Signature(Signature::new(
            vec![tx.raw_header_hash()],
            pks_map.index_secret_keys(vec![keypair]),
            None,
        )));
        let signed_tx = tx.clone();
        vp_env.tx = signed_tx.clone();
        let keys_changed: BTreeSet<storage::Key> =
            vp_env.all_touched_storage_keys();
        let verifiers: BTreeSet<Address> = BTreeSet::default();
        vp_host_env::set(vp_env);
        assert!(
            validate_tx(&CTX, signed_tx, vp_owner, keys_changed, verifiers)
                .unwrap()
        );
    }
}
