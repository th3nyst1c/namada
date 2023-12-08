//! PoS system tests

mod helpers;
mod state_machine;
mod state_machine_v2;
mod utils;

use std::cmp::{max, min};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::ops::{Deref, Range};
use std::str::FromStr;

use assert_matches::assert_matches;
use namada_core::ledger::storage::testing::TestWlStorage;
use namada_core::ledger::storage_api::collections::lazy_map::{
    self, Collectable, NestedMap,
};
use namada_core::ledger::storage_api::collections::LazyCollection;
use namada_core::ledger::storage_api::token::{credit_tokens, read_balance};
use namada_core::ledger::storage_api::StorageRead;
use namada_core::types::address::testing::{
    address_from_simple_seed, arb_established_address, established_address_1,
    established_address_2, established_address_3,
};
use namada_core::types::address::{Address, EstablishedAddressGen};
use namada_core::types::dec::Dec;
use namada_core::types::key::common::{PublicKey, SecretKey};
use namada_core::types::key::testing::{
    arb_common_keypair, common_sk_from_simple_seed, gen_keypair,
};
use namada_core::types::key::RefTo;
use namada_core::types::storage::{BlockHeight, Epoch, Key};
use namada_core::types::token::NATIVE_MAX_DECIMAL_PLACES;
use namada_core::types::{address, key, token};
use proptest::prelude::*;
use proptest::test_runner::Config;
// Use `RUST_LOG=info` (or another tracing level) and `--nocapture` to see
// `tracing` logs from tests
use test_log::test;

use crate::epoched::DEFAULT_NUM_PAST_EPOCHS;
use crate::helpers::{
    advance_epoch, arb_genesis_validators, arb_params_and_genesis_validators,
    arb_redelegation_amounts, test_init_genesis,
};
use crate::parameters::testing::arb_pos_params;
use crate::parameters::{OwnedPosParams, PosParams};
use crate::queries::bonds_and_unbonds;
use crate::rewards::{
    log_block_rewards, update_rewards_products_and_mint_inflation,
    PosRewardsCalculator,
};
use crate::slashing::{
    compute_bond_at_epoch, compute_slash_bond_at_epoch,
    compute_slashable_amount, process_slashes, slash, slash_redelegation,
    slash_validator, slash_validator_redelegation,
};
use crate::storage::{
    find_validator_by_raw_hash, get_consensus_key_set,
    get_num_consensus_validators,
    read_below_capacity_validator_set_addresses_with_stake,
    read_below_threshold_validator_set_addresses,
    read_consensus_validator_set_addresses_with_stake, read_total_stake,
    read_validator_deltas_value, rewards_accumulator_handle,
    total_deltas_handle,
};
use crate::test_utils::test_init_genesis;
use crate::types::{
    into_tm_voting_power, BondDetails, BondId, BondsAndUnbondsDetails,
    ConsensusValidator, EagerRedelegatedBondsMap, GenesisValidator, Position,
    RedelegatedTokens, ReverseOrdTokenAmount, Slash, SlashType, UnbondDetails,
    ValidatorSetUpdate, ValidatorState, VoteInfo, WeightedValidator,
};
use crate::validator_set_update::validator_set_update_tendermint;
use crate::{
    apply_list_slashes, become_validator, below_capacity_validator_set_handle,
    bond_handle, bond_tokens, change_consensus_key,
    compute_amount_after_slashing_unbond,
    compute_amount_after_slashing_withdraw,
    compute_and_store_total_consensus_stake, compute_modified_redelegation,
    compute_new_redelegated_unbonds, consensus_validator_set_handle,
    copy_validator_sets_and_positions, delegator_redelegated_bonds_handle,
    delegator_redelegated_unbonds_handle, find_bonds_to_remove,
    fold_and_slash_redelegated_bonds, insert_validator_into_validator_set,
    is_validator, read_validator_stake, staking_token_address,
    total_bonded_handle, total_unbonded_handle, unbond_handle, unbond_tokens,
    unjail_validator, update_validator_deltas, update_validator_set,
    validator_consensus_key_handle, validator_incoming_redelegations_handle,
    validator_outgoing_redelegations_handle, validator_set_positions_handle,
    validator_slashes_handle, validator_state_handle,
    validator_total_redelegated_bonded_handle,
    validator_total_redelegated_unbonded_handle, withdraw_tokens,
    write_pos_params, write_validator_address_raw_hash, BecomeValidator,
    EagerRedelegatedUnbonds, FoldRedelegatedBondsResult, ModifiedRedelegation,
    RedelegationError,
};

proptest! {
    // Generate arb valid input for `test_test_init_genesis_aux`
    #![proptest_config(Config {
        cases: 100,
        .. Config::default()
    })]
    #[test]
    fn test_test_init_genesis(

    (pos_params, genesis_validators) in arb_params_and_genesis_validators(Some(5), 1..10),
    start_epoch in (0_u64..1000).prop_map(Epoch),

    ) {
        test_test_init_genesis_aux(pos_params, start_epoch, genesis_validators)
    }
}

proptest! {
    // Generate arb valid input for `test_bonds_aux`
    #![proptest_config(Config {
        cases: 100,
        .. Config::default()
    })]
    #[test]
    fn test_bonds(

    (pos_params, genesis_validators) in arb_params_and_genesis_validators(Some(5), 1..3),

    ) {
        test_bonds_aux(pos_params, genesis_validators)
    }
}

proptest! {
    // Generate arb valid input for `test_slashes_with_unbonding_aux`
    #![proptest_config(Config {
        cases: 100,
        .. Config::default()
    })]
    #[test]
    fn test_slashes_with_unbonding(
        (params, genesis_validators, unbond_delay)
            in test_slashes_with_unbonding_params()
    ) {
        test_slashes_with_unbonding_aux(
            params, genesis_validators, unbond_delay)
    }
}

proptest! {
    // Generate arb valid input for `test_unjail_validator_aux`
    #![proptest_config(Config {
        cases: 100,
        .. Config::default()
    })]
    #[test]
    fn test_unjail_validator(
        (pos_params, genesis_validators)
            in arb_params_and_genesis_validators(Some(4),6..9)
    ) {
        test_unjail_validator_aux(pos_params,
            genesis_validators)
    }
}

proptest! {
    // Generate arb valid input for `test_simple_redelegation_aux`
    #![proptest_config(Config {
        cases: 100,
        .. Config::default()
    })]
    #[test]
    fn test_simple_redelegation(

    genesis_validators in arb_genesis_validators(2..4, None),
    (amount_delegate, amount_redelegate, amount_unbond) in arb_redelegation_amounts(20)

    ) {
        test_simple_redelegation_aux(genesis_validators, amount_delegate, amount_redelegate, amount_unbond)
    }
}

proptest! {
    // Generate arb valid input for `test_simple_redelegation_aux`
    #![proptest_config(Config {
        cases: 100,
        .. Config::default()
    })]
    #[test]
    fn test_redelegation_with_slashing(

    genesis_validators in arb_genesis_validators(2..4, None),
    (amount_delegate, amount_redelegate, amount_unbond) in arb_redelegation_amounts(20)

    ) {
        test_redelegation_with_slashing_aux(genesis_validators, amount_delegate, amount_redelegate, amount_unbond)
    }
}

proptest! {
    // Generate arb valid input for `test_chain_redelegations_aux`
    #![proptest_config(Config {
        cases: 100,
        .. Config::default()
    })]
    #[test]
    fn test_chain_redelegations(

    genesis_validators in arb_genesis_validators(3..4, None),

    ) {
        test_chain_redelegations_aux(genesis_validators)
    }
}

proptest! {
    // Generate arb valid input for `test_overslashing_aux`
    #![proptest_config(Config {
        cases: 1,
        .. Config::default()
    })]
    #[test]
    fn test_overslashing(

    genesis_validators in arb_genesis_validators(4..5, None),

    ) {
        test_overslashing_aux(genesis_validators)
    }
}

proptest! {
    // Generate arb valid input for `test_unslashed_bond_amount_aux`
    #![proptest_config(Config {
        cases: 1,
        .. Config::default()
    })]
    #[test]
    fn test_unslashed_bond_amount(

    genesis_validators in arb_genesis_validators(4..5, None),

    ) {
        test_unslashed_bond_amount_aux(genesis_validators)
    }
}

proptest! {
    // Generate arb valid input for `test_slashed_bond_amount_aux`
    #![proptest_config(Config {
        cases: 1,
        .. Config::default()
    })]
    #[test]
    fn test_slashed_bond_amount(

    genesis_validators in arb_genesis_validators(4..5, None),

    ) {
        test_slashed_bond_amount_aux(genesis_validators)
    }
}

proptest! {
    // Generate arb valid input for `test_log_block_rewards_aux`
    #![proptest_config(Config {
        cases: 1,
        .. Config::default()
    })]
    #[test]
    fn test_log_block_rewards(
        genesis_validators in arb_genesis_validators(4..10, None),
        params in arb_pos_params(Some(5))

    ) {
        test_log_block_rewards_aux(genesis_validators, params)
    }
}

proptest! {
    // Generate arb valid input for `test_update_rewards_products_aux`
    #![proptest_config(Config {
        cases: 1,
        .. Config::default()
    })]
    #[test]
    fn test_update_rewards_products(
        genesis_validators in arb_genesis_validators(4..10, None),

    ) {
        test_update_rewards_products_aux(genesis_validators)
    }
}

proptest! {
    // Generate arb valid input for `test_consensus_key_change`
    #![proptest_config(Config {
        cases: 1,
        .. Config::default()
    })]
    #[test]
    fn test_consensus_key_change(

    genesis_validators in arb_genesis_validators(1..2, None),

    ) {
        test_consensus_key_change_aux(genesis_validators)
    }
}

proptest! {
    // Generate arb valid input for `test_is_delegator`
    #![proptest_config(Config {
        cases: 100,
        .. Config::default()
    })]
    #[test]
    fn test_is_delegator(

    genesis_validators in arb_genesis_validators(2..3, None),

    ) {
        test_is_delegator_aux(genesis_validators)
    }
}

/// Test genesis initialization
fn test_test_init_genesis_aux(
    params: OwnedPosParams,
    start_epoch: Epoch,
    mut validators: Vec<GenesisValidator>,
) {
    println!(
        "Test inputs: {params:?}, {start_epoch}, genesis validators: \
         {validators:#?}"
    );
    let mut s = TestWlStorage::default();
    s.storage.block.epoch = start_epoch;

    validators.sort_by(|a, b| b.tokens.cmp(&a.tokens));
    let params = test_init_genesis(
        &mut s,
        params,
        validators.clone().into_iter(),
        start_epoch,
    )
    .unwrap();

    let mut bond_details = bonds_and_unbonds(&s, None, None).unwrap();
    assert!(bond_details.iter().all(|(_id, details)| {
        details.unbonds.is_empty() && details.slashes.is_empty()
    }));

    for (i, validator) in validators.into_iter().enumerate() {
        let addr = &validator.address;
        let self_bonds = bond_details
            .remove(&BondId {
                source: addr.clone(),
                validator: addr.clone(),
            })
            .unwrap();
        assert_eq!(self_bonds.bonds.len(), 1);
        assert_eq!(
            self_bonds.bonds[0],
            BondDetails {
                start: start_epoch,
                amount: validator.tokens,
                slashed_amount: None,
            }
        );

        let state = validator_state_handle(&validator.address)
            .get(&s, start_epoch, &params)
            .unwrap();
        if (i as u64) < params.max_validator_slots
            && validator.tokens >= params.validator_stake_threshold
        {
            // should be in consensus set
            let handle = consensus_validator_set_handle().at(&start_epoch);
            assert!(handle.at(&validator.tokens).iter(&s).unwrap().any(
                |result| {
                    let (_pos, addr) = result.unwrap();
                    addr == validator.address
                }
            ));
            assert_eq!(state, Some(ValidatorState::Consensus));
        } else if validator.tokens >= params.validator_stake_threshold {
            // Should be in below-capacity set if its tokens are greater than
            // `validator_stake_threshold`
            let handle = below_capacity_validator_set_handle().at(&start_epoch);
            assert!(handle.at(&validator.tokens.into()).iter(&s).unwrap().any(
                |result| {
                    let (_pos, addr) = result.unwrap();
                    addr == validator.address
                }
            ));
            assert_eq!(state, Some(ValidatorState::BelowCapacity));
        } else {
            // Should be in below-threshold
            let bt_addresses =
                read_below_threshold_validator_set_addresses(&s, start_epoch)
                    .unwrap();
            assert!(
                bt_addresses
                    .into_iter()
                    .any(|addr| { addr == validator.address })
            );
            assert_eq!(state, Some(ValidatorState::BelowThreshold));
        }
    }
}

/// Test bonding
/// NOTE: copy validator sets each time we advance the epoch
fn test_bonds_aux(params: OwnedPosParams, validators: Vec<GenesisValidator>) {
    // This can be useful for debugging:
    // params.pipeline_len = 2;
    // params.unbonding_len = 4;
    println!("\nTest inputs: {params:?}, genesis validators: {validators:#?}");
    let mut s = TestWlStorage::default();

    // Genesis
    let start_epoch = s.storage.block.epoch;
    let mut current_epoch = s.storage.block.epoch;
    let params = test_init_genesis(
        &mut s,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    s.commit_block().unwrap();

    // Advance to epoch 1
    current_epoch = advance_epoch(&mut s, &params);
    let self_bond_epoch = current_epoch;

    let validator = validators.first().unwrap();

    // Read some data before submitting bond
    let pipeline_epoch = current_epoch + params.pipeline_len;
    let staking_token = staking_token_address(&s);
    let pos_balance_pre = s
        .read::<token::Amount>(&token::balance_key(
            &staking_token,
            &super::ADDRESS,
        ))
        .unwrap()
        .unwrap_or_default();
    let total_stake_before =
        read_total_stake(&s, &params, pipeline_epoch).unwrap();

    // Self-bond
    let amount_self_bond = token::Amount::from_uint(100_500_000, 0).unwrap();
    credit_tokens(&mut s, &staking_token, &validator.address, amount_self_bond)
        .unwrap();
    bond_tokens(
        &mut s,
        None,
        &validator.address,
        amount_self_bond,
        current_epoch,
        None,
    )
    .unwrap();

    // Check the bond delta
    let self_bond = bond_handle(&validator.address, &validator.address);
    let delta = self_bond.get_delta_val(&s, pipeline_epoch).unwrap();
    assert_eq!(delta, Some(amount_self_bond));

    // Check the validator in the validator set
    let set =
        read_consensus_validator_set_addresses_with_stake(&s, pipeline_epoch)
            .unwrap();
    assert!(set.into_iter().any(
        |WeightedValidator {
             bonded_stake,
             address,
         }| {
            address == validator.address
                && bonded_stake == validator.tokens + amount_self_bond
        }
    ));

    let val_deltas =
        read_validator_deltas_value(&s, &validator.address, &pipeline_epoch)
            .unwrap();
    assert_eq!(val_deltas, Some(amount_self_bond.change()));

    let total_deltas_handle = total_deltas_handle();
    assert_eq!(
        current_epoch,
        total_deltas_handle.get_last_update(&s).unwrap().unwrap()
    );
    let total_stake_after =
        read_total_stake(&s, &params, pipeline_epoch).unwrap();
    assert_eq!(total_stake_before + amount_self_bond, total_stake_after);

    // Check bond details after self-bond
    let self_bond_id = BondId {
        source: validator.address.clone(),
        validator: validator.address.clone(),
    };
    let check_bond_details = |ix, bond_details: BondsAndUnbondsDetails| {
        println!("Check index {ix}");
        let details = bond_details.get(&self_bond_id).unwrap();
        assert_eq!(
            details.bonds.len(),
            2,
            "Contains genesis and newly added self-bond"
        );
        dbg!(&details.bonds);
        assert_eq!(
            details.bonds[0],
            BondDetails {
                start: start_epoch,
                amount: validator.tokens,
                slashed_amount: None
            },
        );
        assert_eq!(
            details.bonds[1],
            BondDetails {
                start: pipeline_epoch,
                amount: amount_self_bond,
                slashed_amount: None
            },
        );
    };
    // Try to call it with different combinations of owner/validator args
    check_bond_details(0, bonds_and_unbonds(&s, None, None).unwrap());
    check_bond_details(
        1,
        bonds_and_unbonds(&s, Some(validator.address.clone()), None).unwrap(),
    );
    check_bond_details(
        2,
        bonds_and_unbonds(&s, None, Some(validator.address.clone())).unwrap(),
    );
    check_bond_details(
        3,
        bonds_and_unbonds(
            &s,
            Some(validator.address.clone()),
            Some(validator.address.clone()),
        )
        .unwrap(),
    );

    // Get a non-validating account with tokens
    let delegator = address::testing::gen_implicit_address();
    let amount_del = token::Amount::from_uint(201_000_000, 0).unwrap();
    credit_tokens(&mut s, &staking_token, &delegator, amount_del).unwrap();
    let balance_key = token::balance_key(&staking_token, &delegator);
    let balance = s
        .read::<token::Amount>(&balance_key)
        .unwrap()
        .unwrap_or_default();
    assert_eq!(balance, amount_del);

    // Advance to epoch 3
    advance_epoch(&mut s, &params);
    current_epoch = advance_epoch(&mut s, &params);
    let pipeline_epoch = current_epoch + params.pipeline_len;

    // Delegation
    let delegation_epoch = current_epoch;
    bond_tokens(
        &mut s,
        Some(&delegator),
        &validator.address,
        amount_del,
        current_epoch,
        None,
    )
    .unwrap();
    let val_stake_pre = read_validator_stake(
        &s,
        &params,
        &validator.address,
        pipeline_epoch.prev(),
    )
    .unwrap();
    let val_stake_post =
        read_validator_stake(&s, &params, &validator.address, pipeline_epoch)
            .unwrap();
    assert_eq!(validator.tokens + amount_self_bond, val_stake_pre);
    assert_eq!(
        validator.tokens + amount_self_bond + amount_del,
        val_stake_post
    );
    let delegation = bond_handle(&delegator, &validator.address);
    assert_eq!(
        delegation
            .get_sum(&s, pipeline_epoch.prev(), &params)
            .unwrap()
            .unwrap_or_default(),
        token::Amount::zero()
    );
    assert_eq!(
        delegation
            .get_sum(&s, pipeline_epoch, &params)
            .unwrap()
            .unwrap_or_default(),
        amount_del
    );

    // Check delegation bonds details after delegation
    let delegation_bond_id = BondId {
        source: delegator.clone(),
        validator: validator.address.clone(),
    };
    let check_bond_details = |ix, bond_details: BondsAndUnbondsDetails| {
        println!("Check index {ix}");
        assert_eq!(bond_details.len(), 1);
        let details = bond_details.get(&delegation_bond_id).unwrap();
        assert_eq!(details.bonds.len(), 1,);
        dbg!(&details.bonds);
        assert_eq!(
            details.bonds[0],
            BondDetails {
                start: pipeline_epoch,
                amount: amount_del,
                slashed_amount: None
            },
        );
    };
    // Try to call it with different combinations of owner/validator args
    check_bond_details(
        0,
        bonds_and_unbonds(&s, Some(delegator.clone()), None).unwrap(),
    );
    check_bond_details(
        1,
        bonds_and_unbonds(
            &s,
            Some(delegator.clone()),
            Some(validator.address.clone()),
        )
        .unwrap(),
    );

    // Check all bond details (self-bonds and delegation)
    let check_bond_details = |ix, bond_details: BondsAndUnbondsDetails| {
        println!("Check index {ix}");
        let self_bond_details = bond_details.get(&self_bond_id).unwrap();
        let delegation_details = bond_details.get(&delegation_bond_id).unwrap();
        assert_eq!(
            self_bond_details.bonds.len(),
            2,
            "Contains genesis and newly added self-bond"
        );
        assert_eq!(
            self_bond_details.bonds[0],
            BondDetails {
                start: start_epoch,
                amount: validator.tokens,
                slashed_amount: None
            },
        );
        assert_eq!(self_bond_details.bonds[1].amount, amount_self_bond);
        assert_eq!(
            delegation_details.bonds[0],
            BondDetails {
                start: pipeline_epoch,
                amount: amount_del,
                slashed_amount: None
            },
        );
    };
    // Try to call it with different combinations of owner/validator args
    check_bond_details(0, bonds_and_unbonds(&s, None, None).unwrap());
    check_bond_details(
        1,
        bonds_and_unbonds(&s, None, Some(validator.address.clone())).unwrap(),
    );

    // Advance to epoch 5
    for _ in 0..2 {
        current_epoch = advance_epoch(&mut s, &params);
    }
    let pipeline_epoch = current_epoch + params.pipeline_len;

    // Unbond the self-bond with an amount that will remove all of the self-bond
    // executed after genesis and some of the genesis bond
    let amount_self_unbond: token::Amount =
        amount_self_bond + (validator.tokens / 2);
    // When the difference is 0, only the non-genesis self-bond is unbonded
    let unbonded_genesis_self_bond =
        amount_self_unbond - amount_self_bond != token::Amount::zero();
    dbg!(
        amount_self_unbond,
        amount_self_bond,
        unbonded_genesis_self_bond
    );
    let self_unbond_epoch = s.storage.block.epoch;

    unbond_tokens(
        &mut s,
        None,
        &validator.address,
        amount_self_unbond,
        current_epoch,
        false,
    )
    .unwrap();

    let val_stake_pre = read_validator_stake(
        &s,
        &params,
        &validator.address,
        pipeline_epoch.prev(),
    )
    .unwrap();

    let val_stake_post =
        read_validator_stake(&s, &params, &validator.address, pipeline_epoch)
            .unwrap();

    let val_delta =
        read_validator_deltas_value(&s, &validator.address, &pipeline_epoch)
            .unwrap();
    let unbond = unbond_handle(&validator.address, &validator.address);

    assert_eq!(val_delta, Some(-amount_self_unbond.change()));
    assert_eq!(
        unbond
            .at(&Epoch::default())
            .get(
                &s,
                &(pipeline_epoch
                    + params.unbonding_len
                    + params.cubic_slashing_window_length)
            )
            .unwrap(),
        if unbonded_genesis_self_bond {
            Some(amount_self_unbond - amount_self_bond)
        } else {
            None
        }
    );
    assert_eq!(
        unbond
            .at(&(self_bond_epoch + params.pipeline_len))
            .get(
                &s,
                &(pipeline_epoch
                    + params.unbonding_len
                    + params.cubic_slashing_window_length)
            )
            .unwrap(),
        Some(amount_self_bond)
    );
    assert_eq!(
        val_stake_pre,
        validator.tokens + amount_self_bond + amount_del
    );
    assert_eq!(
        val_stake_post,
        validator.tokens + amount_self_bond + amount_del - amount_self_unbond
    );

    // Check all bond and unbond details (self-bonds and delegation)
    let check_bond_details = |ix, bond_details: BondsAndUnbondsDetails| {
        println!("Check index {ix}");
        dbg!(&bond_details);
        assert_eq!(bond_details.len(), 2);
        let self_bond_details = bond_details.get(&self_bond_id).unwrap();
        let delegation_details = bond_details.get(&delegation_bond_id).unwrap();
        assert_eq!(
            self_bond_details.bonds.len(),
            1,
            "Contains only part of the genesis bond now"
        );
        assert_eq!(
            self_bond_details.bonds[0],
            BondDetails {
                start: start_epoch,
                amount: validator.tokens + amount_self_bond
                    - amount_self_unbond,
                slashed_amount: None
            },
        );
        assert_eq!(
            delegation_details.bonds[0],
            BondDetails {
                start: delegation_epoch + params.pipeline_len,
                amount: amount_del,
                slashed_amount: None
            },
        );
        assert_eq!(
            self_bond_details.unbonds.len(),
            if unbonded_genesis_self_bond { 2 } else { 1 },
            "Contains a full unbond of the last self-bond and an unbond from \
             the genesis bond"
        );
        if unbonded_genesis_self_bond {
            assert_eq!(
                self_bond_details.unbonds[0],
                UnbondDetails {
                    start: start_epoch,
                    withdraw: self_unbond_epoch
                        + params.pipeline_len
                        + params.unbonding_len
                        + params.cubic_slashing_window_length,
                    amount: amount_self_unbond - amount_self_bond,
                    slashed_amount: None
                }
            );
        }
        assert_eq!(
            self_bond_details.unbonds[usize::from(unbonded_genesis_self_bond)],
            UnbondDetails {
                start: self_bond_epoch + params.pipeline_len,
                withdraw: self_unbond_epoch
                    + params.pipeline_len
                    + params.unbonding_len
                    + params.cubic_slashing_window_length,
                amount: amount_self_bond,
                slashed_amount: None
            }
        );
    };
    check_bond_details(
        0,
        bonds_and_unbonds(&s, None, Some(validator.address.clone())).unwrap(),
    );

    // Unbond delegation
    let amount_undel = token::Amount::from_uint(1_000_000, 0).unwrap();
    unbond_tokens(
        &mut s,
        Some(&delegator),
        &validator.address,
        amount_undel,
        current_epoch,
        false,
    )
    .unwrap();

    let val_stake_pre = read_validator_stake(
        &s,
        &params,
        &validator.address,
        pipeline_epoch.prev(),
    )
    .unwrap();
    let val_stake_post =
        read_validator_stake(&s, &params, &validator.address, pipeline_epoch)
            .unwrap();
    let val_delta =
        read_validator_deltas_value(&s, &validator.address, &pipeline_epoch)
            .unwrap();
    let unbond = unbond_handle(&delegator, &validator.address);

    assert_eq!(
        val_delta,
        Some(-(amount_self_unbond + amount_undel).change())
    );
    assert_eq!(
        unbond
            .at(&(delegation_epoch + params.pipeline_len))
            .get(
                &s,
                &(pipeline_epoch
                    + params.unbonding_len
                    + params.cubic_slashing_window_length)
            )
            .unwrap(),
        Some(amount_undel)
    );
    assert_eq!(
        val_stake_pre,
        validator.tokens + amount_self_bond + amount_del
    );
    assert_eq!(
        val_stake_post,
        validator.tokens + amount_self_bond - amount_self_unbond + amount_del
            - amount_undel
    );

    let withdrawable_offset = params.unbonding_len
        + params.pipeline_len
        + params.cubic_slashing_window_length;

    // Advance to withdrawable epoch
    for _ in 0..withdrawable_offset {
        current_epoch = advance_epoch(&mut s, &params);
    }

    dbg!(current_epoch);

    let pos_balance = s
        .read::<token::Amount>(&token::balance_key(
            &staking_token,
            &super::ADDRESS,
        ))
        .unwrap();

    assert_eq!(
        Some(pos_balance_pre + amount_self_bond + amount_del),
        pos_balance
    );

    // Withdraw the self-unbond
    withdraw_tokens(&mut s, None, &validator.address, current_epoch).unwrap();
    let unbond = unbond_handle(&validator.address, &validator.address);
    let unbond_iter = unbond.iter(&s).unwrap().next();
    assert!(unbond_iter.is_none());

    let pos_balance = s
        .read::<token::Amount>(&token::balance_key(
            &staking_token,
            &super::ADDRESS,
        ))
        .unwrap();
    assert_eq!(
        Some(
            pos_balance_pre + amount_self_bond - amount_self_unbond
                + amount_del
        ),
        pos_balance
    );

    // Withdraw the delegation unbond
    withdraw_tokens(
        &mut s,
        Some(&delegator),
        &validator.address,
        current_epoch,
    )
    .unwrap();
    let unbond = unbond_handle(&delegator, &validator.address);
    let unbond_iter = unbond.iter(&s).unwrap().next();
    assert!(unbond_iter.is_none());

    let pos_balance = s
        .read::<token::Amount>(&token::balance_key(
            &staking_token,
            &super::ADDRESS,
        ))
        .unwrap();
    assert_eq!(
        Some(
            pos_balance_pre + amount_self_bond - amount_self_unbond
                + amount_del
                - amount_undel
        ),
        pos_balance
    );
}

fn test_slashes_with_unbonding_aux(
    mut params: OwnedPosParams,
    validators: Vec<GenesisValidator>,
    unbond_delay: u64,
) {
    // This can be useful for debugging:
    params.pipeline_len = 2;
    params.unbonding_len = 4;
    println!("\nTest inputs: {params:?}, genesis validators: {validators:#?}");
    let mut s = TestWlStorage::default();

    // Find the validator with the least stake to avoid the cubic slash rate
    // going to 100%
    let validator =
        itertools::Itertools::sorted_by_key(validators.iter(), |v| v.tokens)
            .next()
            .unwrap();
    let val_addr = &validator.address;
    let val_tokens = validator.tokens;
    println!(
        "Validator that will misbehave addr {val_addr}, tokens {}",
        val_tokens.to_string_native()
    );

    // Genesis
    // let start_epoch = s.storage.block.epoch;
    let mut current_epoch = s.storage.block.epoch;
    let params = test_init_genesis(
        &mut s,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    s.commit_block().unwrap();

    current_epoch = advance_epoch(&mut s, &params);
    process_slashes(&mut s, current_epoch).unwrap();

    // Discover first slash
    let slash_0_evidence_epoch = current_epoch;
    // let slash_0_processing_epoch =
    //     slash_0_evidence_epoch + params.slash_processing_epoch_offset();
    let evidence_block_height = BlockHeight(0); // doesn't matter for slashing logic
    let slash_0_type = SlashType::DuplicateVote;
    slash(
        &mut s,
        &params,
        current_epoch,
        slash_0_evidence_epoch,
        evidence_block_height,
        slash_0_type,
        val_addr,
        current_epoch.next(),
    )
    .unwrap();

    // Advance to an epoch in which we can unbond
    let unfreeze_epoch =
        slash_0_evidence_epoch + params.slash_processing_epoch_offset();
    while current_epoch < unfreeze_epoch {
        current_epoch = advance_epoch(&mut s, &params);
        process_slashes(&mut s, current_epoch).unwrap();
    }

    // Advance more epochs randomly from the generated delay
    for _ in 0..unbond_delay {
        current_epoch = advance_epoch(&mut s, &params);
    }

    // Unbond half of the tokens
    let unbond_amount = Dec::new(5, 1).unwrap() * val_tokens;
    println!("Going to unbond {}", unbond_amount.to_string_native());
    let unbond_epoch = current_epoch;
    unbond_tokens(&mut s, None, val_addr, unbond_amount, unbond_epoch, false)
        .unwrap();

    // Discover second slash
    let slash_1_evidence_epoch = current_epoch;
    // Ensure that both slashes happen before `unbond_epoch + pipeline`
    let _slash_1_processing_epoch =
        slash_1_evidence_epoch + params.slash_processing_epoch_offset();
    let evidence_block_height = BlockHeight(0); // doesn't matter for slashing logic
    let slash_1_type = SlashType::DuplicateVote;
    slash(
        &mut s,
        &params,
        current_epoch,
        slash_1_evidence_epoch,
        evidence_block_height,
        slash_1_type,
        val_addr,
        current_epoch.next(),
    )
    .unwrap();

    // Advance to an epoch in which we can withdraw
    let withdraw_epoch = unbond_epoch + params.withdrawable_epoch_offset();
    while current_epoch < withdraw_epoch {
        current_epoch = advance_epoch(&mut s, &params);
        process_slashes(&mut s, current_epoch).unwrap();
    }
    let token = staking_token_address(&s);
    let val_balance_pre = read_balance(&s, &token, val_addr).unwrap();

    let bond_id = BondId {
        source: val_addr.clone(),
        validator: val_addr.clone(),
    };
    let binding = bonds_and_unbonds(&s, None, Some(val_addr.clone())).unwrap();
    let details = binding.get(&bond_id).unwrap();
    let exp_withdraw_from_details = details.unbonds[0].amount
        - details.unbonds[0].slashed_amount.unwrap_or_default();

    withdraw_tokens(&mut s, None, val_addr, current_epoch).unwrap();

    let val_balance_post = read_balance(&s, &token, val_addr).unwrap();
    let withdrawn_tokens = val_balance_post - val_balance_pre;
    println!("Withdrew {} tokens", withdrawn_tokens.to_string_native());

    assert_eq!(exp_withdraw_from_details, withdrawn_tokens);

    let slash_rate_0 = validator_slashes_handle(val_addr)
        .get(&s, 0)
        .unwrap()
        .unwrap()
        .rate;
    let slash_rate_1 = validator_slashes_handle(val_addr)
        .get(&s, 1)
        .unwrap()
        .unwrap()
        .rate;
    println!("Slash 0 rate {slash_rate_0}, slash 1 rate {slash_rate_1}");

    let expected_withdrawn_amount = Dec::from(
        (Dec::one() - slash_rate_1)
            * (Dec::one() - slash_rate_0)
            * unbond_amount,
    );
    // Allow some rounding error, 1 NAMNAM per each slash
    let rounding_error_tolerance =
        Dec::new(2, NATIVE_MAX_DECIMAL_PLACES).unwrap();
    assert!(
        dbg!(expected_withdrawn_amount.abs_diff(&Dec::from(withdrawn_tokens)))
            <= rounding_error_tolerance
    );

    // TODO: finish once implemented
    // let slash_0 = decimal_mult_amount(slash_rate_0, val_tokens);
    // let slash_1 = decimal_mult_amount(slash_rate_1, val_tokens - slash_0);
    // let expected_slash_pool = slash_0 + slash_1;
    // let slash_pool_balance =
    //     read_balance(&s, &token, &SLASH_POOL_ADDRESS).unwrap();
    // assert_eq!(expected_slash_pool, slash_pool_balance);
}

fn test_unjail_validator_aux(
    params: OwnedPosParams,
    mut validators: Vec<GenesisValidator>,
) {
    println!("\nTest inputs: {params:?}, genesis validators: {validators:#?}");
    let mut s = TestWlStorage::default();

    // Find the validator with the most stake and 100x his stake to keep the
    // cubic slash rate small
    let num_vals = validators.len();
    validators.sort_by_key(|a| a.tokens);
    validators[num_vals - 1].tokens = 100 * validators[num_vals - 1].tokens;

    // Get second highest stake validator tomisbehave
    let val_addr = &validators[num_vals - 2].address;
    let val_tokens = validators[num_vals - 2].tokens;
    println!(
        "Validator that will misbehave addr {val_addr}, tokens {}",
        val_tokens.to_string_native()
    );

    // Genesis
    let mut current_epoch = s.storage.block.epoch;
    let params = test_init_genesis(
        &mut s,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    s.commit_block().unwrap();

    current_epoch = advance_epoch(&mut s, &params);
    process_slashes(&mut s, current_epoch).unwrap();

    // Discover first slash
    let slash_0_evidence_epoch = current_epoch;
    let evidence_block_height = BlockHeight(0); // doesn't matter for slashing logic
    let slash_0_type = SlashType::DuplicateVote;
    slash(
        &mut s,
        &params,
        current_epoch,
        slash_0_evidence_epoch,
        evidence_block_height,
        slash_0_type,
        val_addr,
        current_epoch.next(),
    )
    .unwrap();

    assert_eq!(
        validator_state_handle(val_addr)
            .get(&s, current_epoch, &params)
            .unwrap(),
        Some(ValidatorState::Consensus)
    );

    for epoch in Epoch::iter_bounds_inclusive(
        current_epoch.next(),
        current_epoch + params.pipeline_len,
    ) {
        // Check the validator state
        assert_eq!(
            validator_state_handle(val_addr)
                .get(&s, epoch, &params)
                .unwrap(),
            Some(ValidatorState::Jailed)
        );
        // Check the validator set positions
        assert!(
            validator_set_positions_handle()
                .at(&epoch)
                .get(&s, val_addr)
                .unwrap()
                .is_none(),
        );
    }

    // Advance past an epoch in which we can unbond
    let unfreeze_epoch =
        slash_0_evidence_epoch + params.slash_processing_epoch_offset();
    while current_epoch < unfreeze_epoch + 4u64 {
        current_epoch = advance_epoch(&mut s, &params);
        process_slashes(&mut s, current_epoch).unwrap();
    }

    // Unjail the validator
    unjail_validator(&mut s, val_addr, current_epoch).unwrap();

    // Check the validator state
    for epoch in
        Epoch::iter_bounds_inclusive(current_epoch, current_epoch.next())
    {
        assert_eq!(
            validator_state_handle(val_addr)
                .get(&s, epoch, &params)
                .unwrap(),
            Some(ValidatorState::Jailed)
        );
    }

    assert_eq!(
        validator_state_handle(val_addr)
            .get(&s, current_epoch + params.pipeline_len, &params)
            .unwrap(),
        Some(ValidatorState::Consensus)
    );
    assert!(
        validator_set_positions_handle()
            .at(&(current_epoch + params.pipeline_len))
            .get(&s, val_addr)
            .unwrap()
            .is_some(),
    );

    // Advance another epoch
    current_epoch = advance_epoch(&mut s, &params);
    process_slashes(&mut s, current_epoch).unwrap();

    let second_att = unjail_validator(&mut s, val_addr, current_epoch);
    assert!(second_att.is_err());
}

fn test_simple_redelegation_aux(
    mut validators: Vec<GenesisValidator>,
    amount_delegate: token::Amount,
    amount_redelegate: token::Amount,
    amount_unbond: token::Amount,
) {
    validators.sort_by(|a, b| b.tokens.cmp(&a.tokens));

    let src_validator = validators[0].address.clone();
    let dest_validator = validators[1].address.clone();

    let mut storage = TestWlStorage::default();
    let params = OwnedPosParams {
        unbonding_len: 4,
        ..Default::default()
    };

    // Genesis
    let mut current_epoch = storage.storage.block.epoch;
    let params = test_init_genesis(
        &mut storage,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    storage.commit_block().unwrap();

    // Get a delegator with some tokens
    let staking_token = staking_token_address(&storage);
    let delegator = address::testing::gen_implicit_address();
    let del_balance = token::Amount::from_uint(1_000_000, 0).unwrap();
    credit_tokens(&mut storage, &staking_token, &delegator, del_balance)
        .unwrap();

    // Ensure that we cannot redelegate with the same src and dest validator
    let err = super::redelegate_tokens(
        &mut storage,
        &delegator,
        &src_validator,
        &src_validator,
        current_epoch,
        amount_redelegate,
    )
    .unwrap_err();
    let err_str = err.to_string();
    assert_matches!(
        err.downcast::<RedelegationError>().unwrap().deref(),
        RedelegationError::RedelegationSrcEqDest,
        "Redelegation with the same src and dest validator must be rejected, \
         got {err_str}",
    );

    for _ in 0..5 {
        current_epoch = advance_epoch(&mut storage, &params);
        process_slashes(&mut storage, current_epoch).unwrap();
    }

    let init_epoch = current_epoch;

    // Delegate in epoch 1 to src_validator
    println!(
        "\nBONDING {} TOKENS TO {}\n",
        amount_delegate.to_string_native(),
        &src_validator
    );
    super::bond_tokens(
        &mut storage,
        Some(&delegator),
        &src_validator,
        amount_delegate,
        current_epoch,
        None,
    )
    .unwrap();

    println!("\nAFTER DELEGATION\n");
    let bonds = bond_handle(&delegator, &src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let bonds_dest = bond_handle(&delegator, &dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let unbonds = unbond_handle(&delegator, &src_validator)
        .collect_map(&storage)
        .unwrap();
    let tot_bonds = total_bonded_handle(&src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let tot_unbonds = total_unbonded_handle(&src_validator)
        .collect_map(&storage)
        .unwrap();
    dbg!(&bonds, &bonds_dest, &unbonds, &tot_bonds, &tot_unbonds);

    // Advance three epochs
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Redelegate in epoch 3
    println!(
        "\nREDELEGATING {} TOKENS TO {}\n",
        amount_redelegate.to_string_native(),
        &dest_validator
    );

    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &src_validator,
        &dest_validator,
        current_epoch,
        amount_redelegate,
    )
    .unwrap();

    println!("\nAFTER REDELEGATION\n");
    println!("\nDELEGATOR\n");
    let bonds_src = bond_handle(&delegator, &src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let bonds_dest = bond_handle(&delegator, &dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let unbonds_src = unbond_handle(&delegator, &src_validator)
        .collect_map(&storage)
        .unwrap();
    let unbonds_dest = unbond_handle(&delegator, &dest_validator)
        .collect_map(&storage)
        .unwrap();
    let redel_bonds = delegator_redelegated_bonds_handle(&delegator)
        .collect_map(&storage)
        .unwrap();
    let redel_unbonds = delegator_redelegated_unbonds_handle(&delegator)
        .collect_map(&storage)
        .unwrap();

    dbg!(
        &bonds_src,
        &bonds_dest,
        &unbonds_src,
        &unbonds_dest,
        &redel_bonds,
        &redel_unbonds
    );

    // Dest val
    println!("\nDEST VALIDATOR\n");

    let incoming_redels_dest =
        validator_incoming_redelegations_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let outgoing_redels_dest =
        validator_outgoing_redelegations_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_bonds_dest = total_bonded_handle(&dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let tot_unbonds_dest = total_unbonded_handle(&dest_validator)
        .collect_map(&storage)
        .unwrap();
    let tot_redel_bonds_dest =
        validator_total_redelegated_bonded_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_redel_unbonds_dest =
        validator_total_redelegated_unbonded_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    dbg!(
        &incoming_redels_dest,
        &outgoing_redels_dest,
        &tot_bonds_dest,
        &tot_unbonds_dest,
        &tot_redel_bonds_dest,
        &tot_redel_unbonds_dest
    );

    // Src val
    println!("\nSRC VALIDATOR\n");

    let incoming_redels_src =
        validator_incoming_redelegations_handle(&src_validator)
            .collect_map(&storage)
            .unwrap();
    let outgoing_redels_src =
        validator_outgoing_redelegations_handle(&src_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_bonds_src = total_bonded_handle(&src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let tot_unbonds_src = total_unbonded_handle(&src_validator)
        .collect_map(&storage)
        .unwrap();
    let tot_redel_bonds_src =
        validator_total_redelegated_bonded_handle(&src_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_redel_unbonds_src =
        validator_total_redelegated_unbonded_handle(&src_validator)
            .collect_map(&storage)
            .unwrap();
    dbg!(
        &incoming_redels_src,
        &outgoing_redels_src,
        &tot_bonds_src,
        &tot_unbonds_src,
        &tot_redel_bonds_src,
        &tot_redel_unbonds_src
    );

    // Checks
    let redelegated = delegator_redelegated_bonds_handle(&delegator)
        .at(&dest_validator)
        .at(&(current_epoch + params.pipeline_len))
        .at(&src_validator)
        .get(&storage, &(init_epoch + params.pipeline_len))
        .unwrap()
        .unwrap();
    assert_eq!(redelegated, amount_redelegate);

    let redel_start_epoch =
        validator_incoming_redelegations_handle(&dest_validator)
            .get(&storage, &delegator)
            .unwrap()
            .unwrap();
    assert_eq!(redel_start_epoch, current_epoch + params.pipeline_len);

    let redelegated = validator_outgoing_redelegations_handle(&src_validator)
        .at(&dest_validator)
        .at(&current_epoch.prev())
        .get(&storage, &current_epoch)
        .unwrap()
        .unwrap();
    assert_eq!(redelegated, amount_redelegate);

    // Advance three epochs
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Unbond in epoch 5 from dest_validator
    println!(
        "\nUNBONDING {} TOKENS FROM {}\n",
        amount_unbond.to_string_native(),
        &dest_validator
    );
    let _ = unbond_tokens(
        &mut storage,
        Some(&delegator),
        &dest_validator,
        amount_unbond,
        current_epoch,
        false,
    )
    .unwrap();

    println!("\nAFTER UNBONDING\n");
    println!("\nDELEGATOR\n");

    let bonds_src = bond_handle(&delegator, &src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let bonds_dest = bond_handle(&delegator, &dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let unbonds_src = unbond_handle(&delegator, &src_validator)
        .collect_map(&storage)
        .unwrap();
    let unbonds_dest = unbond_handle(&delegator, &dest_validator)
        .collect_map(&storage)
        .unwrap();
    let redel_bonds = delegator_redelegated_bonds_handle(&delegator)
        .collect_map(&storage)
        .unwrap();
    let redel_unbonds = delegator_redelegated_unbonds_handle(&delegator)
        .collect_map(&storage)
        .unwrap();

    dbg!(
        &bonds_src,
        &bonds_dest,
        &unbonds_src,
        &unbonds_dest,
        &redel_bonds,
        &redel_unbonds
    );

    println!("\nDEST VALIDATOR\n");

    let incoming_redels_dest =
        validator_incoming_redelegations_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let outgoing_redels_dest =
        validator_outgoing_redelegations_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_bonds_dest = total_bonded_handle(&dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let tot_unbonds_dest = total_unbonded_handle(&dest_validator)
        .collect_map(&storage)
        .unwrap();
    let tot_redel_bonds_dest =
        validator_total_redelegated_bonded_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_redel_unbonds_dest =
        validator_total_redelegated_unbonded_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    dbg!(
        &incoming_redels_dest,
        &outgoing_redels_dest,
        &tot_bonds_dest,
        &tot_unbonds_dest,
        &tot_redel_bonds_dest,
        &tot_redel_unbonds_dest
    );

    let bond_start = init_epoch + params.pipeline_len;
    let redelegation_end = bond_start + params.pipeline_len + 1u64;
    let unbond_end =
        redelegation_end + params.withdrawable_epoch_offset() + 1u64;
    let unbond_materialized = redelegation_end + params.pipeline_len + 1u64;

    // Checks
    let redelegated_remaining = delegator_redelegated_bonds_handle(&delegator)
        .at(&dest_validator)
        .at(&redelegation_end)
        .at(&src_validator)
        .get(&storage, &bond_start)
        .unwrap()
        .unwrap_or_default();
    assert_eq!(redelegated_remaining, amount_redelegate - amount_unbond);

    let redel_unbonded = delegator_redelegated_unbonds_handle(&delegator)
        .at(&dest_validator)
        .at(&redelegation_end)
        .at(&unbond_end)
        .at(&src_validator)
        .get(&storage, &bond_start)
        .unwrap()
        .unwrap();
    assert_eq!(redel_unbonded, amount_unbond);

    dbg!(unbond_materialized, redelegation_end, bond_start);
    let total_redel_unbonded =
        validator_total_redelegated_unbonded_handle(&dest_validator)
            .at(&unbond_materialized)
            .at(&redelegation_end)
            .at(&src_validator)
            .get(&storage, &bond_start)
            .unwrap()
            .unwrap();
    assert_eq!(total_redel_unbonded, amount_unbond);

    // Advance to withdrawal epoch
    loop {
        current_epoch = advance_epoch(&mut storage, &params);
        process_slashes(&mut storage, current_epoch).unwrap();
        if current_epoch == unbond_end {
            break;
        }
    }

    // Withdraw
    withdraw_tokens(
        &mut storage,
        Some(&delegator),
        &dest_validator,
        current_epoch,
    )
    .unwrap();

    assert!(
        delegator_redelegated_unbonds_handle(&delegator)
            .at(&dest_validator)
            .is_empty(&storage)
            .unwrap()
    );

    let delegator_balance = storage
        .read::<token::Amount>(&token::balance_key(&staking_token, &delegator))
        .unwrap()
        .unwrap_or_default();
    assert_eq!(
        delegator_balance,
        del_balance - amount_delegate + amount_unbond
    );
}

fn test_redelegation_with_slashing_aux(
    mut validators: Vec<GenesisValidator>,
    amount_delegate: token::Amount,
    amount_redelegate: token::Amount,
    amount_unbond: token::Amount,
) {
    validators.sort_by(|a, b| b.tokens.cmp(&a.tokens));

    let src_validator = validators[0].address.clone();
    let dest_validator = validators[1].address.clone();

    let mut storage = TestWlStorage::default();
    let params = OwnedPosParams {
        unbonding_len: 4,
        // Avoid empty consensus set by removing the threshold
        validator_stake_threshold: token::Amount::zero(),
        ..Default::default()
    };

    // Genesis
    let mut current_epoch = storage.storage.block.epoch;
    let params = test_init_genesis(
        &mut storage,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    storage.commit_block().unwrap();

    // Get a delegator with some tokens
    let staking_token = staking_token_address(&storage);
    let delegator = address::testing::gen_implicit_address();
    let del_balance = token::Amount::from_uint(1_000_000, 0).unwrap();
    credit_tokens(&mut storage, &staking_token, &delegator, del_balance)
        .unwrap();

    for _ in 0..5 {
        current_epoch = advance_epoch(&mut storage, &params);
        process_slashes(&mut storage, current_epoch).unwrap();
    }

    let init_epoch = current_epoch;

    // Delegate in epoch 5 to src_validator
    println!(
        "\nBONDING {} TOKENS TO {}\n",
        amount_delegate.to_string_native(),
        &src_validator
    );
    super::bond_tokens(
        &mut storage,
        Some(&delegator),
        &src_validator,
        amount_delegate,
        current_epoch,
        None,
    )
    .unwrap();

    println!("\nAFTER DELEGATION\n");
    let bonds = bond_handle(&delegator, &src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let bonds_dest = bond_handle(&delegator, &dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let unbonds = unbond_handle(&delegator, &src_validator)
        .collect_map(&storage)
        .unwrap();
    let tot_bonds = total_bonded_handle(&src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let tot_unbonds = total_unbonded_handle(&src_validator)
        .collect_map(&storage)
        .unwrap();
    dbg!(&bonds, &bonds_dest, &unbonds, &tot_bonds, &tot_unbonds);

    // Advance three epochs
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Redelegate in epoch 8
    println!(
        "\nREDELEGATING {} TOKENS TO {}\n",
        amount_redelegate.to_string_native(),
        &dest_validator
    );

    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &src_validator,
        &dest_validator,
        current_epoch,
        amount_redelegate,
    )
    .unwrap();

    println!("\nAFTER REDELEGATION\n");
    println!("\nDELEGATOR\n");
    let bonds_src = bond_handle(&delegator, &src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let bonds_dest = bond_handle(&delegator, &dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let unbonds_src = unbond_handle(&delegator, &src_validator)
        .collect_map(&storage)
        .unwrap();
    let unbonds_dest = unbond_handle(&delegator, &dest_validator)
        .collect_map(&storage)
        .unwrap();
    let redel_bonds = delegator_redelegated_bonds_handle(&delegator)
        .collect_map(&storage)
        .unwrap();
    let redel_unbonds = delegator_redelegated_unbonds_handle(&delegator)
        .collect_map(&storage)
        .unwrap();

    dbg!(
        &bonds_src,
        &bonds_dest,
        &unbonds_src,
        &unbonds_dest,
        &redel_bonds,
        &redel_unbonds
    );

    // Dest val
    println!("\nDEST VALIDATOR\n");

    let incoming_redels_dest =
        validator_incoming_redelegations_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let outgoing_redels_dest =
        validator_outgoing_redelegations_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_bonds_dest = total_bonded_handle(&dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let tot_unbonds_dest = total_unbonded_handle(&dest_validator)
        .collect_map(&storage)
        .unwrap();
    let tot_redel_bonds_dest =
        validator_total_redelegated_bonded_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_redel_unbonds_dest =
        validator_total_redelegated_unbonded_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    dbg!(
        &incoming_redels_dest,
        &outgoing_redels_dest,
        &tot_bonds_dest,
        &tot_unbonds_dest,
        &tot_redel_bonds_dest,
        &tot_redel_unbonds_dest
    );

    // Src val
    println!("\nSRC VALIDATOR\n");

    let incoming_redels_src =
        validator_incoming_redelegations_handle(&src_validator)
            .collect_map(&storage)
            .unwrap();
    let outgoing_redels_src =
        validator_outgoing_redelegations_handle(&src_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_bonds_src = total_bonded_handle(&src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let tot_unbonds_src = total_unbonded_handle(&src_validator)
        .collect_map(&storage)
        .unwrap();
    let tot_redel_bonds_src =
        validator_total_redelegated_bonded_handle(&src_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_redel_unbonds_src =
        validator_total_redelegated_unbonded_handle(&src_validator)
            .collect_map(&storage)
            .unwrap();
    dbg!(
        &incoming_redels_src,
        &outgoing_redels_src,
        &tot_bonds_src,
        &tot_unbonds_src,
        &tot_redel_bonds_src,
        &tot_redel_unbonds_src
    );

    // Checks
    let redelegated = delegator_redelegated_bonds_handle(&delegator)
        .at(&dest_validator)
        .at(&(current_epoch + params.pipeline_len))
        .at(&src_validator)
        .get(&storage, &(init_epoch + params.pipeline_len))
        .unwrap()
        .unwrap();
    assert_eq!(redelegated, amount_redelegate);

    let redel_start_epoch =
        validator_incoming_redelegations_handle(&dest_validator)
            .get(&storage, &delegator)
            .unwrap()
            .unwrap();
    assert_eq!(redel_start_epoch, current_epoch + params.pipeline_len);

    let redelegated = validator_outgoing_redelegations_handle(&src_validator)
        .at(&dest_validator)
        .at(&current_epoch.prev())
        .get(&storage, &current_epoch)
        .unwrap()
        .unwrap();
    assert_eq!(redelegated, amount_redelegate);

    // Advance three epochs
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Unbond in epoch 11 from dest_validator
    println!(
        "\nUNBONDING {} TOKENS FROM {}\n",
        amount_unbond.to_string_native(),
        &dest_validator
    );
    let _ = unbond_tokens(
        &mut storage,
        Some(&delegator),
        &dest_validator,
        amount_unbond,
        current_epoch,
        false,
    )
    .unwrap();

    println!("\nAFTER UNBONDING\n");
    println!("\nDELEGATOR\n");

    let bonds_src = bond_handle(&delegator, &src_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let bonds_dest = bond_handle(&delegator, &dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let unbonds_src = unbond_handle(&delegator, &src_validator)
        .collect_map(&storage)
        .unwrap();
    let unbonds_dest = unbond_handle(&delegator, &dest_validator)
        .collect_map(&storage)
        .unwrap();
    let redel_bonds = delegator_redelegated_bonds_handle(&delegator)
        .collect_map(&storage)
        .unwrap();
    let redel_unbonds = delegator_redelegated_unbonds_handle(&delegator)
        .collect_map(&storage)
        .unwrap();

    dbg!(
        &bonds_src,
        &bonds_dest,
        &unbonds_src,
        &unbonds_dest,
        &redel_bonds,
        &redel_unbonds
    );

    println!("\nDEST VALIDATOR\n");

    let incoming_redels_dest =
        validator_incoming_redelegations_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let outgoing_redels_dest =
        validator_outgoing_redelegations_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_bonds_dest = total_bonded_handle(&dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    let tot_unbonds_dest = total_unbonded_handle(&dest_validator)
        .collect_map(&storage)
        .unwrap();
    let tot_redel_bonds_dest =
        validator_total_redelegated_bonded_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    let tot_redel_unbonds_dest =
        validator_total_redelegated_unbonded_handle(&dest_validator)
            .collect_map(&storage)
            .unwrap();
    dbg!(
        &incoming_redels_dest,
        &outgoing_redels_dest,
        &tot_bonds_dest,
        &tot_unbonds_dest,
        &tot_redel_bonds_dest,
        &tot_redel_unbonds_dest
    );

    // Advance one epoch
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Discover evidence
    slash(
        &mut storage,
        &params,
        current_epoch,
        init_epoch + 2 * params.pipeline_len,
        0u64,
        SlashType::DuplicateVote,
        &src_validator,
        current_epoch.next(),
    )
    .unwrap();

    let bond_start = init_epoch + params.pipeline_len;
    let redelegation_end = bond_start + params.pipeline_len + 1u64;
    let unbond_end =
        redelegation_end + params.withdrawable_epoch_offset() + 1u64;
    let unbond_materialized = redelegation_end + params.pipeline_len + 1u64;

    // Checks
    let redelegated_remaining = delegator_redelegated_bonds_handle(&delegator)
        .at(&dest_validator)
        .at(&redelegation_end)
        .at(&src_validator)
        .get(&storage, &bond_start)
        .unwrap()
        .unwrap_or_default();
    assert_eq!(redelegated_remaining, amount_redelegate - amount_unbond);

    let redel_unbonded = delegator_redelegated_unbonds_handle(&delegator)
        .at(&dest_validator)
        .at(&redelegation_end)
        .at(&unbond_end)
        .at(&src_validator)
        .get(&storage, &bond_start)
        .unwrap()
        .unwrap();
    assert_eq!(redel_unbonded, amount_unbond);

    dbg!(unbond_materialized, redelegation_end, bond_start);
    let total_redel_unbonded =
        validator_total_redelegated_unbonded_handle(&dest_validator)
            .at(&unbond_materialized)
            .at(&redelegation_end)
            .at(&src_validator)
            .get(&storage, &bond_start)
            .unwrap()
            .unwrap();
    assert_eq!(total_redel_unbonded, amount_unbond);

    // Advance to withdrawal epoch
    loop {
        current_epoch = advance_epoch(&mut storage, &params);
        process_slashes(&mut storage, current_epoch).unwrap();
        if current_epoch == unbond_end {
            break;
        }
    }

    // Withdraw
    withdraw_tokens(
        &mut storage,
        Some(&delegator),
        &dest_validator,
        current_epoch,
    )
    .unwrap();

    assert!(
        delegator_redelegated_unbonds_handle(&delegator)
            .at(&dest_validator)
            .is_empty(&storage)
            .unwrap()
    );

    let delegator_balance = storage
        .read::<token::Amount>(&token::balance_key(&staking_token, &delegator))
        .unwrap()
        .unwrap_or_default();
    assert_eq!(delegator_balance, del_balance - amount_delegate);
}

fn test_chain_redelegations_aux(mut validators: Vec<GenesisValidator>) {
    validators.sort_by(|a, b| b.tokens.cmp(&a.tokens));

    let src_validator = validators[0].address.clone();
    let _init_stake_src = validators[0].tokens;
    let dest_validator = validators[1].address.clone();
    let _init_stake_dest = validators[1].tokens;
    let dest_validator_2 = validators[2].address.clone();
    let _init_stake_dest_2 = validators[2].tokens;

    let mut storage = TestWlStorage::default();
    let params = OwnedPosParams {
        unbonding_len: 4,
        ..Default::default()
    };

    // Genesis
    let mut current_epoch = storage.storage.block.epoch;
    let params = test_init_genesis(
        &mut storage,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    storage.commit_block().unwrap();

    // Get a delegator with some tokens
    let staking_token = staking_token_address(&storage);
    let delegator = address::testing::gen_implicit_address();
    let del_balance = token::Amount::from_uint(1_000_000, 0).unwrap();
    credit_tokens(&mut storage, &staking_token, &delegator, del_balance)
        .unwrap();

    // Delegate in epoch 0 to src_validator
    let bond_amount: token::Amount = 100.into();
    super::bond_tokens(
        &mut storage,
        Some(&delegator),
        &src_validator,
        bond_amount,
        current_epoch,
        None,
    )
    .unwrap();

    let bond_start = current_epoch + params.pipeline_len;

    // Advance one epoch
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Redelegate in epoch 1 to dest_validator
    let redel_amount_1: token::Amount = 58.into();
    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &src_validator,
        &dest_validator,
        current_epoch,
        redel_amount_1,
    )
    .unwrap();

    let redel_start = current_epoch;
    let redel_end = current_epoch + params.pipeline_len;

    // Checks ----------------

    // Dest validator should have an incoming redelegation
    let incoming_redelegation =
        validator_incoming_redelegations_handle(&dest_validator)
            .get(&storage, &delegator)
            .unwrap();
    assert_eq!(incoming_redelegation, Some(redel_end));

    // Src validator should have an outoging redelegation
    let outgoing_redelegation =
        validator_outgoing_redelegations_handle(&src_validator)
            .at(&dest_validator)
            .at(&bond_start)
            .get(&storage, &redel_start)
            .unwrap();
    assert_eq!(outgoing_redelegation, Some(redel_amount_1));

    // Delegator should have redelegated bonds
    let del_total_redelegated_bonded =
        delegator_redelegated_bonds_handle(&delegator)
            .at(&dest_validator)
            .at(&redel_end)
            .at(&src_validator)
            .get(&storage, &bond_start)
            .unwrap()
            .unwrap_or_default();
    assert_eq!(del_total_redelegated_bonded, redel_amount_1);

    // There should be delegator bonds for both src and dest validators
    let bonded_src = bond_handle(&delegator, &src_validator);
    let bonded_dest = bond_handle(&delegator, &dest_validator);
    assert_eq!(
        bonded_src
            .get_delta_val(&storage, bond_start)
            .unwrap()
            .unwrap_or_default(),
        bond_amount - redel_amount_1
    );
    assert_eq!(
        bonded_dest
            .get_delta_val(&storage, redel_end)
            .unwrap()
            .unwrap_or_default(),
        redel_amount_1
    );

    // The dest validator should have total redelegated bonded tokens
    let dest_total_redelegated_bonded =
        validator_total_redelegated_bonded_handle(&dest_validator)
            .at(&redel_end)
            .at(&src_validator)
            .get(&storage, &bond_start)
            .unwrap()
            .unwrap_or_default();
    assert_eq!(dest_total_redelegated_bonded, redel_amount_1);

    // The dest validator's total bonded should have an entry for the genesis
    // bond and the redelegation
    let dest_total_bonded = total_bonded_handle(&dest_validator)
        .get_data_handler()
        .collect_map(&storage)
        .unwrap();
    assert!(
        dest_total_bonded.len() == 2
            && dest_total_bonded.contains_key(&Epoch::default())
    );
    assert_eq!(
        dest_total_bonded
            .get(&redel_end)
            .cloned()
            .unwrap_or_default(),
        redel_amount_1
    );

    // The src validator should have a total bonded entry for the original bond
    // accounting for the redelegation
    assert_eq!(
        total_bonded_handle(&src_validator)
            .get_delta_val(&storage, bond_start)
            .unwrap()
            .unwrap_or_default(),
        bond_amount - redel_amount_1
    );

    // The src validator should have a total unbonded entry due to the
    // redelegation
    let src_total_unbonded = total_unbonded_handle(&src_validator)
        .at(&redel_end)
        .get(&storage, &bond_start)
        .unwrap()
        .unwrap_or_default();
    assert_eq!(src_total_unbonded, redel_amount_1);

    // Attempt to redelegate in epoch 3 to dest_validator
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    let redel_amount_2: token::Amount = 23.into();
    let redel_att = super::redelegate_tokens(
        &mut storage,
        &delegator,
        &dest_validator,
        &dest_validator_2,
        current_epoch,
        redel_amount_2,
    );
    assert!(redel_att.is_err());

    // Advance to right before the redelegation can be redelegated again
    assert_eq!(redel_end, current_epoch);
    let epoch_can_redel =
        redel_end.prev() + params.slash_processing_epoch_offset();
    loop {
        current_epoch = advance_epoch(&mut storage, &params);
        process_slashes(&mut storage, current_epoch).unwrap();
        if current_epoch == epoch_can_redel.prev() {
            break;
        }
    }

    // Attempt to redelegate in epoch before we actually are able to
    let redel_att = super::redelegate_tokens(
        &mut storage,
        &delegator,
        &dest_validator,
        &dest_validator_2,
        current_epoch,
        redel_amount_2,
    );
    assert!(redel_att.is_err());

    // Advance one more epoch
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Redelegate from dest_validator to dest_validator_2 now
    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &dest_validator,
        &dest_validator_2,
        current_epoch,
        redel_amount_2,
    )
    .unwrap();

    let redel_2_start = current_epoch;
    let redel_2_end = current_epoch + params.pipeline_len;

    // Checks -----------------------------------

    // Both the dest validator and dest validator 2 should have incoming
    // redelegations
    let incoming_redelegation_1 =
        validator_incoming_redelegations_handle(&dest_validator)
            .get(&storage, &delegator)
            .unwrap();
    assert_eq!(incoming_redelegation_1, Some(redel_end));
    let incoming_redelegation_2 =
        validator_incoming_redelegations_handle(&dest_validator_2)
            .get(&storage, &delegator)
            .unwrap();
    assert_eq!(incoming_redelegation_2, Some(redel_2_end));

    // Both the src validator and dest validator should have outgoing
    // redelegations
    let outgoing_redelegation_1 =
        validator_outgoing_redelegations_handle(&src_validator)
            .at(&dest_validator)
            .at(&bond_start)
            .get(&storage, &redel_start)
            .unwrap();
    assert_eq!(outgoing_redelegation_1, Some(redel_amount_1));

    let outgoing_redelegation_2 =
        validator_outgoing_redelegations_handle(&dest_validator)
            .at(&dest_validator_2)
            .at(&redel_end)
            .get(&storage, &redel_2_start)
            .unwrap();
    assert_eq!(outgoing_redelegation_2, Some(redel_amount_2));

    // All three validators should have bonds
    let bonded_dest2 = bond_handle(&delegator, &dest_validator_2);
    assert_eq!(
        bonded_src
            .get_delta_val(&storage, bond_start)
            .unwrap()
            .unwrap_or_default(),
        bond_amount - redel_amount_1
    );
    assert_eq!(
        bonded_dest
            .get_delta_val(&storage, redel_end)
            .unwrap()
            .unwrap_or_default(),
        redel_amount_1 - redel_amount_2
    );
    assert_eq!(
        bonded_dest2
            .get_delta_val(&storage, redel_2_end)
            .unwrap()
            .unwrap_or_default(),
        redel_amount_2
    );

    // There should be no unbond entries
    let unbond_src = unbond_handle(&delegator, &src_validator);
    let unbond_dest = unbond_handle(&delegator, &dest_validator);
    assert!(unbond_src.is_empty(&storage).unwrap());
    assert!(unbond_dest.is_empty(&storage).unwrap());

    // The dest validator should have some total unbonded due to the second
    // redelegation
    let dest_total_unbonded = total_unbonded_handle(&dest_validator)
        .at(&redel_2_end)
        .get(&storage, &redel_end)
        .unwrap();
    assert_eq!(dest_total_unbonded, Some(redel_amount_2));

    // Delegator should have redelegated bonds due to both redelegations
    let del_redelegated_bonds = delegator_redelegated_bonds_handle(&delegator);
    assert_eq!(
        Some(redel_amount_1 - redel_amount_2),
        del_redelegated_bonds
            .at(&dest_validator)
            .at(&redel_end)
            .at(&src_validator)
            .get(&storage, &bond_start)
            .unwrap()
    );
    assert_eq!(
        Some(redel_amount_2),
        del_redelegated_bonds
            .at(&dest_validator_2)
            .at(&redel_2_end)
            .at(&dest_validator)
            .get(&storage, &redel_end)
            .unwrap()
    );

    // Delegator redelegated unbonds should be empty
    assert!(
        delegator_redelegated_unbonds_handle(&delegator)
            .is_empty(&storage)
            .unwrap()
    );

    // Both the dest validator and dest validator 2 should have total
    // redelegated bonds
    let dest_redelegated_bonded =
        validator_total_redelegated_bonded_handle(&dest_validator)
            .at(&redel_end)
            .at(&src_validator)
            .get(&storage, &bond_start)
            .unwrap()
            .unwrap_or_default();
    let dest2_redelegated_bonded =
        validator_total_redelegated_bonded_handle(&dest_validator_2)
            .at(&redel_2_end)
            .at(&dest_validator)
            .get(&storage, &redel_end)
            .unwrap()
            .unwrap_or_default();
    assert_eq!(dest_redelegated_bonded, redel_amount_1 - redel_amount_2);
    assert_eq!(dest2_redelegated_bonded, redel_amount_2);

    // Total redelegated unbonded should be empty for src_validator and
    // dest_validator_2
    assert!(
        validator_total_redelegated_unbonded_handle(&dest_validator_2)
            .is_empty(&storage)
            .unwrap()
    );
    assert!(
        validator_total_redelegated_unbonded_handle(&src_validator)
            .is_empty(&storage)
            .unwrap()
    );

    // The dest_validator should have total_redelegated unbonded
    let tot_redel_unbonded =
        validator_total_redelegated_unbonded_handle(&dest_validator)
            .at(&redel_2_end)
            .at(&redel_end)
            .at(&src_validator)
            .get(&storage, &bond_start)
            .unwrap()
            .unwrap_or_default();
    assert_eq!(tot_redel_unbonded, redel_amount_2);
}

/// Test precisely that we are not overslashing, as originally discovered by Tomas in this issue: https://github.com/informalsystems/partnership-heliax/issues/74
fn test_overslashing_aux(mut validators: Vec<GenesisValidator>) {
    assert_eq!(validators.len(), 4);

    let params = OwnedPosParams {
        unbonding_len: 4,
        ..Default::default()
    };

    let offending_stake = token::Amount::native_whole(110);
    let other_stake = token::Amount::native_whole(100);

    // Set stakes so we know we will get a slashing rate between 0.5 -1.0
    validators[0].tokens = offending_stake;
    validators[1].tokens = other_stake;
    validators[2].tokens = other_stake;
    validators[3].tokens = other_stake;

    // Get the offending validator
    let validator = validators[0].address.clone();

    println!("\nTest inputs: {params:?}, genesis validators: {validators:#?}");
    let mut storage = TestWlStorage::default();

    // Genesis
    let mut current_epoch = storage.storage.block.epoch;
    let params = test_init_genesis(
        &mut storage,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    storage.commit_block().unwrap();

    // Get a delegator with some tokens
    let staking_token = storage.storage.native_token.clone();
    let delegator = address::testing::gen_implicit_address();
    let amount_del = token::Amount::native_whole(5);
    credit_tokens(&mut storage, &staking_token, &delegator, amount_del)
        .unwrap();

    // Delegate tokens in epoch 0 to validator
    bond_tokens(
        &mut storage,
        Some(&delegator),
        &validator,
        amount_del,
        current_epoch,
        None,
    )
    .unwrap();

    let self_bond_epoch = current_epoch;
    let delegation_epoch = current_epoch + params.pipeline_len;

    // Advance to pipeline epoch
    for _ in 0..params.pipeline_len {
        current_epoch = advance_epoch(&mut storage, &params);
    }
    assert_eq!(delegation_epoch, current_epoch);

    // Find a misbehavior committed in epoch 0
    slash(
        &mut storage,
        &params,
        current_epoch,
        self_bond_epoch,
        0_u64,
        SlashType::DuplicateVote,
        &validator,
        current_epoch.next(),
    )
    .unwrap();

    // Find a misbehavior committed in current epoch
    slash(
        &mut storage,
        &params,
        current_epoch,
        delegation_epoch,
        0_u64,
        SlashType::DuplicateVote,
        &validator,
        current_epoch.next(),
    )
    .unwrap();

    let processing_epoch_1 =
        self_bond_epoch + params.slash_processing_epoch_offset();
    let processing_epoch_2 =
        delegation_epoch + params.slash_processing_epoch_offset();

    // Advance to processing epoch 1
    loop {
        current_epoch = advance_epoch(&mut storage, &params);
        process_slashes(&mut storage, current_epoch).unwrap();
        if current_epoch == processing_epoch_1 {
            break;
        }
    }

    let total_stake_1 = offending_stake + 3 * other_stake;
    let stake_frac = Dec::from(offending_stake) / Dec::from(total_stake_1);
    let slash_rate_1 = Dec::from_str("9.0").unwrap() * stake_frac * stake_frac;
    dbg!(&slash_rate_1);

    let exp_slashed_1 = offending_stake.mul_ceil(slash_rate_1);

    // Check that the proper amount was slashed
    let epoch = current_epoch.next();
    let validator_stake =
        read_validator_stake(&storage, &params, &validator, epoch).unwrap();
    let exp_validator_stake = offending_stake - exp_slashed_1 + amount_del;
    assert_eq!(validator_stake, exp_validator_stake);

    let total_stake = read_total_stake(&storage, &params, epoch).unwrap();
    let exp_total_stake =
        offending_stake - exp_slashed_1 + amount_del + 3 * other_stake;
    assert_eq!(total_stake, exp_total_stake);

    let self_bond_id = BondId {
        source: validator.clone(),
        validator: validator.clone(),
    };
    let bond_amount =
        crate::bond_amount(&storage, &self_bond_id, epoch).unwrap();
    let exp_bond_amount = offending_stake - exp_slashed_1;
    assert_eq!(bond_amount, exp_bond_amount);

    // Advance to processing epoch 2
    loop {
        current_epoch = advance_epoch(&mut storage, &params);
        process_slashes(&mut storage, current_epoch).unwrap();
        if current_epoch == processing_epoch_2 {
            break;
        }
    }

    let total_stake_2 = offending_stake + amount_del + 3 * other_stake;
    let stake_frac =
        Dec::from(offending_stake + amount_del) / Dec::from(total_stake_2);
    let slash_rate_2 = Dec::from_str("9.0").unwrap() * stake_frac * stake_frac;
    dbg!(&slash_rate_2);

    let exp_slashed_from_delegation = amount_del.mul_ceil(slash_rate_2);

    // Check that the proper amount was slashed. We expect that all of the
    // validator self-bond has been slashed and some of the delegation has been
    // slashed due to the second infraction.
    let epoch = current_epoch.next();

    let validator_stake =
        read_validator_stake(&storage, &params, &validator, epoch).unwrap();
    let exp_validator_stake = amount_del - exp_slashed_from_delegation;
    assert_eq!(validator_stake, exp_validator_stake);

    let total_stake = read_total_stake(&storage, &params, epoch).unwrap();
    let exp_total_stake =
        amount_del - exp_slashed_from_delegation + 3 * other_stake;
    assert_eq!(total_stake, exp_total_stake);

    let delegation_id = BondId {
        source: delegator.clone(),
        validator: validator.clone(),
    };
    let delegation_amount =
        crate::bond_amount(&storage, &delegation_id, epoch).unwrap();
    let exp_del_amount = amount_del - exp_slashed_from_delegation;
    assert_eq!(delegation_amount, exp_del_amount);

    let self_bond_amount =
        crate::bond_amount(&storage, &self_bond_id, epoch).unwrap();
    let exp_bond_amount = token::Amount::zero();
    assert_eq!(self_bond_amount, exp_bond_amount);
}

fn test_unslashed_bond_amount_aux(validators: Vec<GenesisValidator>) {
    let mut storage = TestWlStorage::default();
    let params = OwnedPosParams {
        unbonding_len: 4,
        ..Default::default()
    };

    // Genesis
    let mut current_epoch = storage.storage.block.epoch;
    let params = test_init_genesis(
        &mut storage,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    storage.commit_block().unwrap();

    let validator1 = validators[0].address.clone();
    let validator2 = validators[1].address.clone();

    // Get a delegator with some tokens
    let staking_token = staking_token_address(&storage);
    let delegator = address::testing::gen_implicit_address();
    let del_balance = token::Amount::from_uint(1_000_000, 0).unwrap();
    credit_tokens(&mut storage, &staking_token, &delegator, del_balance)
        .unwrap();

    // Bond to validator 1
    super::bond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        10_000.into(),
        current_epoch,
        None,
    )
    .unwrap();

    // Unbond some from validator 1
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        1_342.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Redelegate some from validator 1 -> 2
    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &validator1,
        &validator2,
        current_epoch,
        1_875.into(),
    )
    .unwrap();

    // Unbond some from validator 2
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator2,
        584.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Advance an epoch
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Bond to validator 1
    super::bond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        384.into(),
        current_epoch,
        None,
    )
    .unwrap();

    // Unbond some from validator 1
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        144.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Redelegate some from validator 1 -> 2
    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &validator1,
        &validator2,
        current_epoch,
        3_448.into(),
    )
    .unwrap();

    // Unbond some from validator 2
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator2,
        699.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Advance an epoch
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Bond to validator 1
    super::bond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        4_384.into(),
        current_epoch,
        None,
    )
    .unwrap();

    // Redelegate some from validator 1 -> 2
    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &validator1,
        &validator2,
        current_epoch,
        1_008.into(),
    )
    .unwrap();

    // Unbond some from validator 2
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator2,
        3_500.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Checks
    let val1_init_stake = validators[0].tokens;

    for epoch in Epoch::iter_bounds_inclusive(
        Epoch(0),
        current_epoch + params.pipeline_len,
    ) {
        let bond_amount = crate::bond_amount(
            &storage,
            &BondId {
                source: delegator.clone(),
                validator: validator1.clone(),
            },
            epoch,
        )
        .unwrap_or_default();

        let val_stake =
            crate::read_validator_stake(&storage, &params, &validator1, epoch)
                .unwrap();
        // dbg!(&bond_amount);
        assert_eq!(val_stake - val1_init_stake, bond_amount);
    }
}

fn test_log_block_rewards_aux(
    validators: Vec<GenesisValidator>,
    params: OwnedPosParams,
) {
    tracing::info!(
        "New case with {} validators: {:#?}",
        validators.len(),
        validators
            .iter()
            .map(|v| (&v.address, v.tokens.to_string_native()))
            .collect::<Vec<_>>()
    );
    let mut s = TestWlStorage::default();
    // Init genesis
    let current_epoch = s.storage.block.epoch;
    let params = test_init_genesis(
        &mut s,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    s.commit_block().unwrap();
    let total_stake =
        crate::get_total_consensus_stake(&s, current_epoch, &params).unwrap();
    let consensus_set =
        crate::read_consensus_validator_set_addresses(&s, current_epoch)
            .unwrap();
    let proposer_address = consensus_set.iter().next().unwrap().clone();

    tracing::info!(
            ?params.block_proposer_reward,
            ?params.block_vote_reward,
    );
    tracing::info!(?proposer_address,);

    // Rewards accumulator should be empty at first
    let rewards_handle = rewards_accumulator_handle();
    assert!(rewards_handle.is_empty(&s).unwrap());

    let mut last_rewards = BTreeMap::default();

    let num_blocks = 100;
    // Loop through `num_blocks`, log rewards & check results
    for i in 0..num_blocks {
        tracing::info!("");
        tracing::info!("Block {}", i + 1);

        // A helper closure to prepare minimum required votes
        let prep_votes = |epoch| {
            // Ceil of 2/3 of total stake
            let min_required_votes = total_stake.mul_ceil(Dec::two() / 3);

            let mut total_votes = token::Amount::zero();
            let mut non_voters = HashSet::<Address>::default();
            let mut prep_vote = |validator| {
                // Add validator vote if it's in consensus set and if we don't
                // yet have min required votes
                if consensus_set.contains(validator)
                    && total_votes < min_required_votes
                {
                    let stake =
                        read_validator_stake(&s, &params, validator, epoch)
                            .unwrap();
                    total_votes += stake;
                    let validator_vp =
                        into_tm_voting_power(params.tm_votes_per_token, stake)
                            as u64;
                    tracing::info!("Validator {validator} signed");
                    Some(VoteInfo {
                        validator_address: validator.clone(),
                        validator_vp,
                    })
                } else {
                    non_voters.insert(validator.clone());
                    None
                }
            };

            let votes: Vec<VoteInfo> = validators
                .iter()
                .rev()
                .filter_map(|validator| prep_vote(&validator.address))
                .collect();
            (votes, total_votes, non_voters)
        };

        let (votes, signing_stake, non_voters) = prep_votes(current_epoch);
        log_block_rewards(
            &mut s,
            current_epoch,
            &proposer_address,
            votes.clone(),
        )
        .unwrap();

        assert!(!rewards_handle.is_empty(&s).unwrap());

        let rewards_calculator = PosRewardsCalculator {
            proposer_reward: params.block_proposer_reward,
            signer_reward: params.block_vote_reward,
            signing_stake,
            total_stake,
        };
        let coeffs = rewards_calculator.get_reward_coeffs().unwrap();
        tracing::info!(?coeffs);

        // Check proposer reward
        let stake =
            read_validator_stake(&s, &params, &proposer_address, current_epoch)
                .unwrap();
        let proposer_signing_reward = votes.iter().find_map(|vote| {
            if vote.validator_address == proposer_address {
                let signing_fraction =
                    Dec::from(stake) / Dec::from(signing_stake);
                Some(coeffs.signer_coeff * signing_fraction)
            } else {
                None
            }
        });
        let expected_proposer_rewards = last_rewards.get(&proposer_address).copied().unwrap_or_default() +
        // Proposer reward
        coeffs.proposer_coeff
        // Consensus validator reward
        + (coeffs.active_val_coeff
            * (Dec::from(stake) / Dec::from(total_stake)))
        // Signing reward (if proposer voted)
        + proposer_signing_reward
            .unwrap_or_default();
        tracing::info!(
            "Expected proposer rewards: {expected_proposer_rewards}. Signed \
             block: {}",
            proposer_signing_reward.is_some()
        );
        assert_eq!(
            rewards_handle.get(&s, &proposer_address).unwrap(),
            Some(expected_proposer_rewards)
        );

        // Check voters rewards
        for VoteInfo {
            validator_address, ..
        } in votes.iter()
        {
            // Skip proposer, in case voted - already checked
            if validator_address == &proposer_address {
                continue;
            }

            let stake = read_validator_stake(
                &s,
                &params,
                validator_address,
                current_epoch,
            )
            .unwrap();
            let signing_fraction = Dec::from(stake) / Dec::from(signing_stake);
            let expected_signer_rewards = last_rewards
                .get(validator_address)
                .copied()
                .unwrap_or_default()
                + coeffs.signer_coeff * signing_fraction
                + (coeffs.active_val_coeff
                    * (Dec::from(stake) / Dec::from(total_stake)));
            tracing::info!(
                "Expected signer {validator_address} rewards: \
                 {expected_signer_rewards}"
            );
            assert_eq!(
                rewards_handle.get(&s, validator_address).unwrap(),
                Some(expected_signer_rewards)
            );
        }

        // Check non-voters rewards, if any
        for address in non_voters {
            // Skip proposer, in case it didn't vote - already checked
            if address == proposer_address {
                continue;
            }

            if consensus_set.contains(&address) {
                let stake =
                    read_validator_stake(&s, &params, &address, current_epoch)
                        .unwrap();
                let expected_non_signer_rewards =
                    last_rewards.get(&address).copied().unwrap_or_default()
                        + coeffs.active_val_coeff
                            * (Dec::from(stake) / Dec::from(total_stake));
                tracing::info!(
                    "Expected non-signer {address} rewards: \
                     {expected_non_signer_rewards}"
                );
                assert_eq!(
                    rewards_handle.get(&s, &address).unwrap(),
                    Some(expected_non_signer_rewards)
                );
            } else {
                let last_reward = last_rewards.get(&address).copied();
                assert_eq!(
                    rewards_handle.get(&s, &address).unwrap(),
                    last_reward
                );
            }
        }
        s.commit_block().unwrap();

        last_rewards = rewards_accumulator_handle().collect_map(&s).unwrap();

        let rewards_sum: Dec = last_rewards.values().copied().sum();
        let expected_sum = Dec::one() * (i as u64 + 1);
        let err_tolerance = Dec::new(1, 9).unwrap();
        let fail_msg = format!(
            "Expected rewards sum at block {} to be {expected_sum}, got \
             {rewards_sum}. Error tolerance {err_tolerance}.",
            i + 1
        );
        assert!(expected_sum <= rewards_sum + err_tolerance, "{fail_msg}");
        assert!(rewards_sum <= expected_sum, "{fail_msg}");
    }
}

fn test_update_rewards_products_aux(validators: Vec<GenesisValidator>) {
    tracing::info!(
        "New case with {} validators: {:#?}",
        validators.len(),
        validators
            .iter()
            .map(|v| (&v.address, v.tokens.to_string_native()))
            .collect::<Vec<_>>()
    );
    let mut s = TestWlStorage::default();
    // Init genesis
    let current_epoch = s.storage.block.epoch;
    let params = OwnedPosParams::default();
    let params = test_init_genesis(
        &mut s,
        params,
        validators.into_iter(),
        current_epoch,
    )
    .unwrap();
    s.commit_block().unwrap();

    let staking_token = staking_token_address(&s);
    let consensus_set =
        crate::read_consensus_validator_set_addresses(&s, current_epoch)
            .unwrap();

    // Start a new epoch
    let current_epoch = advance_epoch(&mut s, &params);

    // Read some data before applying rewards
    let pos_balance_pre =
        read_balance(&s, &staking_token, &address::POS).unwrap();
    let gov_balance_pre =
        read_balance(&s, &staking_token, &address::GOV).unwrap();

    let num_consensus_validators = consensus_set.len() as u64;
    let accum_val = Dec::one() / num_consensus_validators;
    let num_blocks_in_last_epoch = 1000;

    // Assign some reward accumulator values to consensus validator
    for validator in &consensus_set {
        rewards_accumulator_handle()
            .insert(
                &mut s,
                validator.clone(),
                accum_val * num_blocks_in_last_epoch,
            )
            .unwrap();
    }

    // Distribute inflation into rewards
    let last_epoch = current_epoch.prev();
    let inflation = token::Amount::native_whole(10_000_000);
    update_rewards_products_and_mint_inflation(
        &mut s,
        &params,
        last_epoch,
        num_blocks_in_last_epoch,
        inflation,
        &staking_token,
    )
    .unwrap();

    let pos_balance_post =
        read_balance(&s, &staking_token, &address::POS).unwrap();
    let gov_balance_post =
        read_balance(&s, &staking_token, &address::GOV).unwrap();

    assert_eq!(
        pos_balance_pre + gov_balance_pre + inflation,
        pos_balance_post + gov_balance_post,
        "Expected inflation to be minted to PoS and left-over amount to Gov"
    );

    let pos_credit = pos_balance_post - pos_balance_pre;
    let gov_credit = gov_balance_post - gov_balance_pre;
    assert!(
        pos_credit > gov_credit,
        "PoS must receive more tokens than Gov, but got {} in PoS and {} in \
         Gov",
        pos_credit.to_string_native(),
        gov_credit.to_string_native()
    );

    // Rewards accumulator must be cleared out
    let rewards_handle = rewards_accumulator_handle();
    assert!(rewards_handle.is_empty(&s).unwrap());
}

fn test_slashed_bond_amount_aux(validators: Vec<GenesisValidator>) {
    let mut storage = TestWlStorage::default();
    let params = OwnedPosParams {
        unbonding_len: 4,
        ..Default::default()
    };

    let init_tot_stake = validators
        .clone()
        .into_iter()
        .fold(token::Amount::zero(), |acc, v| acc + v.tokens);
    let val1_init_stake = validators[0].tokens;

    let mut validators = validators;
    validators[0].tokens = (init_tot_stake - val1_init_stake) / 30;

    // Genesis
    let mut current_epoch = storage.storage.block.epoch;
    let params = test_init_genesis(
        &mut storage,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    storage.commit_block().unwrap();

    let validator1 = validators[0].address.clone();
    let validator2 = validators[1].address.clone();

    // Get a delegator with some tokens
    let staking_token = staking_token_address(&storage);
    let delegator = address::testing::gen_implicit_address();
    let del_balance = token::Amount::from_uint(1_000_000, 0).unwrap();
    credit_tokens(&mut storage, &staking_token, &delegator, del_balance)
        .unwrap();

    // Bond to validator 1
    super::bond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        10_000.into(),
        current_epoch,
        None,
    )
    .unwrap();

    // Unbond some from validator 1
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        1_342.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Redelegate some from validator 1 -> 2
    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &validator1,
        &validator2,
        current_epoch,
        1_875.into(),
    )
    .unwrap();

    // Unbond some from validator 2
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator2,
        584.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Advance an epoch to 1
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Bond to validator 1
    super::bond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        384.into(),
        current_epoch,
        None,
    )
    .unwrap();

    // Unbond some from validator 1
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        144.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Redelegate some from validator 1 -> 2
    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &validator1,
        &validator2,
        current_epoch,
        3_448.into(),
    )
    .unwrap();

    // Unbond some from validator 2
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator2,
        699.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Advance an epoch to ep 2
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Bond to validator 1
    super::bond_tokens(
        &mut storage,
        Some(&delegator),
        &validator1,
        4_384.into(),
        current_epoch,
        None,
    )
    .unwrap();

    // Redelegate some from validator 1 -> 2
    super::redelegate_tokens(
        &mut storage,
        &delegator,
        &validator1,
        &validator2,
        current_epoch,
        1_008.into(),
    )
    .unwrap();

    // Unbond some from validator 2
    super::unbond_tokens(
        &mut storage,
        Some(&delegator),
        &validator2,
        3_500.into(),
        current_epoch,
        false,
    )
    .unwrap();

    // Advance two epochs to ep 4
    for _ in 0..2 {
        current_epoch = advance_epoch(&mut storage, &params);
        process_slashes(&mut storage, current_epoch).unwrap();
    }

    // Find some slashes committed in various epochs
    slash(
        &mut storage,
        &params,
        current_epoch,
        Epoch(1),
        1_u64,
        SlashType::DuplicateVote,
        &validator1,
        current_epoch,
    )
    .unwrap();
    slash(
        &mut storage,
        &params,
        current_epoch,
        Epoch(2),
        1_u64,
        SlashType::DuplicateVote,
        &validator1,
        current_epoch,
    )
    .unwrap();
    slash(
        &mut storage,
        &params,
        current_epoch,
        Epoch(2),
        1_u64,
        SlashType::DuplicateVote,
        &validator1,
        current_epoch,
    )
    .unwrap();
    slash(
        &mut storage,
        &params,
        current_epoch,
        Epoch(3),
        1_u64,
        SlashType::DuplicateVote,
        &validator1,
        current_epoch,
    )
    .unwrap();

    // Advance such that these slashes are all processed
    for _ in 0..params.slash_processing_epoch_offset() {
        current_epoch = advance_epoch(&mut storage, &params);
        process_slashes(&mut storage, current_epoch).unwrap();
    }

    let pipeline_epoch = current_epoch + params.pipeline_len;

    let del_bond_amount = crate::bond_amount(
        &storage,
        &BondId {
            source: delegator.clone(),
            validator: validator1.clone(),
        },
        pipeline_epoch,
    )
    .unwrap_or_default();

    let self_bond_amount = crate::bond_amount(
        &storage,
        &BondId {
            source: validator1.clone(),
            validator: validator1.clone(),
        },
        pipeline_epoch,
    )
    .unwrap_or_default();

    let val_stake = crate::read_validator_stake(
        &storage,
        &params,
        &validator1,
        pipeline_epoch,
    )
    .unwrap();
    // dbg!(&val_stake);
    // dbg!(&del_bond_amount);
    // dbg!(&self_bond_amount);

    let diff = val_stake - self_bond_amount - del_bond_amount;
    assert!(diff <= 2.into());
}

fn test_consensus_key_change_aux(validators: Vec<GenesisValidator>) {
    assert_eq!(validators.len(), 1);

    let params = OwnedPosParams {
        unbonding_len: 4,
        ..Default::default()
    };
    let validator = validators[0].address.clone();

    println!("\nTest inputs: {params:?}, genesis validators: {validators:#?}");
    let mut storage = TestWlStorage::default();

    // Genesis
    let mut current_epoch = storage.storage.block.epoch;
    let params = test_init_genesis(
        &mut storage,
        params,
        validators.into_iter(),
        current_epoch,
    )
    .unwrap();
    storage.commit_block().unwrap();

    // Check that there is one consensus key in the network
    let consensus_keys = get_consensus_key_set(&storage).unwrap();
    assert_eq!(consensus_keys.len(), 1);
    let ck = consensus_keys.first().cloned().unwrap();
    let og_ck = validator_consensus_key_handle(&validator)
        .get(&storage, current_epoch, &params)
        .unwrap()
        .unwrap();
    assert_eq!(ck, og_ck);

    // Attempt to change to a new secp256k1 consensus key (disallowed)
    let secp_ck = gen_keypair::<key::secp256k1::SigScheme>();
    let secp_ck = key::common::SecretKey::Secp256k1(secp_ck).ref_to();
    let res =
        change_consensus_key(&mut storage, &validator, &secp_ck, current_epoch);
    assert!(res.is_err());

    // Change consensus keys
    let ck_2 = common_sk_from_simple_seed(1).ref_to();
    change_consensus_key(&mut storage, &validator, &ck_2, current_epoch)
        .unwrap();

    // Check that there is a new consensus key
    let consensus_keys = get_consensus_key_set(&storage).unwrap();
    assert_eq!(consensus_keys.len(), 2);

    for epoch in current_epoch.iter_range(params.pipeline_len) {
        let ck = validator_consensus_key_handle(&validator)
            .get(&storage, epoch, &params)
            .unwrap()
            .unwrap();
        assert_eq!(ck, og_ck);
    }
    let pipeline_epoch = current_epoch + params.pipeline_len;
    let ck = validator_consensus_key_handle(&validator)
        .get(&storage, pipeline_epoch, &params)
        .unwrap()
        .unwrap();
    assert_eq!(ck, ck_2);

    // Advance to the pipeline epoch
    loop {
        current_epoch = advance_epoch(&mut storage, &params);
        if current_epoch == pipeline_epoch {
            break;
        }
    }

    // Check the consensus keys again
    let consensus_keys = get_consensus_key_set(&storage).unwrap();
    assert_eq!(consensus_keys.len(), 2);

    for epoch in current_epoch.iter_range(params.pipeline_len + 1) {
        let ck = validator_consensus_key_handle(&validator)
            .get(&storage, epoch, &params)
            .unwrap()
            .unwrap();
        assert_eq!(ck, ck_2);
    }

    // Now change the consensus key again and bond in the same epoch
    let ck_3 = common_sk_from_simple_seed(3).ref_to();
    change_consensus_key(&mut storage, &validator, &ck_3, current_epoch)
        .unwrap();

    let staking_token = storage.storage.native_token.clone();
    let amount_del = token::Amount::native_whole(5);
    credit_tokens(&mut storage, &staking_token, &validator, amount_del)
        .unwrap();
    bond_tokens(
        &mut storage,
        None,
        &validator,
        token::Amount::native_whole(1),
        current_epoch,
        None,
    )
    .unwrap();

    // Check consensus keys again
    let consensus_keys = get_consensus_key_set(&storage).unwrap();
    assert_eq!(consensus_keys.len(), 3);

    for epoch in current_epoch.iter_range(params.pipeline_len) {
        let ck = validator_consensus_key_handle(&validator)
            .get(&storage, epoch, &params)
            .unwrap()
            .unwrap();
        assert_eq!(ck, ck_2);
    }
    let pipeline_epoch = current_epoch + params.pipeline_len;
    let ck = validator_consensus_key_handle(&validator)
        .get(&storage, pipeline_epoch, &params)
        .unwrap()
        .unwrap();
    assert_eq!(ck, ck_3);

    // Advance to the pipeline epoch to ensure that the validator set updates to
    // tendermint will work
    loop {
        current_epoch = advance_epoch(&mut storage, &params);
        if current_epoch == pipeline_epoch {
            break;
        }
    }
    assert_eq!(current_epoch.0, 2 * params.pipeline_len);
}

fn test_is_delegator_aux(mut validators: Vec<GenesisValidator>) {
    validators.sort_by(|a, b| b.tokens.cmp(&a.tokens));

    let validator1 = validators[0].address.clone();
    let validator2 = validators[1].address.clone();

    let mut storage = TestWlStorage::default();
    let params = OwnedPosParams {
        unbonding_len: 4,
        ..Default::default()
    };

    // Genesis
    let mut current_epoch = storage.storage.block.epoch;
    let params = test_init_genesis(
        &mut storage,
        params,
        validators.clone().into_iter(),
        current_epoch,
    )
    .unwrap();
    storage.commit_block().unwrap();

    // Get delegators with some tokens
    let staking_token = staking_token_address(&storage);
    let delegator1 = address::testing::gen_implicit_address();
    let delegator2 = address::testing::gen_implicit_address();
    let del_balance = token::Amount::native_whole(1000);
    credit_tokens(&mut storage, &staking_token, &delegator1, del_balance)
        .unwrap();
    credit_tokens(&mut storage, &staking_token, &delegator2, del_balance)
        .unwrap();

    // Advance to epoch 1
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Delegate in epoch 1 to validator1
    let del1_epoch = current_epoch;
    super::bond_tokens(
        &mut storage,
        Some(&delegator1),
        &validator1,
        1000.into(),
        current_epoch,
        None,
    )
    .unwrap();

    // Advance to epoch 2
    current_epoch = advance_epoch(&mut storage, &params);
    process_slashes(&mut storage, current_epoch).unwrap();

    // Delegate in epoch 2 to validator2
    let del2_epoch = current_epoch;
    super::bond_tokens(
        &mut storage,
        Some(&delegator2),
        &validator2,
        1000.into(),
        current_epoch,
        None,
    )
    .unwrap();

    // Checks
    assert!(super::is_validator(&storage, &validator1).unwrap());
    assert!(super::is_validator(&storage, &validator2).unwrap());
    assert!(!super::is_delegator(&storage, &validator1, None).unwrap());
    assert!(!super::is_delegator(&storage, &validator2, None).unwrap());

    assert!(!super::is_validator(&storage, &delegator1).unwrap());
    assert!(!super::is_validator(&storage, &delegator2).unwrap());
    assert!(super::is_delegator(&storage, &delegator1, None).unwrap());
    assert!(super::is_delegator(&storage, &delegator2, None).unwrap());

    for epoch in Epoch::default().iter_range(del1_epoch.0 + params.pipeline_len)
    {
        assert!(
            !super::is_delegator(&storage, &delegator1, Some(epoch)).unwrap()
        );
    }
    assert!(
        super::is_delegator(
            &storage,
            &delegator1,
            Some(del1_epoch + params.pipeline_len)
        )
        .unwrap()
    );
    for epoch in Epoch::default().iter_range(del2_epoch.0 + params.pipeline_len)
    {
        assert!(
            !super::is_delegator(&storage, &delegator2, Some(epoch)).unwrap()
        );
    }
    assert!(
        super::is_delegator(
            &storage,
            &delegator2,
            Some(del2_epoch + params.pipeline_len)
        )
        .unwrap()
    );
}
