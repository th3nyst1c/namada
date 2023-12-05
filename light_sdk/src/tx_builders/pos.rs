use crate::tx_builders;
use namada_core::ledger::governance::storage::proposal::ProposalType;
use namada_core::proto::Section;
use namada_core::proto::SignatureIndex;
use namada_core::proto::Signer;
use namada_core::proto::TxError;
use namada_core::proto::{Signature, Tx};
use namada_core::types::account::AccountPublicKeysMap;
use namada_core::types::address::Address;
use namada_core::types::chain::ChainId;
use namada_core::types::dec::Dec;
use namada_core::types::hash::Hash;
use namada_core::types::key::{common, secp256k1};
use namada_core::types::storage::Epoch;
use namada_core::types::time::DateTimeUtc;
use namada_core::types::token;
use namada_core::types::token::{Amount, DenominatedAmount, MaspDenom};
use namada_core::types::transaction::Fee;
use namada_core::types::transaction::GasLimit;
use std::collections::BTreeMap;
use std::str::FromStr;

// Bond WASM path
const TX_BOND_WASM: &str = "tx_bond.wasm";
// Unbond WASM path
const TX_UNBOND_WASM: &str = "tx_unbond.wasm";
// Initialize validator transaction WASM path
const TX_INIT_VALIDATOR_WASM: &str = "tx_init_validator.wasm";
// Unjail validator transaction WASM path
const TX_UNJAIL_VALIDATOR_WASM: &str = "tx_unjail_validator.wasm";
// Deactivate validator transaction WASM path
const TX_DEACTIVATE_VALIDATOR_WASM: &str = "tx_deactivate_validator.wasm";
// Reactivate validator transaction WASM path
const TX_REACTIVATE_VALIDATOR_WASM: &str = "tx_reactivate_validator.wasm";
// Claim-rewards WASM path
const TX_CLAIM_REWARDS_WASM: &str = "tx_claim_rewards.wasm";
// Redelegate transaction WASM path
const TX_REDELEGATE_WASM: &str = "tx_redelegate.wasm";
// Change validator metadata WASM path
const TX_CHANGE_METADATA_WASM: &str = "tx_change_validator_metadata.wasm";
// Change consensus key WASM path
const TX_CHANGE_CONSENSUS_KEY_WASM: &str = "tx_change_consensus_key.wasm";
// Change commission WASM path
const TX_CHANGE_COMMISSION_WASM: &str = "tx_change_validator_commission.wasm";
// Withdraw WASM path
const TX_WITHDRAW_WASM: &str = "tx_withdraw.wasm";

/// A bond transaction
pub struct Bond(Tx);

impl Bond {
    /// Build a raw Bond transaction from the given parameters
    pub fn new(
        validator: Address,
        amount: token::Amount,
        source: Option<Address>,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        let unbond = namada_core::types::transaction::pos::Bond {
            validator,
            amount,
            source,
        };

        Self(tx_builders::build_tx(
            unbond,
            timestamp,
            expiration,
            code_hash,
            TX_BOND_WASM.to_string(),
            chain_id,
        ))
    }

    //FIXME: share
    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    //FIXME: share
    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

/// An unbond transaction
pub struct Unbond(Tx);

impl Unbond {
    /// Build a raw Unbond transaction from the given parameters
    pub fn new(
        validator: Address,
        amount: token::Amount,
        source: Option<Address>,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        let unbond = namada_core::types::transaction::pos::Unbond {
            validator,
            amount,
            source,
        };

        Self(tx_builders::build_tx(
            unbond,
            timestamp,
            expiration,
            code_hash,
            TX_UNBOND_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

pub struct InitValidator(Tx);

impl InitValidator {
    /// Build a raw Init validator transaction from the given parameters
    pub fn new(
        account_keys: Vec<common::PublicKey>,
        threshold: u8,
        consensus_key: common::PublicKey,
        eth_cold_key: secp256k1::PublicKey,
        eth_hot_key: secp256k1::PublicKey,
        protocol_key: common::PublicKey,
        commission_rate: Dec,
        max_commission_rate_change: Dec,
        email: String,
        description: Option<String>,
        website: Option<String>,
        discord_handle: Option<String>,
        validator_vp_code_hash: Hash,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        let update_account =
            namada_core::types::transaction::pos::InitValidator {
                account_keys,
                threshold,
                consensus_key,
                eth_cold_key,
                eth_hot_key,
                protocol_key,
                commission_rate,
                max_commission_rate_change,
                email,
                description,
                website,
                discord_handle,
                validator_vp_code_hash,
            };

        Self(tx_builders::build_tx(
            update_account,
            timestamp,
            expiration,
            code_hash,
            TX_INIT_VALIDATOR_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

pub struct UnjailValidator(Tx);

impl UnjailValidator {
    /// Build a raw Unjail validator transaction from the given parameters
    pub fn new(
        address: Address,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        Self(tx_builders::build_tx(
            address,
            timestamp,
            expiration,
            code_hash,
            TX_UNJAIL_VALIDATOR_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

pub struct DeactivateValidator(Tx);

impl DeactivateValidator {
    /// Build a raw DeactivateValidator transaction from the given parameters
    pub fn new(
        address: Address,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        Self(tx_builders::build_tx(
            address,
            timestamp,
            expiration,
            code_hash,
            TX_DEACTIVATE_VALIDATOR_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

pub struct ReactivateValidator(Tx);

impl ReactivateValidator {
    /// Build a raw ReactivateValidator transaction from the given parameters
    pub fn new(
        address: Address,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        Self(tx_builders::build_tx(
            address,
            timestamp,
            expiration,
            code_hash,
            TX_REACTIVATE_VALIDATOR_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

pub struct ClaimRewards(Tx);

impl ClaimRewards {
    /// Build a raw ClaimRewards transaction from the given parameters
    pub fn new(
        validator: Address,
        source: Option<Address>,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        let init_proposal = namada_core::types::transaction::pos::Withdraw {
            validator,
            source,
        };

        Self(tx_builders::build_tx(
            init_proposal,
            timestamp,
            expiration,
            code_hash,
            TX_CLAIM_REWARDS_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

pub struct ChangeMetaData(Tx);

impl ChangeMetaData {
    /// Build a raw ChangeMetadata transaction from the given parameters
    pub fn new(
        validator: Address,
        email: Option<String>,
        description: Option<String>,
        website: Option<String>,
        discord_handle: Option<String>,
        commission_rate: Option<Dec>,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        let init_proposal =
            namada_core::types::transaction::pos::MetaDataChange {
                validator,
                email,
                description,
                website,
                discord_handle,
                commission_rate,
            };

        Self(tx_builders::build_tx(
            init_proposal,
            timestamp,
            expiration,
            code_hash,
            TX_CHANGE_METADATA_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

pub struct ChangeConsensusKey(Tx);

impl ChangeConsensusKey {
    /// Build a raw ChangeConsensusKey transaction from the given parameters
    pub fn new(
        validator: Address,
        consensus_key: common::PublicKey,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        let init_proposal =
            namada_core::types::transaction::pos::ConsensusKeyChange {
                validator,
                consensus_key,
            };

        Self(tx_builders::build_tx(
            init_proposal,
            timestamp,
            expiration,
            code_hash,
            TX_CHANGE_CONSENSUS_KEY_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

pub struct ChangeCommission(Tx);

impl ChangeCommission {
    /// Build a raw ChangeCommission transaction from the given parameters
    pub fn new(
        validator: Address,
        new_rate: Dec,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        let init_proposal =
            namada_core::types::transaction::pos::CommissionChange {
                validator,
                new_rate,
            };

        Self(tx_builders::build_tx(
            init_proposal,
            timestamp,
            expiration,
            code_hash,
            TX_CHANGE_COMMISSION_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}

pub struct Withdraw(Tx);

impl Withdraw {
    /// Build a raw Withdraw transaction from the given parameters
    pub fn new(
        validator: Address,
        source: Option<Address>,
        timestamp: DateTimeUtc,
        expiration: Option<DateTimeUtc>,
        code_hash: Hash,
        chain_id: ChainId,
    ) -> Self {
        let init_proposal = namada_core::types::transaction::pos::Withdraw {
            validator,
            source,
        };

        Self(tx_builders::build_tx(
            init_proposal,
            timestamp,
            expiration,
            code_hash,
            TX_WITHDRAW_WASM.to_string(),
            chain_id,
        ))
    }

    /// Generate the signature(s) for the given transaction and signers
    pub fn generate_signatures(
        mut self,
        secret_keys: &[common::SecretKey],
        public_keys_index_map: &AccountPublicKeysMap,
        signer: Option<Address>,
    ) -> (Self, Vec<SignatureIndex>) {
        let (tx, sigs) = tx_builders::generate_tx_signatures(
            self.0,
            secret_keys,
            public_keys_index_map,
            signer,
        );

        (Self(tx), sigs)
    }

    /// Attach the provided signatures to the tx
    pub fn attach_signatures(
        mut self,
        signatures: Vec<SignatureIndex>,
    ) -> Self {
        Self(tx_builders::attach_raw_signatures(self.0, signatures))
    }
}
