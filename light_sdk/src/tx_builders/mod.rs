use borsh::BorshSerialize;
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

pub mod pos;

pub(in crate::tx_builders) fn build_tx(
    data: impl BorshSerialize,
    timestamp: DateTimeUtc,
    expiration: Option<DateTimeUtc>,
    code_hash: Hash,
    code_tag: String,
    chain_id: ChainId,
) -> Tx {
    let mut inner_tx = Tx::new(chain_id, expiration);
    inner_tx.header.timestamp = timestamp;
    inner_tx.add_code_from_hash(code_hash, Some(code_tag));
    inner_tx.add_data(data);

    inner_tx
}

//FIXME: need support for hardware signatures
//FIXME: improve arguments
pub(in crate::tx_builders) fn generate_tx_signatures(
    mut tx: Tx,
    secret_keys: &[common::SecretKey],
    public_keys_index_map: &AccountPublicKeysMap,
    signer: Option<Address>,
) -> (Tx, Vec<SignatureIndex>) {
    tx.protocol_filter();
    let signatures = tx.compute_section_signature(
        secret_keys,
        public_keys_index_map,
        signer,
    );

    (tx, signatures)
}

pub(in crate::tx_builders) fn attach_raw_signatures(
    mut tx: Tx,
    signatures: Vec<SignatureIndex>,
) -> Tx {
    tx.add_signatures(signatures);
    tx
}
