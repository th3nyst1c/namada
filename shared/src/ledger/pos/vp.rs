//! Proof-of-Stake native validity predicate.

use std::collections::BTreeSet;

use namada_core::ledger::storage_api::governance;
// use borsh::BorshDeserialize;
pub use namada_proof_of_stake;
pub use namada_proof_of_stake::parameters::PosParams;
// use namada_proof_of_stake::validation::validate;
use namada_proof_of_stake::storage::read_pos_params;
use namada_proof_of_stake::storage_key::is_params_key;
pub use namada_proof_of_stake::types;
use thiserror::Error;

use crate::ledger::native_vp::{self, Ctx, NativeVp};
// use crate::ledger::pos::{
//     is_validator_address_raw_hash_key,
//     is_validator_max_commission_rate_change_key,
// };
use crate::ledger::storage::{self as ledger_storage, StorageHasher};
use crate::ledger::storage_api::StorageRead;
use crate::proto::Tx;
use crate::types::address::{Address, InternalAddress};
use crate::types::storage::{Key, KeySeg};
use crate::vm::WasmCacheAccess;

#[allow(missing_docs)]
#[derive(Error, Debug)]
pub enum Error {
    #[error("Native VP error: {0}")]
    NativeVpError(native_vp::Error),
}

/// PoS functions result
pub type Result<T> = std::result::Result<T, Error>;

/// Proof-of-Stake validity predicate
pub struct PosVP<'a, DB, H, CA>
where
    DB: ledger_storage::DB + for<'iter> ledger_storage::DBIter<'iter>,
    H: StorageHasher,
    CA: WasmCacheAccess,
{
    /// Context to interact with the host structures.
    pub ctx: Ctx<'a, DB, H, CA>,
}

impl<'a, DB, H, CA> PosVP<'a, DB, H, CA>
where
    DB: 'static + ledger_storage::DB + for<'iter> ledger_storage::DBIter<'iter>,
    H: 'static + StorageHasher,
    CA: 'static + WasmCacheAccess,
{
    /// Instantiate a `PosVP`.
    pub fn new(ctx: Ctx<'a, DB, H, CA>) -> Self {
        Self { ctx }
    }
}

impl<'a, DB, H, CA> NativeVp for PosVP<'a, DB, H, CA>
where
    DB: 'static + ledger_storage::DB + for<'iter> ledger_storage::DBIter<'iter>,
    H: 'static + StorageHasher,
    CA: 'static + WasmCacheAccess,
{
    type Error = Error;

    fn validate_tx(
        &self,
        tx_data: &Tx,
        keys_changed: &BTreeSet<Key>,
        _verifiers: &BTreeSet<Address>,
    ) -> Result<bool> {
        // use validation::Data;
        // use validation::DataUpdate::{self, *};
        // use validation::ValidatorUpdate::*;

        let addr = Address::Internal(InternalAddress::PoS);
        // let mut changes: Vec<DataUpdate> = vec![];
        let _current_epoch = self.ctx.pre().get_block_epoch()?;

        tracing::debug!("\nValidating PoS Tx\n");

        for key in keys_changed {
            if is_params_key(key) {
                let data = if let Some(data) = tx_data.data() {
                    data
                } else {
                    return Ok(false);
                };
                if !governance::is_proposal_accepted(&self.ctx.pre(), &data)
                    .map_err(Error::NativeVpError)?
                {
                    return Ok(false);
                }
            } else if key.segments.get(0) == Some(&addr.to_db_key()) {
                // Unknown changes to this address space are disallowed
                // tracing::info!("PoS unrecognized key change {} rejected",
                // key);
                tracing::debug!(
                    "PoS key change {} - No action is taken currently.",
                    key
                );
                // return Ok(false);
            } else {
                tracing::debug!("PoS unrecognized key change {}", key);
                // Unknown changes anywhere else are permitted
            }
        }

        let _params = read_pos_params(&self.ctx.pre())?;
        // let errors = validate(&params, changes, current_epoch);
        // Ok(if errors.is_empty() {
        //     true
        // } else {
        //     tracing::info!(
        //         "PoS validation errors:\n - {}",
        //         errors.iter().format("\n - ")
        //     );
        //     false
        // })
        Ok(true)
    }
}

impl From<native_vp::Error> for Error {
    fn from(err: native_vp::Error) -> Self {
        Self::NativeVpError(err)
    }
}
