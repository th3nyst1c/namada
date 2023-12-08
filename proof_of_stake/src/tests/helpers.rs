use std::cmp::max;
use std::ops::Range;

use namada_core::ledger::storage::testing::TestWlStorage;
use namada_core::types::address::testing::address_from_simple_seed;
use namada_core::types::dec::Dec;
use namada_core::types::key::testing::common_sk_from_simple_seed;
use namada_core::types::key::{self, RefTo};
use namada_core::types::storage::Epoch;
use namada_core::types::token;
use namada_core::types::token::testing::arb_amount_non_zero_ceiled;
use proptest::strategy::{Just, Strategy};

use crate::parameters::testing::arb_pos_params;
use crate::types::{GenesisValidator, ValidatorSetUpdate};
use crate::validator_set_update::{
    copy_validator_sets_and_positions, validator_set_update_tendermint,
};
use crate::{
    compute_and_store_total_consensus_stake, OwnedPosParams, PosParams,
};

pub fn arb_params_and_genesis_validators(
    num_max_validator_slots: Option<u64>,
    val_size: Range<usize>,
) -> impl Strategy<Value = (OwnedPosParams, Vec<GenesisValidator>)> {
    let params = arb_pos_params(num_max_validator_slots);
    params.prop_flat_map(move |params| {
        let validators = arb_genesis_validators(
            val_size.clone(),
            Some(params.validator_stake_threshold),
        );
        (Just(params), validators)
    })
}

pub fn test_slashes_with_unbonding_params()
-> impl Strategy<Value = (OwnedPosParams, Vec<GenesisValidator>, u64)> {
    let params = arb_pos_params(Some(5));
    params.prop_flat_map(|params| {
        let unbond_delay = 0..(params.slash_processing_epoch_offset() * 2);
        // Must have at least 4 validators so we can slash one and the cubic
        // slash rate will be less than 100%
        let validators = arb_genesis_validators(4..10, None);
        (Just(params), validators, unbond_delay)
    })
}

pub fn get_tendermint_set_updates(
    s: &TestWlStorage,
    params: &PosParams,
    Epoch(epoch): Epoch,
) -> Vec<ValidatorSetUpdate> {
    // Because the `validator_set_update_tendermint` is called 2 blocks before
    // the start of a new epoch, it expects to receive the epoch that is before
    // the start of a new one too and so we give it the predecessor of the
    // current epoch here to actually get the update for the current epoch.
    let epoch = Epoch(epoch - 1);
    validator_set_update_tendermint(s, params, epoch, |update| update).unwrap()
}

/// Advance to the next epoch. Returns the new epoch.
pub fn advance_epoch(s: &mut TestWlStorage, params: &PosParams) -> Epoch {
    s.storage.block.epoch = s.storage.block.epoch.next();
    let current_epoch = s.storage.block.epoch;
    compute_and_store_total_consensus_stake(s, current_epoch).unwrap();
    copy_validator_sets_and_positions(
        s,
        params,
        current_epoch,
        current_epoch + params.pipeline_len,
    )
    .unwrap();
    // purge_validator_sets_for_old_epoch(s, current_epoch).unwrap();
    // process_slashes(s, current_epoch).unwrap();
    // dbg!(current_epoch);
    current_epoch
}

pub fn arb_genesis_validators(
    size: Range<usize>,
    threshold: Option<token::Amount>,
) -> impl Strategy<Value = Vec<GenesisValidator>> {
    let threshold = threshold
        .unwrap_or_else(|| PosParams::default().validator_stake_threshold);
    let tokens: Vec<_> = (0..size.end)
        .map(|ix| {
            if ix == 0 {
                // Make sure that at least one validator has at least a stake
                // greater or equal to the threshold to avoid having an empty
                // consensus set.
                threshold.raw_amount().as_u64()..=10_000_000_u64
            } else {
                1..=10_000_000_u64
            }
            .prop_map(token::Amount::from)
        })
        .collect();
    (size, tokens)
        .prop_map(|(size, token_amounts)| {
            // use unique seeds to generate validators' address and consensus
            // key
            let seeds = (0_u64..).take(size);
            seeds
                .zip(token_amounts)
                .map(|(seed, tokens)| {
                    let address = address_from_simple_seed(seed);
                    let consensus_sk = common_sk_from_simple_seed(seed);
                    let consensus_key = consensus_sk.to_public();

                    let protocol_sk = common_sk_from_simple_seed(seed);
                    let protocol_key = protocol_sk.to_public();

                    let eth_hot_key = key::common::PublicKey::Secp256k1(
                        key::testing::gen_keypair::<key::secp256k1::SigScheme>(
                        )
                        .ref_to(),
                    );
                    let eth_cold_key = key::common::PublicKey::Secp256k1(
                        key::testing::gen_keypair::<key::secp256k1::SigScheme>(
                        )
                        .ref_to(),
                    );

                    let commission_rate = Dec::new(5, 2).expect("Test failed");
                    let max_commission_rate_change =
                        Dec::new(1, 2).expect("Test failed");
                    GenesisValidator {
                        address,
                        tokens,
                        consensus_key,
                        protocol_key,
                        eth_hot_key,
                        eth_cold_key,
                        commission_rate,
                        max_commission_rate_change,
                        metadata: Default::default(),
                    }
                })
                .collect()
        })
        .prop_filter(
            "Must have at least one genesis validator with stake above the \
             provided threshold, if any.",
            move |gen_vals: &Vec<GenesisValidator>| {
                gen_vals.iter().any(|val| val.tokens >= threshold)
            },
        )
}

pub fn arb_redelegation_amounts(
    max_delegation: u64,
) -> impl Strategy<Value = (token::Amount, token::Amount, token::Amount)> {
    let arb_delegation = arb_amount_non_zero_ceiled(max_delegation);
    let amounts = arb_delegation.prop_flat_map(move |amount_delegate| {
        let amount_redelegate = arb_amount_non_zero_ceiled(max(
            1,
            u64::try_from(amount_delegate.raw_amount()).unwrap() - 1,
        ));
        (Just(amount_delegate), amount_redelegate)
    });
    amounts.prop_flat_map(move |(amount_delegate, amount_redelegate)| {
        let amount_unbond = arb_amount_non_zero_ceiled(max(
            1,
            u64::try_from(amount_redelegate.raw_amount()).unwrap() - 1,
        ));
        (
            Just(amount_delegate),
            Just(amount_redelegate),
            amount_unbond,
        )
    })
}
