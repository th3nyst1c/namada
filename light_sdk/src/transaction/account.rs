use std::io::Error;
use borsh_ext::BorshSerializeExt;
use namada_core::proto::{SignatureIndex, Tx};
use namada_core::types::chain::ChainId;
use namada_core::types::hash::Hash;
use namada_core::types::key::common;
use namada_core::types::time::DateTimeUtc;

const TX_INIT_ACCOUNT_WASM: &str = "tx_init_account.wasm";
const TX_REVEAL_PK_WASM: &str = "tx_reveal_pk.wasm";
const TX_UPDATE_ACCOUNT_WASM: &str = "tx_update_account.wasm";
const VP_USER_WASM: &str = "vp_user.wasm";

pub struct InitAccount(Tx);
// the inner type shouldn't be publicly accessible

impl InitAccount {
    // FIXME:
    // * all core types must be re-exported in a coherent fashion
    // * allow the usage of other wasm strings
    // * return an error if any of the parsing fails
    // * set a default timestamp and don't expose it
    // * pubkeys is a hex encoded string
    // * return an informative error

    // NOTES:
    // * vp_code_path is the VP_USER_WASM to be used - gets turned into `vp_user.030272156a8189cc1c24a19dd3cb1f08f883e5708a9d0dc62450b11b19104e58.wasm` this hash
    // * tx_code_path is the TX_INIT_ACCOUNT_WASM to be used - gets turned into `tx_init_account.2cefb5562c184e621afe86ef852c20490cfc340bfce6c48cfe3baa74549a088b.wasm` this hash
    // * VP_USER_WASM is used as the tag and then the specific hash is used as the hash
    // * probably refactor all the tags and strings into an Enum that converts to string
    pub fn new(chain_id: &str, expiration: Option<DateTimeUtc>, public_key: &str, threshold: u8, vp_code_hash: Option<&str>, tx_code_hash: Option<&str>) -> Result<InitAccount, Error> {
        let timestamp = DateTimeUtc::now();
        let chain_id = ChainId::from_str(chain_id).unwrap();
        let pubkey = common::PublicKey::from_str(public_key).unwrap();
        let vp_hash = Hash::from(vp_code_hash.unwrap());
        let tx_hash = Hash::from(tx_code_hash.unwrap());
        let init_account = namada_core::types::transaction::account::InitAccount {
            public_keys: vec![pubkey],
            vp_code_hash: vp_hash,
            threshold,
        };

        // add vp code to tx
        // add tx code to tx
        // add tx to wrapper
        let mut inner_tx = Tx::new(chain_id, expiration);
        inner_tx.header.timestamp = timestamp.unwrap();
        inner_tx.add_code_from_hash(tx_hash, Some(TX_INIT_ACCOUNT_WASM.to_string()));
        inner_tx.add_data(init_account);
        Self(inner_tx)
    }

    // this should never fail if we have an InitAccount object
    pub fn get_sign_bytes(&self) -> Vec<u8> {
        println!("got sign bytes for initaccount");
        self.0.raw_header_hash().serialize_to_vec()
    }

    // FIXME:
    // * take a Vec<{pubkey, signature}> and attach them
    // * return an error if it doesn't work
    // * don't support multisigs in the beginning
    pub fn attach_signatures(&self, signatures: Vec<SignatureIndex>) -> InitAccount {
        println!("attached signature to initaccount and returned a new object");
        let mut tx = self.0.clone();
        tx.add_signatures(signatures);
        Self(tx)
    }
}