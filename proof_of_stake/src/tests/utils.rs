use std::env;
use std::str::FromStr;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::Relaxed;

const ENV_VAR_TEST_PAUSES: &str = "TEST_PAUSES";

pub fn pause_for_enter() {
    if paused_enabled() {
        println!("Press Enter to continue");
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).unwrap();
    }
}

fn paused_enabled() -> bool {
    // Cache the result of reading the environment variable
    static ENABLED: AtomicUsize = AtomicUsize::new(0);
    match ENABLED.load(Relaxed) {
        0 => {}
        1 => return false,
        _ => return true,
    }
    let enabled: bool = matches!(
        env::var(ENV_VAR_TEST_PAUSES).map(|val| {
            FromStr::from_str(&val).expect(&format!(
                "Expected a bool for {ENV_VAR_TEST_PAUSES} env var."
            ))
        }),
        Ok(true),
    );
    ENABLED.store(enabled as usize + 1, Relaxed);
    enabled
}
