//! Separate test binary (separate process): bwrap-dev must refuse to run
//! without `ARENA_DEV_UNSAFE=1`.

use arena_sandbox::*;

#[test]
fn refuses_without_dev_unsafe() {
    std::env::remove_var("ARENA_DEV_UNSAFE");
    let tmp = tempfile::tempdir().unwrap();
    let cfg = BwrapConfig::new(HelperCommand::new(env!("CARGO_BIN_EXE_arena-sandbox-helper")), tmp.path());
    match BwrapDev::new(cfg.clone()) {
        Err(InfraError::Refused(m)) => assert!(m.contains("ARENA_DEV_UNSAFE")),
        Err(e) => panic!("wrong error {e}"),
        Ok(_) => panic!("bwrap-dev must refuse without ARENA_DEV_UNSAFE=1"),
    }
    std::env::set_var("ARENA_DEV_UNSAFE", "yes");
    assert!(BwrapDev::new(cfg.clone()).is_err(), "only the exact value 1 enables it");
    // Constructed while enabled, then disabled: run() re-checks.
    std::env::set_var("ARENA_DEV_UNSAFE", "1");
    let sb = BwrapDev::new(cfg).unwrap();
    std::env::remove_var("ARENA_DEV_UNSAFE");
    assert!(matches!(sb.run(&SandboxSpec::new(vec!["/bin/true".into()])), Err(InfraError::Refused(_))));
}
