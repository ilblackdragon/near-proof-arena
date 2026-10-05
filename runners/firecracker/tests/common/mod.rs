//! Env-gated test skips (CI convention, see .github/workflows/ci.yml). Same
//! helper as `runners/worker/tests/common/mod.rs`.

/// Report that the current test did not exercise what it gates on. Prints one
/// `ARENA-TEST-SKIPPED: <test>: <reason>` line to stderr, or panics when
/// `ARENA_REQUIRE_GATED_TESTS=1` (a CI job that claims to run the gated tests
/// must fail rather than report a skipped test as passed). The caller still
/// returns early itself; prefer the [`skip_gated!`] macro, which fills in the
/// test name.
pub fn report_gated_skip(test: &str, reason: &str) {
    let line = format!("ARENA-TEST-SKIPPED: {test}: {reason}");
    if std::env::var("ARENA_REQUIRE_GATED_TESTS").as_deref() == Ok("1") {
        panic!("{line} (ARENA_REQUIRE_GATED_TESTS=1: gated tests must run, not skip)");
    }
    eprintln!("{line}");
}

/// `skip_gated!("reason {}", x)`: [`report_gated_skip`] with the enclosing
/// function's path (e.g. `corpus::corpus`).
#[allow(unused_macros)]
macro_rules! skip_gated {
    ($($reason:tt)+) => {{
        fn __arena_here() {}
        let name = ::std::any::type_name_of_val(&__arena_here);
        let name = name.strip_suffix("::__arena_here").unwrap_or(name);
        $crate::common::report_gated_skip(name, &format!($($reason)+));
    }};
}
#[allow(unused_imports)]
pub(crate) use skip_gated;
