//! Contracts of the `runtime-errors` cross-family scenario (W03, UQ-014; steps in `src/xfam.rs`).
//!
//! Every contract here is chunk content that reaches one of the runtime-error branches of the
//! pinned Wasmtime runner, or the preparation check that comes before it:
//!
//! * instance-layout `LoadingError`: modules whose defined globals (plus imports, tables and
//!   escaped functions) do not fit Wasmtime's 1 MiB pooling `core_instance_size`. Three module
//!   shapes are built at the largest global count that fits and at one more; the counts are
//!   nearcore's (found with the pinned harness, see `docs/evidence/lean-chunk-completion/
//!   runtime-errors/README.md`), not derived from the Lean layout model;
//! * import `LinkError`: an `env` import that no host function provides (including the names that
//!   exist only in `test_features` / `sandbox` builds and the `internal` finite-wasm hook), and
//!   known host names with a wrong signature;
//! * imports that preparation rejects first (`PrepareError::Instantiate` / `Memory`): a non-`env`
//!   module, the `internal` module, and memory / table / global imports;
//! * combinations whose order matters: an over-limit module that also has an unknown import.
//!
//! Labels and names describe what the contract contains, never what nearcore did with it.
use std::fmt::Write as _;
use std::sync::OnceLock;

/// One module shape of the instance-layout family.
#[derive(Clone, Copy, Debug)]
pub struct Shape {
    /// extra `env` host imports (beyond `storage_write`, which every shape with `writes` has)
    pub host_imports: &'static [(&'static str, &'static str)],
    /// `main` calls `storage_write` (the import is then present)
    pub writes: bool,
    /// exported functions besides `main`
    pub extra_exports: usize,
    /// a table with this many `ref.func` elements of distinct non-exported functions (0: no table)
    pub elems: usize,
}

pub const SHAPE_A: Shape = Shape { host_imports: &[], writes: true, extra_exports: 0, elems: 0 };
pub const SHAPE_B: Shape = Shape {
    host_imports: &[
        ("input", "(param i64)"),
        ("value_return", "(param i64 i64)"),
        ("log_utf8", "(param i64 i64)"),
        ("panic", ""),
    ],
    writes: true,
    extra_exports: 30,
    elems: 40,
};
pub const SHAPE_C: Shape = Shape { host_imports: &[], writes: false, extra_exports: 0, elems: 0 };

/// Largest defined-global count whose module fits the pooling allocator, per shape, as measured
/// with pinned nearcore (`near-wasm-d3-harness`, PV86). `n + 1` is the smallest that does not.
pub const FIT_A: usize = 65_501;
pub const FIT_B: usize = 65_344;
pub const FIT_C: usize = 65_505;
/// Well above every boundary.
pub const OVER: usize = 66_000;
pub const OVER2: usize = 67_000;

/// A module of `shape` with `globals` immutable i32 globals. `unknown` adds an `env` import that
/// no host provides.
pub fn shape_wat(shape: &Shape, globals: usize, unknown: Option<&str>) -> String {
    let mut w = String::from("(module\n");
    if shape.writes {
        w.push_str("  (import \"env\" \"storage_write\" (func $sw (param i64 i64 i64 i64 i64) (result i64)))\n");
    }
    for (i, (name, sig)) in shape.host_imports.iter().enumerate() {
        let _ = writeln!(w, "  (import \"env\" \"{name}\" (func $h{i} {sig}))");
    }
    if let Some(name) = unknown {
        let _ = writeln!(w, "  (import \"env\" \"{name}\" (func $unknown))");
    }
    w.push_str("  (memory 1)\n  (data (i32.const 0) \"kv\")\n");
    for i in 0..globals {
        let _ = writeln!(w, "  (global $g{i} i32 (i32.const {}))", i & 0xff);
    }
    if shape.writes {
        w.push_str("  (func (export \"main\") (drop (call $sw (i64.const 1) (i64.const 0) (i64.const 1) (i64.const 1) (i64.const 0))))\n");
    } else {
        w.push_str("  (func (export \"main\"))\n");
    }
    for i in 0..shape.extra_exports {
        let _ = writeln!(w, "  (func (export \"x{i}\"))");
    }
    if shape.elems > 0 {
        for i in 0..shape.elems {
            let _ = writeln!(w, "  (func $e{i})");
        }
        let _ = writeln!(w, "  (table {} funcref)", shape.elems);
        w.push_str("  (elem (i32.const 0) func");
        for i in 0..shape.elems {
            let _ = write!(w, " $e{i}");
        }
        w.push_str(")\n");
    }
    w.push_str(")\n");
    w
}

/// A minimal module with one import line (anything `wat` accepts inside `(import …)`) and a `main`.
pub fn import_wat(import: &str) -> String {
    format!("(module\n  {import}\n  (memory 1)\n  (func (export \"main\")))\n")
}

/// Import `LinkError` / preparation contracts: (registry name, import line).
pub const IMPORTS: &[(&str, &str)] = &[
    // no host function of this name in a production PV86 build
    ("rtunk_nosuch", r#"(import "env" "no_such_host" (func))"#),
    ("rtunk_burngas", r#"(import "env" "burn_gas" (func (param i64)))"#),
    ("rtunk_sleep", r#"(import "env" "sleep_nanos" (func (param i64)))"#),
    ("rtunk_sandbox", r#"(import "env" "sandbox_debug_log" (func (param i64 i64)))"#),
    ("rtunk_fwgas_env", r#"(import "env" "finite_wasm_gas" (func (param i64)))"#),
    ("rtunk_gas", r#"(import "env" "gas" (func (param i32)))"#),
    // known host functions with a wrong signature
    ("rtbad_storage_write", r#"(import "env" "storage_write" (func (param i64) (result i64)))"#),
    ("rtbad_value_return", r#"(import "env" "value_return" (func))"#),
    ("rtbad_input", r#"(import "env" "input" (func (param i32)))"#),
    ("rtbad_block_index", r#"(import "env" "block_index" (func (result i32)))"#),
    ("rtbad_panic", r#"(import "env" "panic" (func (param i64)))"#),
    ("rtbad_promise_create", r#"(import "env" "promise_create" (func (param i64 i64 i64 i64 i64 i64 i64) (result i64)))"#),
    ("rtbad_read_register", r#"(import "env" "read_register" (func (param i64 i64) (result i64)))"#),
    // imports that preparation rejects before any link step
    ("rtprep_module", r#"(import "foo" "input" (func (param i64)))"#),
    ("rtprep_internal", r#"(import "internal" "finite_wasm_gas" (func (param i64)))"#),
    ("rtprep_memory", r#"(import "env" "memory" (memory 1))"#),
    ("rtprep_table", r#"(import "env" "table" (table 1 funcref))"#),
    ("rtprep_global", r#"(import "env" "global" (global i64))"#),
];

fn wasm(wat: &str) -> Vec<u8> {
    wat::parse_str(wat).expect("runtime-errors wat")
}

/// Every contract of the scenario: (registry name, code). Deterministic.
pub fn contracts() -> &'static [(&'static str, Vec<u8>)] {
    static C: OnceLock<Vec<(&'static str, Vec<u8>)>> = OnceLock::new();
    C.get_or_init(|| {
        let mut v = vec![
            ("rtload", wasm(&shape_wat(&SHAPE_A, OVER, None))),
            ("rtload2", wasm(&shape_wat(&SHAPE_A, OVER2, None))),
            ("rtfita", wasm(&shape_wat(&SHAPE_A, FIT_A, None))),
            ("rtovra", wasm(&shape_wat(&SHAPE_A, FIT_A + 1, None))),
            ("rtfitb", wasm(&shape_wat(&SHAPE_B, FIT_B, None))),
            ("rtovrb", wasm(&shape_wat(&SHAPE_B, FIT_B + 1, None))),
            ("rtfitc", wasm(&shape_wat(&SHAPE_C, FIT_C, None))),
            ("rtovrc", wasm(&shape_wat(&SHAPE_C, FIT_C + 1, None))),
            // over the limit and an unknown import: loading comes before linking
            ("rtcombo", wasm(&shape_wat(&SHAPE_A, OVER, Some("no_such_host")))),
            // fits, with an unknown import: a link failure after the loading fee
            ("rtfitunk", wasm(&shape_wat(&SHAPE_A, FIT_A - 8, Some("no_such_host")))),
        ];
        for (name, import) in IMPORTS {
            v.push((name, wasm(&import_wat(import))));
        }
        v
    })
}

pub fn code(name: &str) -> &'static [u8] {
    &contracts().iter().find(|(n, _)| *n == name).unwrap_or_else(|| panic!("runtime-errors contract {name}")).1
}

/// Is `name` a contract of this scenario?
pub fn is_mine(name: &str) -> bool {
    contracts().iter().any(|(n, _)| *n == name)
}
