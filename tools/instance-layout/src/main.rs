//! Instance-layout probe (workplan item 12).
//!
//! Reads lines `<hex of a NEAR-prepared module>` on stdin and prints, per line, `fit` or
//! `over <wasmtime error>`. The engine is built with exactly the configuration of
//! `near-vm-runner/src/wasmtime_runner/mod.rs:455-545` at nearcore 2.13.4 (44f7ae6c) for the PV86
//! limits (`max_memory_pages = 2048`, `max_tables_per_contract = 1`,
//! `max_elements_per_contract_table = 10000`), including its per-architecture strategy choice
//! (Winch on x86_64, Cranelift elsewhere, `mod.rs:512-521`). Each module goes through the same path
//! as the validator: `Engine::precompile_module` (`compile_uncached`, `mod.rs:567-597`) then
//! `Module::deserialize` (`mod.rs:744-745`), which is where the pooling allocator rejects an instance
//! layout above `core_instance_size` (the `LoadingError` of UQ-014).
//!
//! Preparation (`prepare_contract`) is a pure wasm-to-wasm transform; its output bytes are produced
//! on x86_64 by the pinned harness and are the input here.
use std::io::BufRead;
use wasmtime::{
    Config, Engine, InstanceAllocationStrategy, Inlining, Module, OptLevel,
    PoolingAllocationConfig, RegallocAlgorithm, Strategy, WasmBacktraceDetails,
};

const MAX_CONCURRENCY: u32 = 1_000; // mod.rs:47
const DECOMMIT_BATCH_SIZE: usize = MAX_CONCURRENCY as usize / 2; // mod.rs:52
const GUEST_PAGE_SIZE: usize = 64 * 1024;
const MAX_MEMORY_PAGES: usize = 2048; // 85 snapshot `max_memory_pages`
const MAX_TABLES_PER_CONTRACT: u32 = 1; // `max_tables_per_contract`
const MAX_ELEMENTS_PER_CONTRACT_TABLE: usize = 10_000; // `max_elements_per_contract_table`

fn engine() -> Engine {
    // features.rs:132-137: `wasmtime::Config::default()`.
    let mut engine_config = Config::default();
    let max_memory_size = MAX_MEMORY_PAGES * GUEST_PAGE_SIZE;
    let max_tables = MAX_CONCURRENCY.saturating_mul(MAX_TABLES_PER_CONTRACT);
    let mut pooling_config = PoolingAllocationConfig::default();
    pooling_config
        .decommit_batch_size(DECOMMIT_BATCH_SIZE)
        .max_memory_size(max_memory_size)
        .table_elements(MAX_ELEMENTS_PER_CONTRACT_TABLE)
        .total_component_instances(0)
        .total_core_instances(MAX_CONCURRENCY)
        .total_memories(MAX_CONCURRENCY)
        .total_tables(max_tables)
        .max_memories_per_module(1)
        .max_tables_per_module(MAX_TABLES_PER_CONTRACT)
        .table_keep_resident(MAX_ELEMENTS_PER_CONTRACT_TABLE);
    // Deliberate-breakage control only: `PROBE_BREAK=1` raises `core_instance_size` by 64 bytes
    // above wasmtime's 1 MiB default, so a boundary search must move by exactly 4 globals.
    if std::env::var("PROBE_BREAK").as_deref() == Ok("1") {
        pooling_config.max_core_instance_size((1 << 20) + 64);
    }
    engine_config
        .allocation_strategy(InstanceAllocationStrategy::Pooling(pooling_config))
        .native_unwind_info(false)
        .wasm_backtrace_max_frames(None)
        .wasm_backtrace_details(WasmBacktraceDetails::Disable)
        .generate_address_map(false)
        .memory_init_cow(true)
        .max_wasm_stack(1024 * 1024 * 1024)
        .strategy(if cfg!(target_arch = "x86_64") { Strategy::Winch } else { Strategy::Cranelift })
        .cranelift_opt_level(OptLevel::None)
        .cranelift_regalloc_algorithm(RegallocAlgorithm::SinglePass)
        .compiler_inlining(Inlining::No)
        // Deliberate-breakage control only: `PROBE_NO_CANON=1` turns canonicalisation off.
        .cranelift_nan_canonicalization(std::env::var("PROBE_NO_CANON").as_deref() != Ok("1"))
        .signals_based_traps(true)
        .force_memory_init_memfd(true)
        .memory_guaranteed_dense_image_size(0)
        .guard_before_linear_memory(false)
        .memory_guard_size(0)
        .memory_may_move(false)
        .memory_reservation(max_memory_size.try_into().unwrap_or(u64::MAX))
        .memory_reservation_for_growth(0)
        .wasm_wide_arithmetic(true);
    Engine::new(&engine_config).expect("failed to construct Wasmtime engine")
}

/// `call` mode (UQ-003): the first stdin line is the hex of a module whose exports take and return
/// integer bit patterns; each further line is `<export> <arg>...` (decimal u64). Prints the result
/// bits per line. Used to compare float results, NaN sign and payload included, across targets.
fn call_mode(engine: &Engine) {
    use wasmtime::{Instance, Store, Val, ValType};
    let mut lines = std::io::stdin().lock().lines();
    let wasm = hex::decode(lines.next().expect("module line").expect("stdin").trim()).expect("hex");
    let module = Module::new(engine, &wasm).expect("module");
    let mut store = Store::new(engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instance");
    for line in lines {
        let line = line.expect("stdin");
        let mut parts = line.split_whitespace();
        let Some(name) = parts.next() else { continue };
        let func = instance.get_func(&mut store, name).expect("export");
        let ty = func.ty(&store);
        let args: Vec<Val> = ty
            .params()
            .zip(parts)
            .map(|(t, a)| {
                let v: u64 = a.parse().expect("arg");
                match t {
                    ValType::I32 => Val::I32(v as u32 as i32),
                    ValType::I64 => Val::I64(v as i64),
                    _ => panic!("unsupported param type"),
                }
            })
            .collect();
        let mut out = vec![Val::I32(0); ty.results().len()];
        func.call(&mut store, &args, &mut out).expect("call");
        let r = match out[0] {
            Val::I32(x) => x as u32 as u64,
            Val::I64(x) => x as u64,
            _ => panic!("unsupported result type"),
        };
        println!("{line} -> {r}");
    }
}

fn main() {
    let engine = engine();
    if std::env::args().nth(1).as_deref() == Some("call") {
        return call_mode(&engine);
    }
    eprintln!(
        "arch={} strategy={} ptr_bytes={}",
        std::env::consts::ARCH,
        if cfg!(target_arch = "x86_64") { "winch" } else { "cranelift" },
        std::mem::size_of::<usize>()
    );
    for line in std::io::stdin().lock().lines() {
        let line = line.expect("stdin");
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let prepared = hex::decode(line).expect("hex");
        let serialized = match engine.precompile_module(&prepared) {
            Ok(s) => s,
            Err(e) => {
                println!("compile-error {}", format!("{e:#}").replace('\n', " "));
                continue;
            }
        };
        // SAFETY: the bytes were produced by `precompile_module` of this very engine.
        match unsafe { Module::deserialize(&engine, &serialized) } {
            Ok(_) => println!("fit"),
            Err(e) => println!("over {}", format!("{e:#}").replace('\n', " ")),
        }
    }
}
