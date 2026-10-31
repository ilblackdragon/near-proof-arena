//! Phase 4 fold driver: prove k near-chunk instances, then fold their
//! verification into ONE recursion-guest proof via the examples/recursion
//! pattern. Measures: inner prove times, serialization sizes, in-guest
//! verify cost (via trace), and the aggregate recursion proof time/size.
//!
//! Runs in STEPS because the host environment kills long processes:
//!   FOLD_STEP=1 k  — inner proofs -> state file fold-input-k<k>.bin (records)
//!   FOLD_STEP=2 k  — trace the recursion guest on the state file (rows/time/all_valid)
//!   FOLD_STEP=3 k  — fold preprocess+prove+verify (reads rows from the step-2 state)
//!
//! PCS statement (measured from source, jolt-sdk host_utils.rs): the SDK
//! prove path and the recursion guest's VerifierPCS are DoryScheme —
//! NON-PQ. The only PQ zkVM numbers in this lane remain JOLT_SCREEN's
//! sha2-chain scales 18/20. This fold result is explicitly non-PQ.
use jolt_sdk::host::Program;
use jolt_sdk::{
    JoltDevice, JoltProverPreprocessing, JoltVerifierPreprocessing, MemoryConfig,
    ProgramPreprocessingMode, RV64IMACProof,
};
use serde::Serialize;
use std::time::Instant;
use tracing::info;

fn push_record<T: Serialize>(buffer: &mut Vec<u8>, value: &T) {
    let bytes = bincode::serde::encode_to_vec(value, bincode::config::standard()).unwrap();
    buffer.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    buffer.extend_from_slice(&bytes);
}

const INNER_MEMORY: MemoryConfig = MemoryConfig {
    max_input_size: 4096,
    max_output_size: 4096,
    max_untrusted_advice_size: 4096,
    max_trusted_advice_size: 4096,
    heap_size: 33554432,
    stack_size: 65536,
    program_size: None,
};

fn rec_memory() -> MemoryConfig {
    MemoryConfig {
        max_input_size: 134217728,
        max_output_size: 4096,
        max_untrusted_advice_size: 0,
        max_trusted_advice_size: 0,
        heap_size: 134217728,
        stack_size: 33554432,
        program_size: None,
    }
}

fn write_recursion_macro(memory: &MemoryConfig) {
    // OWN the macro file: the stock recursion example rewrites it on its
    // own runs, so regenerate it here (identical discipline). The guest
    // macro must match the host config exactly or the emulator MMU fails.
    let macro_content = format!(
        r#"macro_rules! provable_with_config {{
    ($item: item) => {{
        #[jolt::provable(
            max_input_size = {},
            max_output_size = {},
            max_untrusted_advice_size = {},
            max_trusted_advice_size = {},
            heap_size = {},
            stack_size = {},
            max_trace_length = {}
        )]
        $item
    }};
}}"#,
        memory.max_input_size,
        memory.max_output_size,
        memory.max_untrusted_advice_size,
        memory.max_trusted_advice_size,
        memory.heap_size,
        memory.stack_size,
        4000000000u64
    );
    let p = std::path::Path::new(
        "/data/illia/pq-tail-architecture-20261024/jolt/examples/recursion/guest/src/provable_macro.rs",
    );
    std::fs::write(p, macro_content).unwrap();
    info!("regenerated recursion guest provable_macro.rs from rec_memory");
}

fn build_recursion_program(memory: &MemoryConfig) -> Program {
    write_recursion_macro(memory);
    let mut program = Program::new("recursion-guest");
    program.set_func("verify");
    program.set_std(true);
    program.set_memory_config(*memory);
    program.build("/tmp/jolt-guest-targets");
    info!("recursion guest built");
    program
}

fn main() {
    tracing_subscriber::fmt::init();
    let target_dir = "/tmp/jolt-guest-targets";
    let step = std::env::var("FOLD_STEP").unwrap_or_else(|_| "all".to_string());
    let state_dir = "/tmp/opencode/fold-state";
    std::fs::create_dir_all(state_dir).unwrap();

    // The near-chunk guest is deterministic (embedded fixtures, no inputs),
    // so k distinct proofs come from re-proving the same program; the
    // recursion guest then verifies k (identical-statement) proofs. That is
    // the honest k=2/k=4 aggregation cost shape for identical chunks; a
    // mixed-chunk fold needs distinct fixtures and is deferred.
    let k: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(2);
    info!("fold k={k} step={step}");
    let input_path = format!("{state_dir}/fold-input-k{k}.bin");
    let framed_path = format!("{state_dir}/fold-framed-k{k}.bin");
    let rows_path = format!("{state_dir}/fold-rows-k{k}.txt");

    if step == "1" || step == "all" {
        // ---- Step 1: inner proofs -> fold input state ----
        let mut inner_program = guest::compile_near_chunk(target_dir);
        info!("inner program built");
        let inner_prover_preprocessing: JoltProverPreprocessing =
            guest::preprocess_prover_near_chunk(
                guest::preprocess_shared_near_chunk(&mut inner_program)
                    .expect("shared preprocessing"),
            );
        let prove_inner =
            guest::build_prover_near_chunk(inner_program, inner_prover_preprocessing.clone());
        let inner_verifier_preprocessing: JoltVerifierPreprocessing =
            jolt_sdk::verifier_preprocessing_from_prover(&inner_prover_preprocessing);
        info!("inner preprocessing done");

        let mut all_data = Vec::new();
        push_record(&mut all_data, &inner_verifier_preprocessing);
        push_record(&mut all_data, &(k as u32));

        let mut inner_prove_times = Vec::new();
        for i in 0..k {
            let now = Instant::now();
            let (_output, proof, io_device) = prove_inner();
            let t = now.elapsed().as_secs_f64();
            inner_prove_times.push(t);
            info!("inner proof {i}: {t:.3} s");
            push_record(&mut all_data, &proof);
            push_record(&mut all_data, &io_device);
            let ok = jolt_sdk::jolt_verifier::verify::<
                jolt_sdk::VerifierField,
                jolt_sdk::VerifierPCS,
                jolt_sdk::VerifierVC,
                jolt_sdk::VerifierTranscript,
            >(&inner_verifier_preprocessing, &io_device, &proof, None)
            .is_ok();
            assert!(ok, "inner proof {i} failed outer verification");
        }
        info!(
            "FOLD_STEP1 k={k} inner_prove_s={inner_prove_times:?} fold_input_bytes={}",
            all_data.len()
        );
        std::fs::write(&input_path, &all_data).unwrap();
        let framed = postcard::to_stdvec(&all_data.as_slice()).unwrap();
        std::fs::write(&framed_path, &framed).unwrap();
        info!("FOLD_STEP1 state written: {input_path} (framed: {framed_path}, {} B)", framed.len());
        if step == "1" {
            return;
        }
    }

    let all_data = std::fs::read(&input_path).expect("step 1 must run first");
    let input_bytes = std::fs::read(&framed_path).unwrap_or_else(|_| {
        postcard::to_stdvec(&all_data.as_slice()).unwrap()
    });

    let memory = rec_memory();

    if step == "2" || step == "all" {
        // ---- Step 2: trace the recursion guest (in-guest verify cost) ----
        let mut recursion_program = build_recursion_program(&memory);
        let trace_start = Instant::now();
        let (trace_iter, _, _, io) = recursion_program.trace(&input_bytes, &[], &[]);
        let mut rows: usize = 0;
        for _ in trace_iter {
            rows += 1;
        }
        let trace_s = trace_start.elapsed().as_secs_f64();
        let rv = postcard::from_bytes::<u32>(&io.outputs).unwrap_or(u32::MAX);
        info!(
            "FOLD_STEP2 k={k} rows={rows} seconds={trace_s:.3} all_valid={rv}"
        );
        assert!(rv == 1, "in-guest verification of the k proofs failed");
        std::fs::write(&rows_path, format!("{rows}")).unwrap();
        if step == "2" {
            return;
        }
    }

    if step == "3" || step == "all" {
        // ---- Step 3: fold preprocess + prove + verify ----
        let rows: usize = std::fs::read_to_string(&rows_path)
            .expect("step 2 must run first")
            .trim()
            .parse()
            .expect("rows file");
        let rec_max_trace = rows.max(1024).next_power_of_two();
        let mut recursion_program = build_recursion_program(&memory);
        let rec_prover_preprocessing: JoltProverPreprocessing = jolt_sdk::preprocess_program(
            &mut recursion_program,
            memory,
            rec_max_trace,
            ProgramPreprocessingMode::Full,
        )
        .expect("recursion preprocessing");
        let rec_verifier_preprocessing: JoltVerifierPreprocessing =
            jolt_sdk::verifier_preprocessing_from_prover(&rec_prover_preprocessing);
        info!("recursion preprocessing done (max_trace={rec_max_trace})");

        let now = Instant::now();
        let (fold_proof, fold_io): (RV64IMACProof, _) = jolt_sdk::prove_program(
            &recursion_program,
            &rec_prover_preprocessing,
            &input_bytes,
            &[],
            &[],
            None,
            None,
            None,
        )
        .expect("fold proof");
        let fold_prove_s = now.elapsed().as_secs_f64();
        let fold_bytes =
            bincode::serde::encode_to_vec(&fold_proof, bincode::config::standard())
                .unwrap()
                .len();

        let now = Instant::now();
        let fold_ok = jolt_sdk::jolt_verifier::verify::<
            jolt_sdk::VerifierField,
            jolt_sdk::VerifierPCS,
            jolt_sdk::VerifierVC,
            jolt_sdk::VerifierTranscript,
        >(&rec_verifier_preprocessing, &fold_io, &fold_proof, None)
        .is_ok();
        let fold_verify_s = now.elapsed().as_secs_f64();
        let fold_rv = postcard::from_bytes::<u32>(&fold_io.outputs).unwrap_or(u32::MAX);

        info!(
            "FOLD_RESULT k={k} rows={rows} fold_prove_s={fold_prove_s:.3} fold_bytes={fold_bytes} fold_verify_s={fold_verify_s:.4} fold_valid={fold_ok} fold_all_valid={fold_rv}"
        );
    }
}
