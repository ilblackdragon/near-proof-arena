//! `npai-bench`: speed of the Rust interpreter vs the compiled Lean reference
//! (`arena-interp-ref`) on a few verifier-shaped workloads. Also checks that
//! both produce byte-identical results on each workload.
//!
//! ```text
//! npai-bench --ref <arena-interp-ref> [--work DIR] [--scale K]
//! ```
#![forbid(unsafe_code)]

use arena_npai::asm::assemble_image;
use arena_npai::interp::{self, Inputs};
use arena_npai::report::{expect_json, to_hex};
use std::path::PathBuf;
use std::process::Command;
use std::time::{Duration, Instant};

struct W {
    name: String,
    src: String,
    proof: Vec<u8>,
    fuel: u64,
}

fn workloads(k: u64) -> Vec<W> {
    let loop_src = |n: u64| {
        format!(
            "const r1, {n}\nconst r3, 1\nloop:\nadd r2, r2, r1\nsub r1, r1, r3\njnz r1, loop\nconst r4, 1\nhalt r4\n"
        )
    };
    let sha_chain = |n: u64| {
        format!(
            ".mem 64\nconst r1, {n}\nconst r3, 1\nconst r5, 32\nloop:\nsha256 r0, r0, r5\nsub r1, r1, r3\njnz r1, loop\nout 0, r0, r5\nconst r4, 1\nhalt r4\n"
        )
    };
    let sha_big = |n: u64| {
        format!(
            ".mem {}\nconst r1, {n}\ntcopy r0, r0, r1, proof\nconst r2, {n}\nconst r5, 32\nsha256 r2, r0, r1\nout 0, r2, r5\nconst r4, 1\nhalt r4\n",
            n + 32
        )
    };
    let bytes = |n: u64| {
        format!(
            ".mem {n}\nconst r1, {n}\ntcopy r0, r0, r1, proof\nconst r3, 1\nconst r6, 0\nloop:\nld8 r2, r6\naddi r2, r2, 1\nst8 r6, r2\nadd r6, r6, r3\nltu r7, r6, r1\njnz r7, loop\nconst r5, 32\nout 0, r0, r5\nhalt r3\n"
        )
    };
    let pr = |n: u64| (0..n).map(|i| (i * 31 + 7) as u8).collect::<Vec<u8>>();
    vec![
        W {
            name: format!("alu-loop {}k iters", 10 * k),
            src: loop_src(10_000 * k),
            proof: vec![],
            fuel: u64::MAX,
        },
        W {
            name: format!("sha256-chain {}x32B", 1000 * k),
            src: sha_chain(1000 * k),
            proof: vec![],
            fuel: u64::MAX,
        },
        W {
            name: format!("sha256 {} KiB", 16 * k),
            src: sha_big(16384 * k),
            proof: pr(16384 * k),
            fuel: u64::MAX,
        },
        W {
            name: format!("ld8/st8 loop {} KiB", 4 * k),
            src: bytes(4096 * k),
            proof: pr(4096 * k),
            fuel: u64::MAX,
        },
    ]
}

fn lean_run(refexe: &str, dir: &std::path::Path, line: &str) -> (String, Duration) {
    let inp = dir.join("bench.in");
    let out = dir.join("bench.out");
    std::fs::write(&inp, format!("{line}\n")).unwrap();
    let t = Instant::now();
    let st = Command::new(refexe)
        .arg("batch")
        .arg(&inp)
        .arg(&out)
        .status()
        .unwrap();
    let dt = t.elapsed();
    assert!(st.success());
    (
        std::fs::read_to_string(&out).unwrap().trim().to_string(),
        dt,
    )
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |k: &str| {
        args.iter()
            .position(|a| a == k)
            .and_then(|i| args.get(i + 1))
            .cloned()
    };
    let refexe =
        get("--ref").unwrap_or_else(|| "formal-core/.lake/build/bin/arena-interp-ref".into());
    let k: u64 = get("--scale").map(|s| s.parse().unwrap()).unwrap_or(1);
    let dir = PathBuf::from(get("--work").unwrap_or_else(|| {
        std::env::temp_dir()
            .join("npai-bench")
            .display()
            .to_string()
    }));
    std::fs::create_dir_all(&dir).unwrap();
    // Process start-up of the Lean exe (subtracted below).
    let (_, startup) = lean_run(
        &refexe,
        &dir,
        "4e504149010000000000000000010000000000000000000000,,,,1",
    );
    println!("lean process start-up: {startup:.2?}");
    println!("| workload | fuel used | Rust | Lean (minus start-up) | ratio | same result |");
    println!("|---|---|---|---|---|---|");
    for w in workloads(k) {
        let img = assemble_image(&w.src).unwrap();
        let inp = Inputs {
            public: &[],
            claim: &[],
            proof: &w.proof,
        };
        let mut best = Duration::MAX;
        let mut res = String::new();
        for _ in 0..5 {
            let t = Instant::now();
            let r = interp::expect(&img, &inp, w.fuel);
            best = best.min(t.elapsed());
            res = expect_json(&r);
        }
        let used = res
            .split("\"fuel_used\":")
            .nth(1)
            .and_then(|s| s.split(',').next())
            .unwrap_or("?")
            .to_string();
        let line = format!("{},,,{},{}", to_hex(&img), to_hex(&w.proof), w.fuel);
        let (lres, ldt) = lean_run(&refexe, &dir, &line);
        let lnet = ldt.saturating_sub(startup);
        println!(
            "| {} | {used} | {best:.2?} | {lnet:.2?} | {:.0}x | {} |",
            w.name,
            lnet.as_secs_f64() / best.as_secs_f64().max(1e-9),
            if lres == res { "yes" } else { "NO" }
        );
    }
}
