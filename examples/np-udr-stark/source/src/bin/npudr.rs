//! Developer CLI.
//!
//! * `npudr bench <width> <log_height> [tables]` — prove/verify a synthetic
//!   AIR (cube constraints, degree 4) and report time and proof size.
//! * `npudr toy <fib|multi> <log> <outdir>` — write `air.json`, `claim.bin`,
//!   `proof.bin`, `pubdigest.bin` for differential tests against the Lean
//!   verifier.
//! * `npudr verify <air.json> <pubdigest.bin> <claim.bin> <proof.bin>` —
//!   Rust reference verifier; exit 0 iff accepted.
//! * `npudr export <fib|multi>` — print the toy AIR in `np-air-v1`.
use std::time::Instant;

use npudr::air::Air;
use npudr::prover::{prove, ProveOptions};
use npudr::toy;
use npudr::verifier::verify;

fn die(m: &str) -> ! {
    eprintln!("npudr: {m}");
    std::process::exit(2)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("bench") => {
            let w: usize = a[2].parse().unwrap();
            let h: usize = a[3].parse().unwrap();
            let nt: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(1);
            let air = Air {
                tables: (0..nt).map(|_| toy::cube_table(w, 22)).collect(),
                num_buses: 0,
                num_pub: 0,
            };
            let traces: Vec<_> = (0..nt).map(|i| toy::cube_trace(w, h.saturating_sub(i).max(1))).collect();
            let pd = [0u8; 32];
            let t = Instant::now();
            let p = prove(&air, traces, &pd, &[], &ProveOptions { verbose: true }).unwrap_or_else(|e| die(&e));
            let tp = t.elapsed().as_secs_f64();
            let b = p.to_bytes();
            let t = Instant::now();
            verify(&air, &pd, &[], &b).unwrap_or_else(|e| die(&e));
            let tv = t.elapsed().as_secs_f64();
            println!(
                "tables={nt} width={w} log_h={h} prove={tp:.3}s proof={} B ({:.3} MiB) verify_rust={tv:.3}s threads={}",
                b.len(),
                b.len() as f64 / (1u64 << 20) as f64,
                rayon::current_num_threads()
            );
        }
        Some("toy") => {
            let (air, traces, cb) = toy_instance(&a[2], a[3].parse().unwrap());
            let dir = std::path::Path::new(&a[4]);
            std::fs::create_dir_all(dir).unwrap();
            let pd = npudr::hash::sha256(b"np-udr-stark toy public tape");
            let p = prove(&air, traces, &pd, &cb, &ProveOptions { verbose: false }).unwrap_or_else(|e| die(&e));
            std::fs::write(dir.join("air.json"), air.to_json()).unwrap();
            std::fs::write(dir.join("claim.bin"), &cb).unwrap();
            std::fs::write(dir.join("pubdigest.bin"), pd).unwrap();
            std::fs::write(dir.join("proof.bin"), p.to_bytes()).unwrap();
        }
        Some("verify") => {
            let rd = |p: &String| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
            let air = Air::from_json(&String::from_utf8(rd(&a[2])).unwrap()).unwrap_or_else(|e| die(&e));
            let pd: [u8; 32] = rd(&a[3]).try_into().unwrap_or_else(|_| die("pubdigest must be 32 bytes"));
            match verify(&air, &pd, &rd(&a[4]), &rd(&a[5])) {
                Ok(()) => println!("accept"),
                Err(e) => {
                    println!("reject: {e}");
                    std::process::exit(1)
                }
            }
        }
        Some("export") => {
            let (air, _, _) = toy_instance(&a[2], 3);
            println!("{}", air.to_json());
        }
        _ => die("usage: npudr bench|toy|verify|export ..."),
    }
}

fn toy_instance(which: &str, log: usize) -> (Air, Vec<p3_matrix::dense::RowMajorMatrix<npudr::field::F>>, Vec<u8>) {
    let (tr, last) = toy::fib_trace(log, 1, 1);
    let cb = toy::fib_claim(1, 1, last);
    match which {
        "fib" => (toy::fib_air(), vec![tr], cb),
        "multi" => (toy::multi_air(), vec![tr, toy::cube_trace(3, log.saturating_sub(2).max(1)), toy::cube_trace(1, 1)], cb),
        _ => die("toy: fib|multi"),
    }
}
