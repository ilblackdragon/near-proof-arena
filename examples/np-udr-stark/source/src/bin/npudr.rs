//! Developer CLI.
//!
//! * `npudr bench <width> <log_height> [tables]` — prove/verify a synthetic
//!   AIR (cube constraints, degree 4) and report time and proof size.
//! * `npudr toy <fib|multi> <log> <outdir>` — write `air.json`, `claim.bin`,
//!   `proof.bin`, `pub.bin` for differential tests against the Lean
//!   verifier.
//! * `npudr verify <air.json> <pub.bin> <claim.bin> <proof.bin>` —
//!   Rust reference verifier; exit 0 iff accepted.
//! * `npudr export <fib|multi|sha>` — print the toy AIR in `np-air-v1`.
//! * `npudr toy sha <log> <outdir> [len ...]` — SHA-256 toy (src/sha.rs):
//!   messages of the given lengths (default: 1000-byte messages filling a
//!   SHA table of `2^log` rows), proved and written as for the other toys.
//! * `npudr shatrace <out.bin> <len>...` — dump the honest SHA table in the
//!   `np-lean-shatrace` format (cross-check against the Lean generator).
//! * `npudr shacheck <len>...` — evaluate every constraint of the SHA toy on
//!   every row of the honest traces and check bus balance.
use std::time::Instant;

use npudr::air::Air;
use npudr::prover::{prove_bytes, ProveOptions};
use npudr::{check, sha, toy};
use p3_matrix::Matrix;
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
            let pd = b"bench".to_vec();
            let t = Instant::now();
            let b = prove_bytes(&air, traces, &pd, &[], &ProveOptions { verbose: true }).unwrap_or_else(|e| die(&e));
            let tp = t.elapsed().as_secs_f64();
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
            let t0 = Instant::now();
            let (air, traces, cb) = if a[2] == "sha" {
                let msgs = sha_msgs(a[3].parse().unwrap(), &a[5..]);
                (sha::sha_air(), sha::sha_traces(&msgs), vec![])
            } else {
                toy_instance(&a[2], a[3].parse().unwrap())
            };
            let tg = t0.elapsed().as_secs_f64();
            let dir = std::path::Path::new(&a[4]);
            std::fs::create_dir_all(dir).unwrap();
            let pd = b"np-udr-stark toy public tape".to_vec();
            let shapes: Vec<String> = traces.iter().map(|m| format!("{}x2^{}", m.width(), m.height().trailing_zeros())).collect();
            let t = Instant::now();
            let b = prove_bytes(&air, traces, &pd, &cb, &ProveOptions { verbose: false }).unwrap_or_else(|e| die(&e));
            let tp = t.elapsed().as_secs_f64();
            let t = Instant::now();
            let ok = verify(&air, &pd, &cb, &b);
            let tv = t.elapsed().as_secs_f64();
            eprintln!(
                "toy {} tables=[{}] tracegen={tg:.3}s prove={tp:.3}s proof={} B verify_rust={tv:.3}s ({}) threads={}",
                a[2],
                shapes.join(","),
                b.len(),
                if ok.is_ok() { "accept".to_string() } else { format!("{ok:?}") },
                rayon::current_num_threads()
            );
            std::fs::write(dir.join("air.json"), air.to_json()).unwrap();
            std::fs::write(dir.join("claim.bin"), &cb).unwrap();
            std::fs::write(dir.join("pub.bin"), &pd).unwrap();
            std::fs::write(dir.join("proof.bin"), b).unwrap();
        }
        Some("verify") => {
            let rd = |p: &String| std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")));
            let air = Air::from_json(&String::from_utf8(rd(&a[2])).unwrap()).unwrap_or_else(|e| die(&e));
            let pd = rd(&a[3]);
            match verify(&air, &pd, &rd(&a[4]), &rd(&a[5])) {
                Ok(()) => println!("accept"),
                Err(e) => {
                    println!("reject: {e}");
                    std::process::exit(1)
                }
            }
        }
        Some("shatrace") => {
            let lens: Vec<usize> = a[3..].iter().map(|s| s.parse().unwrap()).collect();
            std::fs::write(&a[2], sha::dump_trace(&sha::toy_msgs(&lens))).unwrap();
        }
        Some("shacheck") => {
            let lens: Vec<usize> = a[2..].iter().map(|s| s.parse().unwrap()).collect();
            let msgs = sha::toy_msgs(&lens);
            let air = sha::sha_air();
            let trs = sha::sha_traces(&msgs);
            let mut bad = false;
            for (ti, (t, tr)) in air.tables.iter().zip(&trs).enumerate() {
                let f = check::failing_constraints(t, tr, &[], 20);
                println!("table {ti} ({}): {} constraints, failing (constraint, row): {:?}", t.name, t.constraints.len(), f);
                bad |= !f.is_empty();
            }
            let im = check::bus_imbalance(&air, &trs, &[]);
            println!("bus imbalance: {} message(s) {:?}", im.len(), im.iter().take(5).collect::<Vec<_>>());
            if bad || !im.is_empty() {
                std::process::exit(1)
            }
        }
        Some("export") => {
            if a[2] == "sha" {
                println!("{}", sha::sha_air().to_json());
                return;
            }
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
        "bus" => {
            let lr = 4.max(log.saturating_sub(2));
            let xs: Vec<u32> = (0..(1u32 << log)).map(|i| (i * 7) % (1 << lr)).collect();
            (toy::bus_air(), toy::bus_traces(lr, log, &xs), vec![])
        }
        "wide" => {
            let w = 64;
            let air = Air { tables: vec![toy::cube_table(w, 22)], num_buses: 0, num_pub: 0 };
            (air, vec![toy::cube_trace(w, log)], vec![])
        }
        _ => die("toy: fib|multi|bus|wide"),
    }
}

/// SHA toy messages: explicit lengths, or 1000-byte messages filling `2^log`
/// SHA rows (each takes 1 + 17·16 = 273 rows).
fn sha_msgs(log: usize, lens: &[String]) -> Vec<sha::Msg> {
    let lens: Vec<usize> = if lens.is_empty() {
        vec![1000; ((1usize << log) / 273).max(1)]
    } else {
        lens.iter().map(|s| s.parse().unwrap()).collect()
    };
    sha::toy_msgs(&lens)
}
