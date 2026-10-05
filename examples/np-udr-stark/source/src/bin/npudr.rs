//! Developer CLI.
//!
//! * `npudr bench <width> <log_height> [tables]` — prove/verify a synthetic
//!   AIR (cube constraints, degree 4) and report time and proof size.
//! * `npudr toy <fib|multi> <log> <outdir>` — write `air.json`, `claim.bin`,
//!   `proof.bin`, `pub.bin` for differential tests against the Lean
//!   verifier.
//! * `npudr verify <air.json> <pub.bin> <claim.bin> <proof.bin>` —
//!   Rust reference verifier; exit 0 iff accepted.
//! * `npudr export <fib|multi>` — print the toy AIR in `np-air-v1`.
use std::time::Instant;

use npudr::air::Air;
use npudr::prover::{prove_bytes, ProveOptions};
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
            let (air, traces, cb) = toy_instance(&a[2], a[3].parse().unwrap());
            let dir = std::path::Path::new(&a[4]);
            std::fs::create_dir_all(dir).unwrap();
            let pd = b"np-udr-stark toy public tape".to_vec();
            let b = prove_bytes(&air, traces, &pd, &cb, &ProveOptions { verbose: false }).unwrap_or_else(|e| die(&e));
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
        Some("eval-random") => {
            use npudr::field::{decode_chal, EF};
            use p3_field::PrimeField32;
            let air = Air::from_json(&std::fs::read_to_string(&a[2]).unwrap()).unwrap_or_else(|e| die(&e));
            let seed: u32 = a[3].parse().unwrap();
            let rnd = |kind: u8, t: usize, i: usize| -> EF {
                let mut m = b"np-eval".to_vec();
                m.extend_from_slice(&seed.to_le_bytes());
                m.push(kind);
                m.extend_from_slice(&(t as u32).to_le_bytes());
                m.extend_from_slice(&(i as u32).to_le_bytes());
                decode_chal(&npudr::hash::sha256(&m))
            };
            for (t, tab) in air.tables.iter().enumerate() {
                let tape = npudr::air::Tape::compile(&tab.constraints);
                // pub(i) values are extension elements here: evaluate with a tape over EF
                let mut regs = vec![];
                tape.eval_ext(&mut regs, |c, n| rnd(n as u8, t, c), |i| rnd(2, t, i), [rnd(3, t, 0), rnd(4, t, 0), rnd(5, t, 0)]);
                for (i, &o) in tape.outputs.iter().enumerate() {
                    let ls: Vec<String> =
                        npudr::field::ef_coeffs(&regs[o as usize]).iter().map(|x| x.as_canonical_u32().to_string()).collect();
                    println!("{t} {i} {}", ls.join(" "));
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
