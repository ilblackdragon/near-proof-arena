//! Developer CLI.
//!
//! * `npudr bench <width> <log_height> [tables] [--out <dir>]` — prove/verify a
//!   synthetic AIR (cube constraints, degree 4) and report time and proof
//!   size; with `--out`, also write `air.json`, `pub.bin`, `claim.bin`,
//!   `proof.bin` (for `np-lean-verify` timings).
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
//! * `npudr nearrender <request.bin> <witness.bin> <out.bin>` — the NEAR honest
//!   tables 1..6 and SHA messages in the `np-lean-render` format.
//! * `npudr nearcheck <request.bin> <witness.bin>` — evaluate every nearAir
//!   constraint on the honest traces (incl. sha) and check bus balance.
use std::time::Instant;

use npudr::air::Air;
use npudr::prover::{prove_bytes, ProveOptions};
use npudr::{check, near, sha, toy};
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
            let (pos, out): (Vec<&String>, Option<&String>) = match a.iter().position(|x| x == "--out") {
                Some(i) => (a[2..i].iter().chain(&a[i + 2..]).collect(), a.get(i + 1)),
                None => (a[2..].iter().collect(), None),
            };
            let w: usize = pos[0].parse().unwrap();
            let h: usize = pos[1].parse().unwrap();
            let nt: usize = pos.get(2).map(|s| s.parse().unwrap()).unwrap_or(1);
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
            if let Some(dir) = out {
                let dir = std::path::Path::new(dir);
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(dir.join("air.json"), air.to_json()).unwrap();
                std::fs::write(dir.join("pub.bin"), &pd).unwrap();
                std::fs::write(dir.join("claim.bin"), []).unwrap();
                std::fs::write(dir.join("proof.bin"), &b).unwrap();
            }
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
        Some("nearrender") => {
            let t = Instant::now();
            let (req, wit) = (std::fs::read(&a[2]).unwrap(), std::fs::read(&a[3]).unwrap());
            let (c, e) = near::load(&req, &wit).unwrap_or_else(|e| die(&e));
            let b = near::trace::bundle(&c, &e);
            if !b.errors.is_empty() {
                eprintln!("npudr nearrender: walk errors {:?}", b.errors);
            }
            std::fs::write(&a[4], near::dump(&c.encode(), &b)).unwrap();
            let rows: Vec<usize> = b.parts().iter().map(|p| p.2.len()).collect();
            eprintln!("npudr nearrender: {} nodes, {} receipts, {} msgs, rows {rows:?}, {} ms",
                e.ns.len(), e.rs.len(), b.msgs.len(), t.elapsed().as_millis());
        }
        Some("nearcheck") => {
            // every constraint of every nearAir table on the honest traces, and bus balance
            let (req, wit) = (std::fs::read(&a[2]).unwrap(), std::fs::read(&a[3]).unwrap());
            let t = Instant::now();
            let (cb, air, trs) = near::prepare(&req, &wit).unwrap_or_else(|e| die(&e));
            let tg = t.elapsed().as_millis();
            let pubs = near::public_of(&cb);
            let names = ["sha", "node", "walk", "rcpt", "acct", "mrk", "sort"];
            let mut bad = false;
            for (k, (tab, tr)) in air.tables.iter().zip(&trs).enumerate() {
                let f = check::failing_constraints(tab, tr, &pubs, 20);
                println!("table {k} {:5} {:>8} x {:3}: {} failing (constraint,row) {:?}", names[k], tr.height(), tr.width(), f.len(), f);
                bad |= !f.is_empty();
            }
            let imb = check::bus_imbalance(&air, &trs, &pubs);
            let mut per_bus = std::collections::BTreeMap::new();
            for (bus, _, _, _) in &imb {
                *per_bus.entry(*bus).or_insert(0usize) += 1;
            }
            println!("bus imbalance: {} messages, per bus {per_bus:?}", imb.len());
            for (bus, msg, s, r) in imb.iter().take(10) {
                println!("  bus {bus} msg {:?} sent {s} received {r}", &msg[..msg.len().min(12)]);
            }
            println!("render {tg} ms, check {} ms", t.elapsed().as_millis() - tg);
            if bad || !imb.is_empty() {
                std::process::exit(1);
            }
        }
        _ => die("usage: npudr bench|toy|verify|export|nearrender|nearcheck ..."),
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
