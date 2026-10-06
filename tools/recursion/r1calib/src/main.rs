//! R1 ("one STARK, many segment tables, global buses") cost-model calibration
//! for np-udr-stark-v1. See docs/research/recursion-r1-cost.md.
//!
//! * `r1calib shape <air.json>` — per table: width, aux width (K cols),
//!   quotient chunks, finals, degree, #constraints, #interactions (JSON lines).
//! * `r1calib breakdown <air.json> <public.bin> <claim.bin> <proof.bin>` —
//!   exact byte breakdown of a real proof (query positions replayed from the
//!   transcript), checked to sum to the file size; Rust verify time.
//! * `r1calib expect <air.json> <h_0,h_1,...> [trials]` — the same breakdown
//!   for random query positions (Monte Carlo mean over `trials`).
//! * `r1calib seg <S> <log_h> <w_0,w_1,...> [--k K] [--out dir] [--no-verify]`
//!   — build and prove a synthetic R1 instance: S segments, each with tables
//!   of widths w_i at height 2^log_h (table 0 carries the global boundary bus
//!   with K state columns), plus one io table; prints prove/verify time and
//!   size, and writes air.json/pub.bin/claim.bin/proof.bin with --out.
use std::time::Instant;

use npudr::air::{Air, Expr as E, Interaction, Table};
use npudr::field::F;
use npudr::mmcs::index_sets;
use npudr::protocol::{oracle_shapes, parse_prefix, Schedule, NUM_CHUNKS, PER_CHUNK};
use npudr::prover::{prove_bytes, ProveOptions};
use npudr::transcript::Transcript;
use npudr::verifier::{replay, verify};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

fn die(m: &str) -> ! {
    eprintln!("r1calib: {m}");
    std::process::exit(2)
}

#[derive(Default, Clone, Debug)]
struct Breakdown {
    header: f64,
    roots: f64,
    finals: f64,
    ood: f64,
    fri_roots: f64,
    final_poly: f64,
    /// per oracle (main, aux, quot, fri_0..): (row bytes, sibling bytes)
    oracles: Vec<(f64, f64)>,
    /// per oracle: distinct leaves, sibling count
    counts: Vec<(f64, f64)>,
}

impl Breakdown {
    fn total(&self) -> f64 {
        self.header
            + self.roots
            + self.finals
            + self.ood
            + self.fri_roots
            + self.final_poly
            + self.oracles.iter().map(|(a, b)| a + b).sum::<f64>()
    }
    fn add(&mut self, o: &Breakdown, s: f64) {
        self.header += s * o.header;
        self.roots += s * o.roots;
        self.finals += s * o.finals;
        self.ood += s * o.ood;
        self.fri_roots += s * o.fri_roots;
        self.final_poly += s * o.final_poly;
        if self.oracles.is_empty() {
            self.oracles = vec![(0.0, 0.0); o.oracles.len()];
            self.counts = vec![(0.0, 0.0); o.oracles.len()];
        }
        for i in 0..o.oracles.len() {
            self.oracles[i].0 += s * o.oracles[i].0;
            self.oracles[i].1 += s * o.oracles[i].1;
            self.counts[i].0 += s * o.counts[i].0;
            self.counts[i].1 += s * o.counts[i].1;
        }
    }
    fn print(&self, label: &str) {
        let names = |i: usize| match i {
            0 => "main".to_string(),
            1 => "aux".to_string(),
            2 => "quot".to_string(),
            k => format!("fri{}", k - 3),
        };
        println!("{label}: total {:.0} B", self.total());
        println!(
            "  header {:.0}  roots {:.0}  finals {:.0}  ood {:.0}  fri_roots {:.0}  final_poly {:.0}",
            self.header, self.roots, self.finals, self.ood, self.fri_roots, self.final_poly
        );
        for (i, ((r, s), (u, n))) in self.oracles.iter().zip(&self.counts).enumerate() {
            println!("  {:<6} rows {:>10.0}  siblings {:>9.0}  (leaves {:.1}, sib {:.1})", names(i), r, s, u, n);
        }
        let rows: f64 = self.oracles.iter().map(|x| x.0).sum();
        let sibs: f64 = self.oracles.iter().map(|x| x.1).sum();
        println!("  sum rows {rows:.0}  sum siblings {sibs:.0}");
    }
}

/// Byte breakdown of the proof for schedule `sch` and layer-0 positions `qs`
/// (FORMATS.md §5; protocol.rs `Proof::to_bytes`, mmcs.rs `write_opening`).
fn breakdown(sch: &Schedule, qs: &[usize]) -> Breakdown {
    let nt = sch.num_tables();
    let mut b = Breakdown {
        header: (8 + nt) as f64,
        roots: 3.0 * 64.0,
        finals: 32.0 * sch.n_finals.iter().sum::<usize>() as f64,
        ood: 32.0 * sch.num_ood() as f64,
        fri_roots: 64.0 * sch.committed.len() as f64,
        final_poly: 64.0,
        ..Default::default()
    };
    for (shape, sh) in oracle_shapes(sch) {
        let idx: Vec<usize> = qs.iter().map(|&x| x >> sh).collect();
        let l0 = shape.iter().map(|s| s.0).max().unwrap();
        let sets = index_sets(l0, &idx);
        let mut rows = 0usize;
        let mut sib = 0usize;
        for k in 0..=l0 {
            let wsum: usize = shape.iter().filter(|s| s.0 + k == l0).map(|s| s.1).sum();
            rows += sets[k].len() * wsum * 4;
            if k >= 1 {
                for &j in &sets[k] {
                    let a = sets[k - 1].binary_search(&(2 * j)).is_ok();
                    let c = sets[k - 1].binary_search(&(2 * j + 1)).is_ok();
                    if !(a && c) {
                        sib += 1;
                    }
                }
            }
        }
        b.oracles.push((rows as f64, (sib * 64) as f64));
        b.counts.push((sets[0].len() as f64, sib as f64));
    }
    b
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
}

fn read(p: &str) -> Vec<u8> {
    std::fs::read(p).unwrap_or_else(|e| die(&format!("{p}: {e}")))
}

fn load_air(p: &str) -> Air {
    Air::from_json(&String::from_utf8(read(p)).unwrap()).unwrap_or_else(|e| die(&e))
}

fn shape_cmd(air: &Air) {
    for (i, t) in air.tables.iter().enumerate() {
        println!(
            "{{\"t\":{i},\"name\":\"{}\",\"width\":{},\"aux\":{},\"quot\":{},\"finals\":{},\"degree\":{},\"constraints\":{},\"interactions\":{},\"maxLog\":{}}}",
            t.name,
            t.width,
            t.aux_width(),
            t.num_quot_chunks(),
            t.num_finals(),
            t.degree(),
            t.constraints.len(),
            t.interactions.len(),
            t.max_log
        );
    }
}

/// Synthetic R1 instance (see module doc).
fn seg_instance(s: usize, log_h: usize, widths: &[usize], k: usize) -> (Air, Vec<RowMajorMatrix<F>>) {
    assert!(widths[0] >= k && k >= 1);
    let n = 1usize << log_h;
    let mut tables = vec![];
    let mut traces = vec![];
    // io table: cols 0..k = initial state (row 0 pinned), k..2k = final state.
    {
        let mut cs = vec![];
        for c in 0..k {
            cs.push(E::mul(E::IsFirst, E::sub(E::col(c), E::c(c as u64 + 2))));
        }
        let msg = |tag: usize, off: usize| -> Vec<E> {
            let mut m = vec![E::c(tag as u64)];
            m.extend((0..k).map(|c| E::col(off + c)));
            m
        };
        let mut t = Table {
            name: "io".into(),
            width: 2 * k,
            constraints: cs,
            interactions: vec![
                Interaction { bus: 0, mult: vec![E::IsFirst], msg: msg(0, 0), send: true },
                Interaction { bus: 0, mult: vec![E::IsFirst], msg: msg(s, k), send: false },
            ],
            max_log: 22,
        };
        t.constraints.extend(npudr::aux::bit_constraints(&t));
        tables.push(t);
    }
    // global chain values per state column: x' = x^3 + c, x_0 = c + 2
    let w0 = widths[0];
    let mut cur: Vec<F> = (0..w0).map(|c| F::from_u64(c as u64 + 2)).collect();
    for seg in 0..s {
        for (ti, &w) in widths.iter().enumerate() {
            if ti == 0 {
                let mut cs = vec![];
                for c in 0..w {
                    let cube = E::mul(E::col(c), E::mul(E::col(c), E::col(c)));
                    cs.push(E::mul(E::IsTransition, E::sub(E::nxt(c), E::add(cube, E::c(c as u64)))));
                }
                let msg = |tag: usize| -> Vec<E> {
                    let mut m = vec![E::c(tag as u64)];
                    m.extend((0..k).map(E::col));
                    m
                };
                let mut t = Table {
                    name: format!("seg{seg}_exec"),
                    width: w,
                    constraints: cs,
                    interactions: vec![
                        Interaction { bus: 0, mult: vec![E::IsFirst], msg: msg(seg), send: false },
                        Interaction { bus: 0, mult: vec![E::IsLast], msg: msg(seg + 1), send: true },
                    ],
                    max_log: 22,
                };
                t.constraints.extend(npudr::aux::bit_constraints(&t));
                tables.push(t);
                let mut v = vec![F::ZERO; w * n];
                for r in 0..n {
                    for c in 0..w {
                        v[r * w + c] = cur[c];
                    }
                    if r + 1 < n {
                        for c in 0..w {
                            cur[c] = cur[c] * cur[c] * cur[c] + F::from_u64(c as u64);
                        }
                    }
                }
                traces.push(RowMajorMatrix::new(v, w));
            } else {
                let mut t = npudr::toy::cube_table(w, 22);
                t.name = format!("seg{seg}_t{ti}");
                tables.push(t);
                traces.push(npudr::toy::cube_trace(w, log_h));
            }
        }
    }
    // io trace (16 rows): row 0 = init ‖ final
    let io_h = 16usize;
    let mut io = vec![F::ZERO; 2 * k * io_h];
    for c in 0..k {
        io[c] = F::from_u64(c as u64 + 2);
        io[k + c] = cur[c];
    }
    traces.insert(0, RowMajorMatrix::new(io, 2 * k));
    (Air { tables, num_buses: 1, num_pub: 0 }, traces)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("shape") => shape_cmd(&load_air(&a[2])),
        Some("breakdown") => {
            let air = load_air(&a[2]);
            let (pubt, cb, pb) = (read(&a[3]), read(&a[4]), read(&a[5]));
            let (proof, sch, _) = parse_prefix(&air, &pb).unwrap_or_else(|| die("parse prefix"));
            let mut tr = Transcript::new(&pubt, &cb);
            let ch = replay(&sch, &mut tr, &proof);
            let b = breakdown(&sch, &ch.queries);
            println!("heights {:?} l0 {} fri_l {} committed {:?}", sch.heights, sch.l0, sch.fri_l, sch.committed);
            b.print("exact");
            println!("file {} B, model-exact {} B, diff {}", pb.len(), b.total() as usize, pb.len() as i64 - b.total() as i64);
            let t = Instant::now();
            let ok = verify(&air, &pubt, &cb, &pb);
            println!("rust_verify {:.3}s {:?}", t.elapsed().as_secs_f64(), ok.map(|_| "accept"));
            let mut rng = Rng(1);
            let mut m = Breakdown::default();
            let trials = 200;
            for _ in 0..trials {
                let qs: Vec<usize> =
                    (0..NUM_CHUNKS * PER_CHUNK).map(|_| (rng.next() as usize) & ((1 << sch.l0) - 1)).collect();
                m.add(&breakdown(&sch, &qs), 1.0 / trials as f64);
            }
            m.print("expected (random positions, 200 trials)");
        }
        Some("expect") => {
            let air = load_air(&a[2]);
            let hs: Vec<usize> = a[3].split(',').map(|x| x.parse().unwrap()).collect();
            let trials: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(200);
            let sch = Schedule::new(&air, &hs).unwrap_or_else(|e| die(&e));
            let mut rng = Rng(7);
            let mut m = Breakdown::default();
            for _ in 0..trials {
                let qs: Vec<usize> =
                    (0..NUM_CHUNKS * PER_CHUNK).map(|_| (rng.next() as usize) & ((1 << sch.l0) - 1)).collect();
                m.add(&breakdown(&sch, &qs), 1.0 / trials as f64);
            }
            m.print(&format!("expected ({trials} trials)"));
        }
        Some("seg") => {
            let s: usize = a[2].parse().unwrap();
            let log_h: usize = a[3].parse().unwrap();
            let widths: Vec<usize> = a[4].split(',').map(|x| x.parse().unwrap()).collect();
            let opt = |name: &str| a.iter().position(|x| x == name).map(|i| a[i + 1].clone());
            let k: usize = opt("--k").map(|v| v.parse().unwrap()).unwrap_or(8.min(widths[0]));
            let no_verify = a.iter().any(|x| x == "--no-verify");
            let t0 = Instant::now();
            let (air, traces) = seg_instance(s, log_h, &widths, k);
            let tg = t0.elapsed().as_secs_f64();
            let heights: Vec<usize> = traces.iter().map(|m| {
                use p3_matrix::Matrix;
                m.height().trailing_zeros() as usize
            }).collect();
            let cells: usize = {
                use p3_matrix::Matrix;
                traces.iter().map(|m| m.width() * m.height()).sum()
            };
            let pd = b"r1calib seg".to_vec();
            let verbose = std::env::var("NPUDR_VERBOSE").is_ok_and(|v| v == "1");
            let t = Instant::now();
            let pb = prove_bytes(&air, traces, &pd, &[], &ProveOptions { verbose }).unwrap_or_else(|e| die(&e));
            let tp = t.elapsed().as_secs_f64();
            let (tv, ok) = if no_verify {
                (0.0, "skipped".to_string())
            } else {
                let t = Instant::now();
                let r = verify(&air, &pd, &[], &pb);
                (t.elapsed().as_secs_f64(), format!("{:?}", r.map(|_| "accept")))
            };
            let sch = Schedule::new(&air, &heights).unwrap();
            println!(
                "seg S={s} log_h={log_h} widths={:?} k={k} tables={} cells={cells} ood={} finals={} tracegen={tg:.2}s prove={tp:.3}s proof={} B verify_rust={tv:.3}s {ok} threads={}",
                widths,
                air.tables.len(),
                sch.num_ood(),
                sch.n_finals.iter().sum::<usize>(),
                pb.len(),
                rayon::current_num_threads()
            );
            if let Some(dir) = opt("--out") {
                let dir = std::path::Path::new(&dir);
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(dir.join("air.json"), air.to_json()).unwrap();
                std::fs::write(dir.join("pub.bin"), &pd).unwrap();
                std::fs::write(dir.join("claim.bin"), []).unwrap();
                std::fs::write(dir.join("proof.bin"), &pb).unwrap();
            }
        }
        _ => die("usage: r1calib shape|breakdown|expect|seg ... (see module doc)"),
    }
}
