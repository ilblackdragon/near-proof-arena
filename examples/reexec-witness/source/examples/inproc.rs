//! In-process timing of `engine::prove` (dev only): `inproc CASES_DIR [iters]`.
use std::time::Instant;
fn main() {
    let dir = std::env::args().nth(1).expect("cases dir");
    let iters: u32 = std::env::args().nth(2).map(|s| s.parse().unwrap()).unwrap_or(200);
    let mut cases = Vec::new();
    for e in std::fs::read_dir(&dir).unwrap() {
        let p = e.unwrap().path();
        cases.push((std::fs::read(p.join("request.bin")).unwrap(), std::fs::read(p.join("witness.bin")).unwrap()));
    }
    let t = Instant::now();
    let mut n = 0;
    for _ in 0..iters {
        for (r, w) in &cases {
            let (c, p) = reexec::engine::prove(r, w).unwrap();
            n += c.len() + p.len();
        }
    }
    let per = t.elapsed().as_nanos() as f64 / (iters as f64 * cases.len() as f64);
    println!("{dir}: {:.1} µs/request ({} bytes)", per / 1e3, n);
}
