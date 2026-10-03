//! In-process timing of `engine::prove` (dev only): `inproc CASES_DIR [reps]`.
//! Reports, per request, the MINIMUM over `reps` repetitions (robust to a
//! loaded machine) averaged over the cases, and the median for reference.
use std::time::Instant;
fn main() {
    let dir = std::env::args().nth(1).expect("cases dir");
    let reps: u32 = std::env::args().nth(2).map(|s| s.parse().unwrap()).unwrap_or(200);
    let mut cases = Vec::new();
    for e in std::fs::read_dir(&dir).unwrap() {
        let p = e.unwrap().path();
        cases.push((std::fs::read(p.join("request.bin")).unwrap(), std::fs::read(p.join("witness.bin")).unwrap()));
    }
    let (mut min_sum, mut med_sum) = (0f64, 0f64);
    for (r, w) in &cases {
        let mut ts: Vec<u128> = (0..reps)
            .map(|_| {
                let t = Instant::now();
                std::hint::black_box(reexec::engine::prove(r, w).unwrap());
                t.elapsed().as_nanos()
            })
            .collect();
        ts.sort_unstable();
        min_sum += ts[0] as f64;
        med_sum += ts[ts.len() / 2] as f64;
    }
    let n = cases.len() as f64;
    println!("{dir}: min {:.1} µs/request, median {:.1} µs/request", min_sum / n / 1e3, med_sum / n / 1e3);
}
