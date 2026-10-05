//! `rcpt` table generator (`src/near/rcpt.rs`, port of `Render/Rcpt.lean`) on
//! the public fixtures:
//!
//! * every constraint of the `rcpt` table of `nearAir` (table 3 of
//!   `near-air.json`) vanishes on the rendered rows;
//! * the bus messages derived from the rows (`DIGEST` windows, `BYTES`
//!   emissions) agree with `rcptMsgs` (every emitted byte is a byte of the
//!   message with that id, each (id, pos) exactly once, all positions covered);
//! * if `RCPT_LEAN_DIR` is set, the rows equal the Lean render cell for cell
//!   (`<dir>/<case>.rows`, one row per line, decimal cells; produced by
//!   `rcptRowsAll` via `lake env lean`).
use std::collections::BTreeMap;

use npudr::check;
use npudr::field::F;
use npudr::near::{self, info, rcpt};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

fn cases() -> Vec<std::path::PathBuf> {
    let d = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../oracle/fixtures/public/cases");
    let mut v: Vec<_> = std::fs::read_dir(d).unwrap().map(|e| e.unwrap().path()).collect();
    v.sort();
    v
}

const RCPT_TABLE: usize = 3;
const WIDTH: usize = 228;

#[test]
fn fixtures_rcpt() {
    let air = near::near_air();
    let tab = &air.tables[RCPT_TABLE];
    assert_eq!(tab.width, WIDTH);
    let lean_dir = std::env::var("RCPT_LEAN_DIR").ok();
    let mut fails = vec![];
    for d in cases() {
        let name = d.file_name().unwrap().to_string_lossy().to_string();
        let req = std::fs::read(d.join("request.bin")).unwrap();
        let wit = std::fs::read(d.join("witness.bin")).unwrap();
        let (c, e) = near::load(&req, &wit).unwrap_or_else(|err| panic!("{name}: {err}"));
        let i = info::mk_info(&c, &e);
        let rows = rcpt::rcpt_rows_all(&i);
        assert!(rows.iter().all(|r| r.len() == WIDTH));
        assert!(rows.len().is_power_of_two());
        let pubs = near::public_of(&c.encode());
        let vals: Vec<F> = rows.iter().flatten().map(|&x| F::new(x)).collect();
        let tr = RowMajorMatrix::new(vals, WIDTH);
        let bad = check::failing_constraints(tab, &tr, &pubs, 50);
        if !bad.is_empty() {
            fails.push(format!("{name}: failing (constraint,row) {bad:?}"));
        }
        // BYTES emissions vs rcptMsgs
        let msgs: BTreeMap<u32, Vec<u8>> = rcpt::rcpt_msgs(&i).into_iter().map(|m| (m.id, m.bytes)).collect();
        let mut seen: BTreeMap<(u32, u32), u32> = BTreeMap::new();
        for r in &rows {
            for e in 0..3 {
                if r[34 + 4 * e] == 1 {
                    let (id, pos, v) = (r[31 + 4 * e], r[32 + 4 * e], r[33 + 4 * e]);
                    let m = msgs.get(&id).unwrap_or_else(|| panic!("{name}: emission to unknown id {id}"));
                    assert_eq!(m.get(pos as usize).map(|&b| b as u32), Some(v), "{name}: id {id} pos {pos}");
                    *seen.entry((id, pos)).or_default() += 1;
                }
            }
        }
        for (id, m) in &msgs {
            for p in 0..m.len() as u32 {
                assert_eq!(seen.get(&(*id, p)).copied(), Some(1), "{name}: id {id} pos {p} emitted once");
            }
        }
        assert_eq!(seen.len(), msgs.values().map(|m| m.len()).sum::<usize>(), "{name}: extra emissions");
        let _ = F::ZERO;
        let mut lean_note = String::new();
        if let Some(ld) = &lean_dir {
            let p = std::path::Path::new(ld).join(format!("{name}.rows"));
            let txt = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{p:?}: {e}"));
            let lean: Vec<Vec<u64>> =
                txt.lines().map(|l| l.split_whitespace().map(|x| x.parse().unwrap()).collect()).collect();
            assert_eq!(lean.len(), rows.len(), "{name}: row count vs Lean");
            let mut diffs = vec![];
            for (ri, (a, b)) in rows.iter().zip(&lean).enumerate() {
                for c in 0..WIDTH {
                    let lv = b.get(c).copied().unwrap_or(0) % 2013265921;
                    if a[c] as u64 != lv {
                        diffs.push((ri, c, a[c], lv));
                    }
                }
            }
            if !diffs.is_empty() {
                fails.push(format!("{name}: {} cells differ from Lean, first {:?}", diffs.len(), &diffs[..diffs.len().min(20)]));
            }
            lean_note = " = Lean".into();
        }
        eprintln!("{name}: receipts={} rows={} constraints ok={}{lean_note}", i.n_rcpt(), rows.len(), bad.is_empty());
    }
    assert!(fails.is_empty(), "{}", fails.join("\n"));
}
