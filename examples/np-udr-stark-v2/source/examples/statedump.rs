//! `cargo run --release --example statedump -- <d0a|d1> <air.json> <case_dir> <out_dir> [<table>...]`
//!
//! Lane pq-state-port (research only, not shipped; a cargo *example*, so the package is unchanged):
//! render the honest traces of the classical `nearAirV3` (D0a, 25 tables, the same generators as
//! `npudr v3prove`) or `nearAirV3D1` (30 tables, as `npudr v3d1prove`) for a real case, re-check
//! every classical constraint with the classical checker, and write them for the PQ (SWIRL) port.
//!
//! **Height normalisation** (`pad_pattern`, `recut`).  The classical renders use fixed heights
//! (`2^22` for the scheduler and receipt tables, `padLog22` rounding elsewhere), an artefact of the
//! classical FRI roll-in; `HoldsP` accepts any `1 ≤ log ≤ maxLog`.  Every render is "rows, then
//! padding rows", where the padding is a constant row or (`shuf`) a row counter, i.e. an arithmetic
//! progression `row(r) = row(u) + (r − u)·δ`.  With `u` = the first row from which the rows follow
//! that progression up to the last row, the table is re-cut at `log' = max(2, ⌈log₂(u + 1)⌉)` rows
//! (rows `< u` unchanged, then the progression).  This is a *generator* choice only: the re-cut
//! table is re-checked here against every classical constraint, and the PQ driver re-checks every
//! constraint and the balance of every bus (including the public messages), so the result is an
//! honest `HoldsP` trace by check, not by assumption.  The floor of 4 rows is NV's minimum height.
//! `--no-compact` keeps the classical heights.
//!
//! **Shape classes** (`--class=<class.json>`, lane E2E-D D-7): re-cut every table at the class's
//! log height instead (`{"names": [...], "heights": [[log, tight], ...]}`, the PQ driver's
//! `base-class` output; a table whose compact log exceeds the class's is an error), continuing the
//! same padding progression, so all chunks of a class have identical table heights. Re-checked
//! like every re-cut.
//!
//! **Growing past the classical render** (D-8).  A table whose render is full (no padding row, e.g.
//! `walk` with exactly `2^log` steps, `acct` with one record) has no padding progression: `pad_pattern`
//! then finds a spurious progression inside the real rows, and continuing it breaks the last-row
//! flags.  Every such render (`walk_aligned`, `acct_aligned`) pads with zero rows, so the grown table
//! is taken as the render's rows followed by zero rows (`grow_zero`) — exactly what the same
//! renderer produces at the larger height — and re-checked.  Two renders (`uniq`, `sort`) carry a
//! cyclic byte window (`(q + 2H − 1 − j) % H`, wrapping around the height), recomputed at the new
//! height (`grow_window`).  The order tried is: the padding progression, then `grow_zero` (with
//! the window recomputed for `uniq` / `sort`, the row counter for `shuf`, the carried counter
//! columns for `rng`), then `grow_keep_last`; the first that passes every
//! classical constraint is used (`--class` only; the compact re-cut never grows).
//!
//! **Census** (`--heights-only`, D-8): render, take the padding pattern, write `heights.json` (with
//! `last_nonzero`: one past the last non-zero row of the render, `pad_zero`: the render has a zero
//! padding row, and the width) and `pubmsgs.json`; no constraint re-check and no traces.  A census
//! is a size estimate only: chunks are admitted to a class by a full `--class` dump.
//!
//! Output (`out_dir`): `<table>.bin` (u32 LE `log_h`, `width`, then the row-major canonical
//! cells), `pubs.bin` (the public vector, u32 LE), `pubmsgs.json` (`[[bus, send, [felts]], …]`),
//! `prepared.bin` (the prepared public tape `cb'`), `claim.bin`, `hint.bin`, `heights.json`
//! (classical log, used rows, normalised log per table).
use npudr::air::Air;
use npudr::cols::TraceCols;
use npudr::field::F;
use npudr::v3::d1;
use npudr::v3::prove as vp;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use std::io::Write;

/// The padding pattern of a render: `delta` = last row − second-to-last row (zero for a constant
/// padding row; the row counter of `shuf`'s padding), and `u` = the first row from which every row
/// `r` equals `last + (r − (h−1))·delta` (an arithmetic progression up to the last row).
fn pad_pattern(tc: &TraceCols) -> (usize, Vec<F>) {
    let (h, w) = (tc.height(), tc.width());
    let mut last = vec![F::new(0); w];
    tc.row_into(h - 1, &mut last);
    let mut delta = vec![F::new(0); w];
    if h >= 2 {
        let mut prev = vec![F::new(0); w];
        tc.row_into(h - 2, &mut prev);
        for c in 0..w {
            delta[c] = last[c] - prev[c];
        }
    }
    let mut row = vec![F::new(0); w];
    let mut want = last.clone();
    let mut u = h;
    while u > 0 {
        tc.row_into(u - 1, &mut row);
        if row != want {
            break;
        }
        for c in 0..w {
            want[c] -= delta[c];
        }
        u -= 1;
    }
    (u, delta)
}

fn clog2(n: usize) -> usize {
    n.next_power_of_two().trailing_zeros() as usize
}

/// Re-cut `tc` at `log2` rows: rows `< u` from `tc`, then the padding progression
/// `row(u) + (r − u)·delta` (rows `≥ u` of `tc` where they exist).
fn recut(tc: &TraceCols, u: usize, delta: &[F], log2: usize) -> TraceCols {
    let w = tc.width();
    let h = tc.height();
    let mut base = vec![F::new(0); w];
    tc.row_into(u.min(h - 1), &mut base);
    let base_at = u.min(h - 1);
    TraceCols::from_rows(log2, w, |r, buf| {
        if r < u {
            for (c, x) in buf.iter_mut().enumerate() {
                *x = tc.get(r, c).as_canonical_u32();
            }
        } else {
            let k = F::from_u64((r - base_at) as u64);
            for (c, x) in buf.iter_mut().enumerate() {
                *x = (base[c] + delta[c] * k).as_canonical_u32();
            }
        }
    })
}

/// [E2E-D D-8] Grow `tc` to `log2` rows: every row of the render unchanged, then zero rows (what a
/// zero-padded render produces at the larger height). Re-checked by the caller.
fn grow_zero(tc: &TraceCols, log2: usize) -> TraceCols {
    let h = tc.height();
    TraceCols::from_rows(log2, tc.width(), |r, buf| {
        for (c, x) in buf.iter_mut().enumerate() {
            *x = if r < h { tc.get(r, c).as_canonical_u32() } else { 0 };
        }
    })
}

/// [E2E-D D-8] The two renders with a cyclic byte window (`uniq_aligned`, `sort_aligned`: columns
/// `w0 + j`, `j < 32`, hold the byte column at row `(q + 2H − 1 − j) % H`, Lean's `UniqGen` /
/// `SortGen`): `(byte column, w0)`. Their window wraps around the table height, so growing them
/// needs the window recomputed at the new height.
fn window_of(name: &str) -> Option<(usize, usize)> {
    match name {
        "uniq" => Some((10, 21)),
        "sort" => Some((6, 17)),
        _ => None,
    }
}

/// [E2E-D D-8] [`grow_zero`] for a cyclic-window render: the render's rows, then zero rows, with
/// the window columns recomputed at the new height `H' = 2^log2` from the (grown) byte column, as
/// the renderer computes them at `H'`. Re-checked by the caller.
fn grow_window(tc: &TraceCols, log2: usize, byte_col: usize, w0: usize) -> TraceCols {
    let h = tc.height();
    let n = 1usize << log2;
    let bb = |r: usize| if r < h { tc.get(r, byte_col).as_canonical_u32() } else { 0 };
    TraceCols::from_rows(log2, tc.width(), |q, buf| {
        for (c, x) in buf.iter_mut().enumerate() {
            *x = if (w0..w0 + 32).contains(&c) {
                let j = c - w0;
                bb((q + 2 * n).saturating_sub(1).saturating_sub(j) % n)
            } else if q < h {
                tc.get(q, c).as_canonical_u32()
            } else {
                0
            };
        }
    })
}

/// [E2E-D D-8] The render whose padding row is a row counter (`shuf_aligned`: `rowCell .pad r c =
/// if c = colRc then r else 0`, `colRc` = 1): its counter column.
fn counter_of(name: &str) -> Option<usize> {
    match name {
        "shuf" => Some(1),
        _ => None,
    }
}

/// [E2E-D D-8] Grow a row-counter-padded render: the render's rows, then its padding row at the
/// new heights (column `cc` = the row index, every other cell 0). Re-checked by the caller.
fn grow_counter(tc: &TraceCols, log2: usize, cc: usize) -> TraceCols {
    let h = tc.height();
    TraceCols::from_rows(log2, tc.width(), |q, buf| {
        for (c, x) in buf.iter_mut().enumerate() {
            *x = if q < h { tc.get(q, c).as_canonical_u32() } else if c == cc { q as u32 } else { 0 };
        }
    })
}

/// [E2E-D D-8] The render whose padding row is zero in its base columns and carries its counter
/// columns (`rng_aligned`: columns `>= 137` = the running active-row count `w` and the bits of
/// `W0 − w`, constant after the last active row): the first carried column.
fn carry_of(name: &str) -> Option<usize> {
    match name {
        "rng" => Some(137),
        _ => None,
    }
}

/// [E2E-D D-8] Grow a carry-padded render: the render's rows, then rows that are zero below column
/// `c0` and repeat the render's last row from `c0` on (what `rng_aligned` produces at the larger
/// height: no active row is added, so the count and its complement stay). Re-checked by the caller.
fn grow_carry(tc: &TraceCols, log2: usize, c0: usize) -> TraceCols {
    let h = tc.height();
    TraceCols::from_rows(log2, tc.width(), |q, buf| {
        for (c, x) in buf.iter_mut().enumerate() {
            *x = if q < h { tc.get(q, c).as_canonical_u32() } else if c >= c0 { tc.get(h - 1, c).as_canonical_u32() } else { 0 };
        }
    })
}

/// One past the last row of `tc` with a non-zero cell (0 for an all-zero table).
fn last_nonzero(tc: &TraceCols) -> usize {
    let w = tc.width();
    (0..tc.height())
        .rev()
        .find(|&r| (0..w).any(|c| tc.get(r, c).as_canonical_u32() != 0))
        .map_or(0, |r| r + 1)
}

/// [E2E-D D-7] Grow `tc` to `log2` rows: rows `< u` unchanged, rows `u..H-1` copies of the first
/// padding row `u`, and the render's last row kept last (for renders whose last padding row is
/// distinguished). Re-checked by the caller.
fn grow_keep_last(tc: &TraceCols, u: usize, log2: usize) -> TraceCols {
    let h = tc.height();
    let n = 1usize << log2;
    TraceCols::from_rows(log2, tc.width(), |r, buf| {
        let src = if r < u { r } else if r == n - 1 { h - 1 } else { u.min(h - 1) };
        for (c, x) in buf.iter_mut().enumerate() {
            *x = tc.get(src, c).as_canonical_u32();
        }
    })
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 5 {
        eprintln!("usage: statedump <d0a|d1> <air.json> <case_dir> <out_dir> [--no-compact] [<table>...]");
        std::process::exit(2);
    }
    let mode = a[1].as_str();
    let air = Air::from_json(&std::fs::read_to_string(&a[2]).unwrap()).unwrap();
    let cb = std::fs::read(format!("{}/claim.bin", a[3])).unwrap();
    let wb = std::fs::read(format!("{}/witness.bin", a[3])).unwrap();
    let od = std::path::PathBuf::from(&a[4]);
    std::fs::create_dir_all(&od).unwrap();
    let compact = !a[5..].iter().any(|x| x == "--no-compact");
    // [E2E-D D-8] census: heights only (no re-check, no traces)
    let census = a[5..].iter().any(|x| x == "--heights-only");
    // [E2E-D D-7] --class=<class.json>: per-table target log heights
    let class_logs: Option<std::collections::HashMap<String, usize>> = a[5..].iter().find_map(|x| x.strip_prefix("--class=")).map(|p| {
        let v: serde_json::Value = serde_json::from_slice(&std::fs::read(p).unwrap()).unwrap();
        let names = v["names"].as_array().expect("class names");
        let hs = v["heights"].as_array().expect("class heights");
        names.iter().zip(hs).map(|(n, h)| (n.as_str().unwrap().to_string(), h[0].as_u64().unwrap() as usize)).collect()
    });
    let wanted: Vec<&str> = a[5..].iter().filter(|x| !x.starts_with("--")).map(|s| s.as_str()).collect();
    let (order, tape, hint, entries, new_tabs): (&[&str], Vec<u8>, Vec<u8>, _, Vec<npudr::v3::Tab>) = match mode {
        "d0a" => {
            assert_eq!(air.tables.len(), 25, "not nearAirV3");
            let ci = vp::case_inputs(&cb, &wb, None).unwrap();
            (vp::ORDER, ci.tape, ci.hint.encode(), ci.entries, vec![])
        }
        "d1" => {
            assert_eq!(air.tables.len(), 30, "not nearAirV3D1");
            let ci = d1::case_inputs_d1(&cb, &wb).unwrap();
            let nt = d1::d1_tables(&ci).unwrap();
            (d1::ORDER_D1, ci.tape, ci.hint, ci.entries, nt)
        }
        m => panic!("mode {m}"),
    };
    let pubs = npudr::verifier::public_inputs(&air, &tape);
    let names: Vec<&str> = if wanted.is_empty() { order.to_vec() } else { wanted };
    let mut heights = serde_json::Map::new();
    for name in names {
        let t = order.iter().position(|n| *n == name).unwrap_or_else(|| panic!("no table {name}"));
        let tc0 = if t < 25 {
            vp::render_cols(name, &entries[name]).unwrap()
        } else {
            let tb = &new_tabs[t - 25];
            let w = tb.width;
            TraceCols::from_rows(tb.log, w, |r, buf| buf.copy_from_slice(&tb.cells[r * w..(r + 1) * w]))
        };
        if !census {
            let bad = npudr::check::failing_constraints_cols(&air.tables[t], &tc0, &pubs, 10);
            assert!(bad.is_empty(), "{name}: classical constraint failure {bad:?}");
        }
        let (u, delta) = pad_pattern(&tc0);
        // [E2E-D D-8] any two last rows form a "progression": a non-constant progression is taken as
        // the padding only when it spans >= 3 rows (else the last row alone is padding, its
        // continuation unknown: a 2-row `shuf` with one real row read as all padding corrupted it)
        let prog_ok = delta.iter().all(|x| x.as_canonical_u32() == 0) || tc0.height() - u >= 3;
        let u = if prog_ok { u } else { tc0.height() - 1 };
        if census {
            let mut pr = vec![F::new(0); tc0.width()];
            tc0.row_into(tc0.height() - 1, &mut pr);
            let pad_zero = u < tc0.height() && pr.iter().all(|x| x.as_canonical_u32() == 0);
            heights.insert(
                name.to_string(),
                serde_json::json!({"classical_log": tc0.log_h, "used_rows": u, "log": clog2(u + 1).max(2),
                    "max_log": air.tables[t].max_log, "last_nonzero": last_nonzero(&tc0),
                    "pad_zero": pad_zero, "width": tc0.width()}),
            );
            continue;
        }
        let log0 = tc0.log_h;
        let mut log2 = clog2(u + 1).max(2);
        if let Some(cl) = &class_logs {
            let c = *cl.get(name).unwrap_or_else(|| panic!("{name}: not in the class"));
            assert!(log2 <= c, "{name}: compact log {log2} exceeds the class log {c}");
            log2 = c;
        }
        let tc = if (compact || class_logs.is_some()) && log2 != tc0.log_h {
            let tc1 = recut(&tc0, u, &delta, log2);
            let bad = npudr::check::failing_constraints_cols(&air.tables[t], &tc1, &pubs, 10);
            // [E2E-D D-7] growing past the classical render: if the progression fails, try the
            // other padding shape the renders use (constant padding row, distinguished last row)
            let bad = if prog_ok { bad } else { vec![(usize::MAX, usize::MAX)] };
            let (tc1, bad) = if !bad.is_empty() && log2 > tc0.log_h {
                // [E2E-D D-8] the render's rows, then zero rows (zero-padded renders: a full `walk`
                // or `acct`)
                let tz = grow_zero(&tc0, log2);
                let badz = npudr::check::failing_constraints_cols(&air.tables[t], &tz, &pubs, 10);
                let (tz, badz) = match window_of(name) {
                    Some((bc, w0)) if !badz.is_empty() => {
                        let tw = grow_window(&tc0, log2, bc, w0);
                        let badw = npudr::check::failing_constraints_cols(&air.tables[t], &tw, &pubs, 10);
                        (tw, badw)
                    }
                    _ => (tz, badz),
                };
                let (tz, badz) = match carry_of(name) {
                    Some(c0) if !badz.is_empty() => {
                        let tw = grow_carry(&tc0, log2, c0);
                        let badw = npudr::check::failing_constraints_cols(&air.tables[t], &tw, &pubs, 10);
                        (tw, badw)
                    }
                    _ => (tz, badz),
                };
                let (tz, badz) = match counter_of(name) {
                    Some(cc) if !badz.is_empty() => {
                        let tw = grow_counter(&tc0, log2, cc);
                        let badw = npudr::check::failing_constraints_cols(&air.tables[t], &tw, &pubs, 10);
                        (tw, badw)
                    }
                    _ => (tz, badz),
                };
                if badz.is_empty() {
                    let how = if window_of(name).is_some() {
                        " (cyclic window recomputed if needed)"
                    } else if counter_of(name).is_some() {
                        " (or its row-counter padding)"
                    } else if carry_of(name).is_some() {
                        " (or its carried counter columns)"
                    } else {
                        ""
                    };
                    eprintln!("statedump: {name}: grown with zero rows after the render{how}");
                    (tz, badz)
                } else {
                    let tc2 = grow_keep_last(&tc0, u, log2);
                    let bad2 = npudr::check::failing_constraints_cols(&air.tables[t], &tc2, &pubs, 10);
                    if bad2.is_empty() { eprintln!("statedump: {name}: grown with a constant padding row and the render's last row"); }
                    (tc2, bad2)
                }
            } else {
                (tc1, bad)
            };
            if !bad.is_empty() && std::env::var("STATEDUMP_CLASS_PROBE").is_ok() {
                // [E2E-D D-7] probe mode: report and keep the compact cut
                for r in u.saturating_sub(2)..tc0.height() {
                    let row: Vec<u32> = (0..tc0.width()).map(|c| tc0.get(r, c).as_canonical_u32()).collect();
                    eprintln!("CLASS_ROW {name} {r} {:?}", row);
                }
                eprintln!("CLASS_RECUT_FAIL {name} classical_log {} used {u} class_log {log2} {:?}", tc0.log_h, &bad[..bad.len().min(3)]);
                let l = clog2(u + 1).max(2);
                if l != tc0.log_h { recut(&tc0, u, &delta, l) } else { tc0.clone() }
            } else {
                assert!(bad.is_empty(), "{name}: re-cut at log {log2} fails classical constraints {bad:?}");
                tc1
            }
        } else {
            tc0
        };
        assert!(tc.log_h <= air.tables[t].max_log, "{name}: log {} > maxLog", tc.log_h);
        heights.insert(
            name.to_string(),
            serde_json::json!({"classical_log": log0, "used_rows": u, "log": tc.log_h, "max_log": air.tables[t].max_log}),
        );
        let (h, w) = (tc.height(), tc.width());
        let mut out = Vec::with_capacity(8 + 4 * h * w);
        out.extend_from_slice(&(tc.log_h as u32).to_le_bytes());
        out.extend_from_slice(&(w as u32).to_le_bytes());
        let mut row = vec![F::new(0); w];
        for r in 0..h {
            tc.row_into(r, &mut row);
            for x in &row {
                out.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
            }
        }
        std::fs::write(od.join(format!("{name}.bin")), out).unwrap();
        eprintln!(
            "statedump: table {t:2} {name:9} classical log {:2} used rows {u:8} -> log {:2} width {w:3}: classical constraints ok",
            log0, tc.log_h
        );
    }
    if census {
        std::fs::write(od.join("heights.json"), serde_json::Value::Object(heights).to_string()).unwrap();
        let msgs = npudr::verifier::pub_msgs(&air, &tape);
        let js: Vec<serde_json::Value> = msgs
            .iter()
            .map(|(b, s, m)| serde_json::json!([b, s, m.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>()]))
            .collect();
        std::fs::write(od.join("pubmsgs.json"), serde_json::to_string(&js).unwrap()).unwrap();
        eprintln!("statedump: census {mode} tape {} B, {} public messages", tape.len(), msgs.len());
        return;
    }
    let mut pb = Vec::with_capacity(4 * pubs.len());
    for x in &pubs {
        pb.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
    }
    std::fs::write(od.join("pubs.bin"), pb).unwrap();
    std::fs::write(od.join("prepared.bin"), &tape).unwrap();
    std::fs::write(od.join("claim.bin"), &cb).unwrap();
    std::fs::write(od.join("hint.bin"), &hint).unwrap();
    std::fs::write(od.join("heights.json"), serde_json::Value::Object(heights).to_string()).unwrap();
    let msgs = npudr::verifier::pub_msgs(&air, &tape);
    let mut f = std::fs::File::create(od.join("pubmsgs.json")).unwrap();
    let js: Vec<serde_json::Value> = msgs
        .iter()
        .map(|(b, s, m)| serde_json::json!([b, s, m.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>()]))
        .collect();
    f.write_all(serde_json::to_string(&js).unwrap().as_bytes()).unwrap();
    eprintln!(
        "statedump: {mode} tape {} B, hint {} B, {} public messages, {} public inputs",
        tape.len(),
        hint.len(),
        msgs.len(),
        pubs.len()
    );
}
