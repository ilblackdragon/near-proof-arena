//! `render_cols` (compact, row functions) = `render` (row-major) cell for cell,
//! on the public fixtures and on a generated case with empty-key extensions.
use npudr::near::{self, genmax, trace};
use p3_field::PrimeField32;
use p3_matrix::Matrix;

fn same(name: &str, req: &[u8], wit: &[u8]) {
    let (c, e) = near::load(req, wit).unwrap_or_else(|e| panic!("{name}: {e}"));
    let a = trace::render(&c, &e);
    let b = trace::render_cols(&c, &e);
    assert_eq!(a.len(), b.len());
    for (k, (m, t)) in a.iter().zip(&b).enumerate() {
        assert_eq!(
            (m.height(), m.width()),
            (t.height(), t.width()),
            "{name}: table {k} shape"
        );
        for r in 0..m.height() {
            for col in 0..m.width() {
                assert_eq!(
                    m.values[r * m.width() + col].as_canonical_u32(),
                    t.cols[col].get(r),
                    "{name}: table {k} row {r} col {col}"
                );
            }
        }
    }
    let (cb, _, tr) = near::prepare_cols(req, wit).unwrap();
    assert_eq!(cb, c.encode());
    assert_eq!(tr.len(), 7);
}

#[test]
fn render_cols_matches_render() {
    let d = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../oracle/fixtures/public/cases");
    let mut v: Vec<_> = std::fs::read_dir(d)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    v.sort();
    for d in v {
        same(
            &d.display().to_string(),
            &std::fs::read(d.join("request.bin")).unwrap(),
            &std::fs::read(d.join("witness.bin")).unwrap(),
        );
    }
    let g = genmax::gen_max(&genmax::Opts {
        target_bytes: 60_000,
        n: Some(5),
        ..Default::default()
    })
    .unwrap();
    assert!(g.exts > 0);
    same("genmax 60k", &g.request, &g.witness);
}

/// `check::*_cols` (the max-case checker behind `npudr nearcolscheck`): honest
/// compact traces pass; a corrupted walk cell is caught (constraint or bus).
#[test]
fn cols_checker() {
    use npudr::check;
    use npudr::cols::Col;
    let g = genmax::gen_max(&genmax::Opts {
        target_bytes: 60_000,
        n: Some(5),
        ..Default::default()
    })
    .unwrap();
    let (cb, air, mut trs) = near::prepare_cols(&g.request, &g.witness).unwrap();
    let pubs = near::public_of(&cb);
    for (t, tr) in air.tables.iter().zip(&trs) {
        assert!(check::failing_constraints_cols(t, tr, &pubs, 5).is_empty());
    }
    let (imb, total) = check::bus_imbalance_cols(&air, &trs, &pubs);
    assert!(imb.is_empty() && total > 0, "{imb:?}");
    // walk table (2), first row: bump every column that holds a small value
    for c in &mut trs[2].cols {
        match c {
            Col::U8(v) => v[0] = v[0].wrapping_add(1),
            Col::U16(v) => v[0] = v[0].wrapping_add(1),
            Col::U32(v) => v[0] = v[0].wrapping_add(1),
        }
    }
    let bad = !check::failing_constraints_cols(&air.tables[2], &trs[2], &pubs, 5).is_empty();
    let (imb, _) = check::bus_imbalance_cols(&air, &trs, &pubs);
    assert!(
        bad && !imb.is_empty(),
        "corruption not detected: constraints {bad}, buses {imb:?}"
    );
}
