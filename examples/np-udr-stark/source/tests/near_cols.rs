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
        assert_eq!((m.height(), m.width()), (t.height(), t.width()), "{name}: table {k} shape");
        for r in 0..m.height() {
            for col in 0..m.width() {
                assert_eq!(m.values[r * m.width() + col].as_canonical_u32(), t.cols[col].get(r), "{name}: table {k} row {r} col {col}");
            }
        }
    }
    let (cb, _, tr) = near::prepare_cols(req, wit).unwrap();
    assert_eq!(cb, c.encode());
    assert_eq!(tr.len(), 7);
}

#[test]
fn render_cols_matches_render() {
    let d = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../oracle/fixtures/public/cases");
    let mut v: Vec<_> = std::fs::read_dir(d).unwrap().map(|e| e.unwrap().path()).collect();
    v.sort();
    for d in v {
        same(&d.display().to_string(), &std::fs::read(d.join("request.bin")).unwrap(), &std::fs::read(d.join("witness.bin")).unwrap());
    }
    let g = genmax::gen_max(&genmax::Opts { target_bytes: 60_000, n: Some(5), ..Default::default() }).unwrap();
    assert!(g.exts > 0);
    same("genmax 60k", &g.request, &g.witness);
}
