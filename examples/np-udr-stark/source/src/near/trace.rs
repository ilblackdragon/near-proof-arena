//! All honest NEAR tables (`ZkFormal/Near/Render/{Tables,Trace}.lean`).

use p3_matrix::dense::RowMajorMatrix;
use rayon::prelude::*;

use super::ext::Ext;
use super::info::*;
use super::spec::Claim;
use super::{node, rcpt, small};
use crate::cols::TraceCols;
use crate::field::F;
use crate::sha;

/// Width of the `rcpt` table (`Rcpt.width`).
pub const RCPT_WIDTH: usize = 228;

/// `Bundle`: every generator's rows and the SHA messages.
pub struct Bundle {
    pub info: Info,
    pub walks: Vec<Vec<WStep>>,
    pub node: Vec<Row>,
    pub walk: Vec<Row>,
    pub rcpt: Vec<Row>,
    pub acct: Vec<Row>,
    pub mrk: Vec<Row>,
    pub sort: Vec<Row>,
    /// every SHA message: node, acct, mrk, rcpt
    pub msgs: Vec<Msg>,
    /// walks that fail (none for honest records)
    pub errors: Vec<String>,
}

impl Bundle {
    /// Tables `1 … 6` in `nearAir` order with their widths.
    pub fn parts(&self) -> [(&'static str, usize, &Vec<Row>); 6] {
        [
            ("node", node::WIDTH, &self.node),
            ("walk", small::WALK_WIDTH, &self.walk),
            ("rcpt", RCPT_WIDTH, &self.rcpt),
            ("acct", small::ACCT_WIDTH, &self.acct),
            ("mrk", small::MRK_WIDTH, &self.mrk),
            ("sort", small::SORT_WIDTH, &self.sort),
        ]
    }
}

/// `bundle c e`.
pub fn bundle(c: &Claim, e: &Ext) -> Bundle {
    let i = mk_info(c, e);
    let ws = walks_of(&i);
    let uses = edge_uses(&ws);
    let ((node, walk), ((rcpt, acct), (mrk, sort))) = rayon::join(
        || (node::node_rows_all(&i, &uses), small::walk_rows_all(&ws)),
        || {
            rayon::join(
                || (rcpt::rcpt_rows_all(&i), small::acct_rows_all(&i)),
                || (small::mrk_rows_all(&i), small::sort_rows_all(&i)),
            )
        },
    );
    let mut msgs = node::node_msgs(&i);
    msgs.extend(small::acct_msgs(&i));
    msgs.extend(small::mrk_msgs(&i));
    msgs.extend(rcpt::rcpt_msgs(&i));
    let errors = walk_errors(&i);
    Bundle { info: i, walks: ws, node, walk, rcpt, acct, mrk, sort, msgs, errors }
}

/// `shaMsgs`: every message with its digest provided once (`dmult = true`).
pub fn sha_msgs(ms: &[Msg]) -> Vec<sha::Msg> {
    ms.iter().map(|m| sha::Msg { id: m.id, bytes: m.bytes.clone(), dmult: true }).collect()
}

fn to_matrix(rows: &[Row], width: usize) -> RowMajorMatrix<F> {
    // `clog2 rows.size` rows (generators already pad to a power of two >= 2);
    // an empty table (the rcpt stub) is one zero row.
    let h = 1usize << clog2(rows.len());
    let mut v = vec![F::new(0); h * width];
    v.par_chunks_mut(width).zip(rows.par_iter()).for_each(|(o, r)| {
        for (x, &y) in o.iter_mut().zip(r.iter()) {
            *x = F::new(y);
        }
    });
    RowMajorMatrix::new(v, width)
}

/// The SHA table on the bundle's messages (`Sha.Gen`, `render` table 0).
pub fn sha_matrix(msgs: &[Msg]) -> RowMajorMatrix<F> {
    let (cells, _, _) = sha::sha_cells(&sha_msgs(msgs));
    RowMajorMatrix::new(cells.par_iter().map(|&x| F::new(x as u32)).collect(), sha::WIDTH)
}

/// The traces of a bundle in `nearAir` order (`0 sha, 1 node, 2 walk, 3 rcpt,
/// 4 acct, 5 mrk, 6 sort`).
pub fn bundle_traces(b: &Bundle) -> Vec<RowMajorMatrix<F>> {
    let mut out = vec![sha_matrix(&b.msgs)];
    for (_, w, rows) in b.parts() {
        out.push(to_matrix(rows, w));
    }
    out
}

/// **The honest trace** of a claim and its records (`Render.render`).
pub fn render(claim: &Claim, ext: &Ext) -> Vec<RowMajorMatrix<F>> { bundle_traces(&bundle(claim, ext)) }

/// Small table rows → compact columns (`clog2 rows` rows; empty → one zero row).
fn rows_cols(rows: &[Row], width: usize) -> TraceCols {
    TraceCols::from_rows(clog2(rows.len()), width, |r, b| {
        if let Some(x) = rows.get(r) {
            b[..x.len()].copy_from_slice(x);
        }
    })
}

/// The honest trace as compact columns: same content and heights as
/// [`render`], without materializing the big tables (`sha` from block
/// descriptors, `node` from per-node field layouts, rows on demand). Also
/// returns the walk errors (none for honest records).
pub fn render_cols_checked(claim: &Claim, ext: &Ext) -> (Vec<TraceCols>, Vec<String>) {
    let i = mk_info(claim, ext);
    let ws = walks_of(&i);
    let uses = edge_uses(&ws);
    let mut msgs = node::node_msgs(&i);
    msgs.extend(small::acct_msgs(&i));
    msgs.extend(small::mrk_msgs(&i));
    msgs.extend(rcpt::rcpt_msgs(&i));
    let sha = sha::sha_cols(&sha_msgs(&msgs));
    drop(msgs);
    let node = node::NodeTab::new(&i, &uses).cols();
    let mut out = vec![sha, node];
    out.push(rows_cols(&small::walk_rows_all(&ws), small::WALK_WIDTH));
    out.push(rows_cols(&rcpt::rcpt_rows_all(&i), RCPT_WIDTH));
    out.push(rows_cols(&small::acct_rows_all(&i), small::ACCT_WIDTH));
    out.push(rows_cols(&small::mrk_rows_all(&i), small::MRK_WIDTH));
    out.push(rows_cols(&small::sort_rows_all(&i), small::SORT_WIDTH));
    (out, walk_errors(&i))
}

/// [`render_cols_checked`] without the walk errors.
pub fn render_cols(claim: &Claim, ext: &Ext) -> Vec<TraceCols> { render_cols_checked(claim, ext).0 }
