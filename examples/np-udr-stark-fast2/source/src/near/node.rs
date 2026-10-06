//! Honest rows of the `node` table (`ZkFormal/Near/Render/Node.lean`).

use std::collections::HashMap;

use super::ext::*;
use super::ids::*;
use super::info::*;
use super::spec::Bytes;

pub const WIDTH: usize = 163;
pub const SUMR: usize = 3;
pub const SZ: usize = 152;
const S_TAG: usize = 14;

/// A hash window.
#[derive(Clone, Debug, Default)]
pub struct Win {
    pub look: bool,
    pub cid: usize,
    pub clen: usize,
    pub cres: usize,
    pub w: usize,
    pub lastw: bool,
    pub slot: Option<usize>,
    pub pre: Bytes,
    pub post: Bytes,
}

#[derive(Clone, Debug)]
pub enum Fld {
    Tag,
    Hpl,
    Hpf,
    Key,
    Vlen,
    Vh(Win),
    Bm,
    Ch(Win),
    Mem,
}

impl Fld {
    fn state(&self) -> usize {
        S_TAG
            + match self {
                Fld::Tag => 0,
                Fld::Hpl => 1,
                Fld::Hpf => 2,
                Fld::Key => 3,
                Fld::Vlen => 4,
                Fld::Vh(_) => 5,
                Fld::Bm => 6,
                Fld::Ch(_) => 7,
                Fld::Mem => 8,
            }
    }
    fn len(&self, hplen: usize) -> usize {
        match self {
            Fld::Tag | Fld::Hpf => 1,
            Fld::Hpl | Fld::Vlen => 4,
            Fld::Key => hplen.saturating_sub(1),
            Fld::Vh(_) | Fld::Ch(_) => 32,
            Fld::Bm => 2,
            Fld::Mem => 8,
        }
    }
    fn win(&self) -> Option<&Win> {
        match self {
            Fld::Vh(w) | Fld::Ch(w) => Some(w),
            _ => None,
        }
    }
    fn chw(&self) -> Option<&Win> {
        match self {
            Fld::Ch(w) => Some(w),
            _ => None,
        }
    }
    fn nib(&self) -> bool { matches!(self, Fld::Hpf | Fld::Key) }
}

fn kid_win(i: &Info, kid: &Kid, w: usize, lastw: bool, slot: Option<usize>) -> Win {
    match kid {
        Kid::Node(c) => Win {
            look: true,
            cid: *c,
            clen: i.pre_at(*c).len(),
            cres: i.res_or(*c, *c),
            w,
            lastw,
            slot,
            pre: i.pre_dig(*c),
            post: i.post_dig(*c),
        },
        Kid::Hash(h) => Win { w, lastw, slot, pre: h.clone(), post: h.clone(), ..Default::default() },
        Kid::None => Win { w, lastw, slot, ..Default::default() },
    }
}

fn val_win(i: &Info, n: usize, v: &VSlot) -> Win {
    match v {
        VSlot::Touched => {
            Win { look: true, pre: sha_n(i.vpre_at(n)), post: sha_n(i.vpost_at(n)), ..Default::default() }
        }
        VSlot::Ref(_, h) => Win { pre: h.clone(), post: h.clone(), ..Default::default() },
    }
}

fn branch_wins(i: &Info, kids: &[Kid]) -> Vec<Fld> {
    let present: Vec<(usize, &Kid)> = kids.iter().enumerate().filter(|(_, k)| **k != Kid::None).collect();
    let np = present.len();
    present.iter().enumerate().map(|(w, (j, k))| Fld::Ch(kid_win(i, k, w, w + 1 == np, Some(*j)))).collect()
}

fn fields_of(i: &Info, n: usize, nr: &NodeRec) -> Vec<Fld> {
    use Fld::*;
    match nr {
        NodeRec::Leaf(_, v, _) => vec![Tag, Hpl, Hpf, Key, Vlen, Vh(val_win(i, n, v)), Mem],
        NodeRec::Ext(_, kid, _) => vec![Tag, Hpl, Hpf, Key, Ch(kid_win(i, kid, 0, true, None)), Mem],
        NodeRec::Branch(None, kids, _) => [vec![Tag, Bm], branch_wins(i, kids), vec![Mem]].concat(),
        NodeRec::Branch(Some(v), kids, _) => {
            [vec![Tag, Vlen, Vh(val_win(i, n, v)), Bm], branch_wins(i, kids), vec![Mem]].concat()
        }
    }
}

fn bit_of(x: u128, b: usize) -> u64 { ((x >> b) & 1) as u64 }
fn b2n(b: bool) -> u64 { b as u64 }

fn is_le(nr: &NodeRec) -> bool { !matches!(nr, NodeRec::Branch(..)) }
fn is_ext(nr: &NodeRec) -> bool { matches!(nr, NodeRec::Ext(..)) }
fn hplen_of(nr: &NodeRec) -> usize { if is_le(nr) { 1 + nr.key().len() / 2 } else { 0 } }
fn odd_of(nr: &NodeRec) -> usize { if is_le(nr) { nr.key().len() % 2 } else { 0 } }
fn nokey_of(nr: &NodeRec) -> bool { is_le(nr) && hplen_of(nr) == 1 }
fn bmv_of(nr: &NodeRec) -> u128 { if is_le(nr) { 0 } else { bitmap_of(nr.kids()) } }
fn pop_of(nr: &NodeRec) -> u64 { (0..16).map(|b| bit_of(bmv_of(nr), b)).sum() }
fn nochild_of(nr: &NodeRec) -> bool { !is_le(nr) && pop_of(nr) == 0 }
fn xrv_of(nr: &NodeRec) -> bool { matches!(nr, NodeRec::Ext(_, Kid::Node(_), _)) }
fn xres_of(i: &Info, nr: &NodeRec) -> usize {
    match nr {
        NodeRec::Ext(_, Kid::Node(c), _) => i.res_or(*c, *c),
        _ => 0,
    }
}
fn xdead_of(nr: &NodeRec) -> bool { is_ext(nr) && !xrv_of(nr) }
fn xlast0_of(nr: &NodeRec) -> bool { is_ext(nr) && nokey_of(nr) }
fn eext_of(nr: &NodeRec) -> bool { is_ext(nr) && nokey_of(nr) && odd_of(nr) == 0 }
fn type_of(nr: &NodeRec) -> [u64; 4] {
    match nr {
        NodeRec::Leaf(..) => [1, 0, 0, 0],
        NodeRec::Ext(..) => [0, 1, 0, 0],
        NodeRec::Branch(None, ..) => [0, 0, 1, 0],
        NodeRec::Branch(Some(_), ..) => [0, 0, 0, 1],
    }
}

/// A node row.
#[derive(Clone, Debug)]
struct NRec<'a> {
    n: usize,
    pos: usize,
    f: &'a Fld,
    idx: usize,
    b: u8,
    pb: u8,
}

type EdgeG = Option<(Edge, bool)>;

fn edge_a(i: &Info, r: &NRec, nr: &NodeRec) -> EdgeG {
    let n = r.n;
    let odd = odd_of(nr);
    let ki = 2 * r.idx + odd;
    let b = r.b as usize;
    if r.pos == 0 && n == 0 {
        return Some((vec![0, 0, SYM_START, i.res_or(n, n), 0], true));
    }
    match &*r.f {
        Fld::Ch(wn) => (r.idx == 0 && wn.look && !is_le(nr)).then(|| (vec![n, 0, wn.slot.unwrap_or(0), wn.cres, 0], true)),
        Fld::Vh(wn) => (r.idx == 0 && wn.look)
            .then(|| (vec![n, type_of(nr)[0] as usize * nr.key().len(), SYM_END, n, 0], true)),
        Fld::Hpf => (odd == 1).then(|| {
            (
                if xlast0_of(nr) { vec![n, 0, b % 16, xres_of(i, nr), 0] } else { vec![n, 0, b % 16, n, 1] },
                !(nokey_of(nr) && xdead_of(nr)),
            )
        }),
        Fld::Key => Some((vec![n, ki, b / 16, n, ki + 1], true)),
        _ => None,
    }
}

fn edge_b(i: &Info, r: &NRec, nr: &NodeRec) -> EdgeG {
    let n = r.n;
    let ki = 2 * r.idx + odd_of(nr);
    let b = r.b as usize;
    match &*r.f {
        Fld::Key => Some(if r.idx + 1 == Fld::Key.len(hplen_of(nr)) && is_ext(nr) {
            (vec![n, ki + 1, b % 16, xres_of(i, nr), 0], !xdead_of(nr))
        } else {
            (vec![n, ki + 1, b % 16, n, ki + 2], true)
        }),
        _ => None,
    }
}

fn dig_of(r: &NRec) -> Option<(usize, usize, bool)> {
    match &*r.f {
        Fld::Ch(w) if r.idx == 0 && w.look => Some((msg_id(K_NPRE, w.cid), w.clen, true)),
        Fld::Vh(w) if r.idx == 0 && w.look => Some((msg_id(K_VPRE, r.n), 72, false)),
        _ => None,
    }
}

fn edge_cell(a: &EdgeG, j: usize) -> u64 { a.as_ref().map(|(e, _)| e.get(j).copied().unwrap_or(0) as u64).unwrap_or(0) }
fn gate_cell(a: &EdgeG) -> u64 { matches!(a, Some((_, true))) as u64 }
fn mult_cell(a: &EdgeG, u: &HashMap<Edge, usize>) -> u64 {
    match a {
        Some((e, true)) => u.get(e).copied().unwrap_or(0) as u64,
        _ => 0,
    }
}

/// Per-node data shared by the rows of a node.
struct NodeCtx {
    nr: NodeRec,
    len: usize,
    hplen: usize,
    depth: usize,
    sz_before: usize,
    /// fields and their start positions (ascending), rows `row0 ..`
    fields: Vec<Fld>,
    starts: Vec<usize>,
    row0: usize,
}

fn row_cells(i: &Info, u: &HashMap<Edge, usize>, r: &NRec<'_>, cx: &NodeCtx, row: &mut [u32]) {
    let nr = &cx.nr;
    let n = r.n;
    let b = r.b as u128;
    let ty = type_of(nr);
    let ea = edge_a(i, r, nr);
    let eb = edge_b(i, r, nr);
    let dg = dig_of(r);
    let chw = r.f.chw();
    let win = r.f.win();
    for (col, out) in row.iter_mut().enumerate() {
        let v: u64 = match col {
            0 => 1,
            1 => b2n(r.pos == 0),
            2 => b2n(r.pos + 1 == cx.len),
            3 => 0,
            4 => n as u64,
            5 => r.pos as u64,
            6 => cx.len as u64,
            7 => cx.depth as u64,
            8 => r.b as u64,
            9 => r.pb as u64,
            10..=13 => ty[col - 10],
            23 => r.idx as u64,
            24 => b2n(r.idx == 0),
            25 => b2n(r.idx + 1 == r.f.len(cx.hplen)),
            26 => cx.hplen as u64,
            27 => odd_of(nr) as u64,
            28 => b2n(nokey_of(nr)),
            14..=22 => b2n(r.f.state() == col),
            29..=32 => if r.f.nib() { bit_of(b / 16, col - 29) } else { 0 },
            33..=36 => if r.f.nib() { bit_of(b % 16, col - 33) } else { 0 },
            37..=52 => bit_of(bmv_of(nr), col - 37),
            53 => b2n(nochild_of(nr)),
            54..=69 => chw.map(|w| b2n(w.slot == Some(col - 54))).unwrap_or(0),
            70 => chw.map(|w| w.w as u64).unwrap_or(0),
            71 => chw.map(|w| b2n(w.lastw)).unwrap_or(0),
            72..=103 => win.map(|w| w.pre.get(r.idx + col - 72).copied().unwrap_or(0) as u64).unwrap_or(0),
            104..=135 => win.map(|w| w.post.get(r.idx + col - 104).copied().unwrap_or(0) as u64).unwrap_or(0),
            136 => chw.map(|w| b2n(w.look)).unwrap_or(0),
            137 => chw.map(|w| w.cid as u64).unwrap_or(0),
            138 => chw.map(|w| w.clen as u64).unwrap_or(0),
            139 => b2n(nr.touched()),
            140 => dg.map(|d| d.0 as u64).unwrap_or(0),
            141 => dg.map(|d| d.1 as u64).unwrap_or(0),
            142 => dg.is_some() as u64,
            143 => matches!(dg, Some((_, _, true))) as u64,
            144 => b2n(r.pos == 0 && nr.touched()),
            145 => gate_cell(&ea),
            146..=149 => edge_cell(&ea, col - 145),
            150 => mult_cell(&ea, u),
            151 => mult_cell(&eb, u),
            152 => (cx.sz_before + r.pos) as u64,
            153 => i.res_or(n, n) as u64,
            154 => chw.map(|w| w.cres as u64).unwrap_or(0),
            155 => xres_of(i, nr) as u64,
            156 => b2n(xrv_of(nr)),
            157 => b2n(xdead_of(nr)),
            158 => b2n(xlast0_of(nr)),
            159 => b2n(eext_of(nr)),
            160 => gate_cell(&eb),
            161 => edge_cell(&eb, 3),
            162 => edge_cell(&eb, 4),
            _ => 0,
        };
        *out = cell(v);
    }
}

/// `nodeSz I n`: revealed size added by node `n`.
fn node_sz(i: &Info, n: usize) -> usize { i.pre_at(n).len() + if i.node_at(n).touched() { 72 } else { 0 } }

/// The `node` table as a row function (`nodeRowsAll I uses`): one row per
/// serialized byte (node-id order), the `SUM` row, padding (`sz` carried).
pub struct NodeTab<'a> {
    i: &'a Info,
    uses: &'a HashMap<Edge, usize>,
    ctxs: Vec<NodeCtx>,
    nrecs: usize,
    total: usize,
    /// `log2` of the height
    pub log_h: usize,
}

impl<'a> NodeTab<'a> {
    pub fn new(i: &'a Info, uses: &'a HashMap<Edge, usize>) -> NodeTab<'a> {
        let nn = i.ns.len();
        let mut ctxs = Vec::with_capacity(nn);
        let (mut sz, mut row0) = (0usize, 0usize);
        for n in 0..nn {
            let nr = i.node_at(n);
            let hplen = hplen_of(&nr);
            let fields = fields_of(i, n, &nr);
            let mut starts = Vec::with_capacity(fields.len());
            let mut pos = 0;
            for f in &fields {
                starts.push(pos);
                pos += f.len(hplen);
            }
            let cx = NodeCtx {
                len: i.pre_at(n).len(),
                hplen,
                depth: i.depth.get(n).copied().unwrap_or(0),
                sz_before: sz,
                nr,
                fields,
                starts,
                row0,
            };
            sz += node_sz(i, n);
            row0 += pos;
            ctxs.push(cx);
        }
        NodeTab { i, uses, ctxs, nrecs: row0, total: sz, log_h: log_of(row0 + 1) }
    }

    /// Row `q` into `row` (`WIDTH` entries, zeroed by the caller).
    pub fn row(&self, q: usize, row: &mut [u32]) {
        if q < self.nrecs {
            let n = self.ctxs.partition_point(|c| c.row0 <= q) - 1;
            let cx = &self.ctxs[n];
            let pos = q - cx.row0;
            let k = cx.starts.partition_point(|&s| s <= pos) - 1;
            let (pre, post) = (self.i.pre_at(n), self.i.post_at(n));
            let r = NRec {
                n,
                pos,
                f: &cx.fields[k],
                idx: pos - cx.starts[k],
                b: pre.get(pos).copied().unwrap_or(0),
                pb: post.get(pos).copied().unwrap_or(0),
            };
            row_cells(self.i, self.uses, &r, cx, row);
        } else {
            row[SZ] = cell(self.total as u64);
            if q == self.nrecs {
                row[SUMR] = 1;
                let slack = 3_000_000usize.saturating_sub(self.total) as u128;
                for (col, x) in row.iter_mut().enumerate().take(94).skip(72) {
                    *x = bit_of(slack, col - 72) as u32;
                }
            }
        }
    }

    /// As compact columns.
    pub fn cols(&self) -> crate::cols::TraceCols { crate::cols::TraceCols::from_rows(self.log_h, WIDTH, |q, b| self.row(q, b)) }
}

/// `nodeRowsAll I uses` as rows.
pub fn node_rows_all(i: &Info, uses: &HashMap<Edge, usize>) -> Vec<Row> {
    let t = NodeTab::new(i, uses);
    (0..1usize << t.log_h)
        .map(|q| {
            let mut row = vec![0u32; WIDTH];
            t.row(q, &mut row);
            row
        })
        .collect()
}

/// `nodeMsgs I`: `NPRE(N)`, `NPOST(N)`.
pub fn node_msgs(i: &Info) -> Vec<Msg> {
    (0..i.ns.len())
        .flat_map(|n| {
            [
                Msg { id: msg_id(K_NPRE, n) as u32, bytes: i.pre_at(n).clone() },
                Msg { id: msg_id(K_NPOST, n) as u32, bytes: i.post_at(n).clone() },
            ]
        })
        .collect()
}
