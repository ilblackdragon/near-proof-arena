//! Honest rows of the `walk`, `acct`, `sort` and `mrk` tables
//! (`ZkFormal/Near/Render/{Walk,Acct,Sort,Mrk}.lean`).

use std::collections::HashMap;

use super::ids::*;
use super::info::*;
use super::sim::leaf_bytes;
use super::spec::Bytes;

// ---------------------------------------------------------------------------
// walk
// ---------------------------------------------------------------------------

pub const WALK_WIDTH: usize = 12;

/// `walkRowsAll ws`: one segment per receipt; `u` = earlier steps with the same edge.
pub fn walk_rows_all(ws: &[Vec<WStep>]) -> Vec<Row> {
    let st: Vec<(usize, &WStep)> = ws.iter().enumerate().flat_map(|(r, w)| w.iter().map(move |s| (r, s))).collect();
    let mut seen: HashMap<&Edge, usize> = HashMap::new();
    let us: Vec<usize> = st
        .iter()
        .map(|(_, s)| {
            let c = seen.entry(&s.edge).or_insert(0);
            *c += 1;
            *c - 1
        })
        .collect();
    let h = 1usize << log_of(st.len());
    let e = |s: &WStep, j: usize| s.edge.get(j).copied().unwrap_or(0) as u64;
    mk_tab(h, WALK_WIDTH, |q, col| {
        if q >= st.len() {
            return 0;
        }
        let (r, s) = st[q];
        match col {
            0 => 1,
            1 => s.t.is_none() as u64,
            2 => s.last as u64,
            3 => r as u64,
            4 => s.t.unwrap_or(0) as u64,
            5 => s.sym as u64,
            6 => e(s, 0),
            7 => e(s, 1),
            8 => e(s, 3),
            9 => e(s, 4),
            10 => us[q] as u64,
            11 => s.t.is_some() as u64,
            _ => 0,
        }
    })
}

// ---------------------------------------------------------------------------
// acct
// ---------------------------------------------------------------------------

pub const ACCT_WIDTH: usize = 16;

fn dsum_of(v: &[u8], i: usize) -> u64 { (0..=i).map(|j| 255 - v.get(j).copied().unwrap_or(0) as u64).sum() }

/// `acctRowsAll I`: 16 rows per touched slot, padded with zero rows.
pub fn acct_rows_all(i: &Info) -> Vec<Row> {
    let nt = i.touched.len();
    let h = 1usize << log_of(16 * nt);
    let tl: Vec<u64> = i.touched.iter().map(|&k| tlast_of(&i.e, k) as u64).collect();
    mk_tab(h, ACCT_WIDTH, |q, col| {
        if q >= 16 * nt {
            return 0;
        }
        let k = i.touched[q / 16];
        let l = q % 16;
        let pre = i.vpre_at(k);
        let post = i.vpost_at(k);
        let g = |v: &Bytes, j: usize| v.get(j).copied().unwrap_or(0) as u64;
        match col {
            0 => 1,
            1 => (l == 0) as u64,
            2 => (l == 15) as u64,
            3 => k as u64,
            4 => l as u64,
            5 => tl[q / 16],
            6 => g(pre, l),
            7 => g(post, l),
            8 => g(pre, 16 + l),
            9 => if l < 8 { g(pre, 64 + l) } else { 0 },
            10 => g(pre, 32 + 2 * l),
            11 => g(pre, 33 + 2 * l),
            12 => (l < 8) as u64,
            13 => dsum_of(pre, l),
            14 => if l == 15 { inv_p(dsum_of(pre, 15)) } else { 0 },
            15 => (l < 8) as u64,
            _ => 0,
        }
    })
}

/// `acctMsgs I`: `VPRE(k)`, `VPOST(k)`.
pub fn acct_msgs(i: &Info) -> Vec<Msg> {
    i.touched
        .iter()
        .flat_map(|&k| {
            [
                Msg { id: msg_id(K_VPRE, k) as u32, bytes: i.vpre_at(k).clone() },
                Msg { id: msg_id(K_VPOST, k) as u32, bytes: i.vpost_at(k).clone() },
            ]
        })
        .collect()
}

// ---------------------------------------------------------------------------
// sort
// ---------------------------------------------------------------------------

pub const SORT_WIDTH: usize = 49;

/// Compare little-endian naturals (`leVal`).
fn le_cmp(a: &[u8], b: &[u8]) -> std::cmp::Ordering {
    let n = a.len().max(b.len());
    for j in (0..n).rev() {
        let (x, y) = (a.get(j).copied().unwrap_or(0), b.get(j).copied().unwrap_or(0));
        if x != y {
            return x.cmp(&y);
        }
    }
    std::cmp::Ordering::Equal
}

/// `sortedIds I`: `(receipt index, id)` ascending (stable on ties, as the
/// `foldr insertSorted`).
pub fn sorted_ids(i: &Info) -> Vec<(usize, Bytes)> {
    let mut v: Vec<(usize, Bytes)> = i.e.rs.iter().enumerate().map(|(r, rc)| (r, rc.receipt_id.clone())).collect();
    v.sort_by(|a, b| le_cmp(&a.1, &b.1));
    v
}

/// `x − y − 1` (truncated at 0) of little-endian naturals, as 33 bytes.
fn sub1(x: &[u8], y: &[u8]) -> Vec<u8> {
    let n = x.len().max(y.len()) + 1;
    let mut out = vec![0u8; n];
    let mut br: i32 = 1; // the "− 1"
    for j in 0..n {
        let t = x.get(j).copied().unwrap_or(0) as i32 - y.get(j).copied().unwrap_or(0) as i32 - br;
        if t < 0 {
            out[j] = (t + 256) as u8;
            br = 1;
        } else {
            out[j] = t as u8;
            br = 0;
        }
    }
    if br != 0 { vec![0u8; n] } else { out }
}

/// `sortRowsAll I`.
pub fn sort_rows_all(i: &Info) -> Vec<Row> {
    let s = sorted_ids(i);
    let ns = s.len();
    let h = 1usize << log_of(32 * ns);
    let id_of = |t: usize| -> &[u8] { s.get(t).map(|x| x.1.as_slice()).unwrap_or(&[]) };
    // diffOf t, prevOf t (bytes) and carries per segment
    let diffs: Vec<Vec<u8>> = (0..ns).map(|t| if t == 0 { vec![] } else { sub1(id_of(t), id_of(t - 1)) }).collect();
    let carries: Vec<Vec<u64>> = (0..ns)
        .map(|t| {
            (0..=33)
                .map(|ii| {
                    if t == 0 {
                        (ii == 0) as u64
                    } else {
                        // carryFrom prev diff 1 ii
                        let (x, y) = (id_of(t - 1), &diffs[t]);
                        let mut c = 1u64;
                        for j in 0..ii {
                            c = (x.get(j).copied().unwrap_or(0) as u64 + y.get(j).copied().unwrap_or(0) as u64 + c) / 256;
                        }
                        c
                    }
                })
                .collect()
        })
        .collect();
    let bb_at = |q: usize| -> u64 { if q < 32 * ns { id_of(q / 32).get(q % 32).copied().unwrap_or(0) as u64 } else { 0 } };
    mk_tab(h, SORT_WIDTH, |q, col| {
        if col >= 17 {
            return if col < 49 { bb_at((q + 2 * h - 1 - (col - 17)) % h) } else { 0 };
        }
        if q >= 32 * ns {
            return 0;
        }
        let t = q / 32;
        let l = q % 32;
        match col {
            0 => 1,
            1 => (l == 0) as u64,
            2 => (l == 31) as u64,
            3 => (t == 0) as u64,
            4 => s[t].0 as u64,
            5 => l as u64,
            6 => bb_at(q),
            7 => carries[t][l],
            8 => carries[t][l + 1],
            _ => {
                let j = col - 9;
                if j < 8 { (diffs[t].get(l).copied().unwrap_or(0) as u64 >> j) & 1 } else { 0 }
            }
        }
    })
}

// ---------------------------------------------------------------------------
// mrk
// ---------------------------------------------------------------------------

pub const MRK_WIDTH: usize = 58;
mod mc {
    pub const RT: usize = 0;
    pub const SG: usize = 1;
    pub const PR: usize = 2;
    pub const PW: usize = 3;
    pub const WN: usize = 4;
    pub const WF: usize = 5;
    pub const WL: usize = 6;
    pub const SF: usize = 7;
    pub const SL: usize = 8;
    pub const Q: usize = 9;
    pub const J: usize = 10;
    pub const I: usize = 11;
    pub const SP: usize = 12;
    pub const S: usize = 13;
    pub const ODD: usize = 14;
    pub const LIL: usize = 15;
    pub const TOP: usize = 16;
    pub const INV: usize = 17;
    pub const CID: usize = 18;
    pub const CLEN: usize = 19;
    pub const MJ: usize = 20;
    pub const MI: usize = 21;
    pub const OID: usize = 22;
    pub const OLEN: usize = 23;
    pub const GM: usize = 24;
    pub const GO: usize = 25;
    pub const REG: usize = 26;
}

/// A merkle node: SHA message id, length, digest.
#[derive(Clone, Debug, Default)]
pub struct MNode {
    pub id: usize,
    pub len: usize,
    pub dig: Bytes,
}

/// `size n j`.
fn msize(n: usize, j: usize) -> usize { (0..j).fold(n, |s, _| s.div_ceil(2)) }
/// `qBase n j`.
fn qbase(n: usize, j: usize) -> usize { if j < 2 { 0 } else { qbase(n, j - 1) + msize(n, j - 2) / 2 } }

/// `mrkShape n`: `(level, index, hashed?)` of the levels `1, 2, …`.
pub fn mrk_shape(n: usize) -> Vec<(usize, usize, bool)> {
    let mut out = vec![];
    let (mut f, mut j, mut sp) = (n + 1, 1, n);
    while f > 0 {
        let s = sp.div_ceil(2);
        out.extend((0..s).map(|i| (j, i, 2 * i + 1 < sp)));
        if s == 1 {
            break;
        }
        f -= 1;
        j += 1;
        sp = s;
    }
    out
}

/// `levels I j` for `j < n + 2`.
fn mrk_levels(i: &Info) -> Vec<Vec<MNode>> {
    let n = i.n_rcpt();
    let mut lv: Vec<Vec<MNode>> =
        vec![(0..n).map(|r| MNode { id: msg_id(K_LEAF, r), len: 68, dig: sha_n(&leaf_bytes(i, r)) }).collect()];
    for j in 0..n + 1 {
        let prev = &lv[j];
        let next = (0..prev.len().div_ceil(2))
            .map(|ii| {
                if 2 * ii + 1 < prev.len() {
                    let dig = sha_n(&[prev[2 * ii].dig.as_slice(), prev[2 * ii + 1].dig.as_slice()].concat());
                    MNode { id: msg_id(K_MRK, qbase(n, j + 1) + ii), len: 64, dig }
                } else {
                    prev[2 * ii].clone()
                }
            })
            .collect();
        lv.push(next);
    }
    lv
}

/// `mrkRowsAll I`: root row, node rows, at least one padding row.
pub fn mrk_rows_all(i: &Info) -> Vec<Row> {
    use mc::*;
    let n = i.n_rcpt();
    let lv = mrk_levels(i);
    let shape = mrk_shape(n);
    let top_j = shape.last().map(|x| x.0).unwrap_or(1);
    let recs: Vec<(usize, usize, bool, usize)> = shape
        .iter()
        .flat_map(|&(j, ii, h)| if h { (0..64).map(|p| (j, ii, true, p)).collect::<Vec<_>>() } else { vec![(j, ii, false, 0)] })
        .collect();
    let dflt = MNode::default();
    let node = |j: usize, k: usize| -> &MNode { lv.get(j).and_then(|l| l.get(k)).unwrap_or(&dflt) };
    let hh = 1usize << log_of(recs.len() + 2);
    mk_tab(hh, MRK_WIDTH, |q, col| {
        if q == 0 {
            let root = node(top_j, 0);
            return match col {
                RT | GM => 1,
                MJ => top_j as u64,
                CID => root.id as u64,
                CLEN => root.len as u64,
                _ => 0,
            };
        }
        let Some(&(j, ii, h, p)) = recs.get(q - 1) else { return 0 };
        let sp = msize(n, j - 1);
        let s = msize(n, j);
        let qq = qbase(n, j) + ii;
        let c = |k: usize| node(j - 1, k);
        let ch = if p / 32 == 0 { c(2 * ii) } else { c(2 * ii + 1) };
        match col {
            Q => qq as u64,
            J => j as u64,
            I => ii as u64,
            SP => sp as u64,
            S => s as u64,
            ODD => (sp % 2) as u64,
            LIL => (ii + 1 == s) as u64,
            TOP => (s == 1) as u64,
            INV => if s == 1 { 0 } else { inv_p((s - 1) as u64) },
            MJ => (j - 1) as u64,
            _ if h => match col {
                SG => 1,
                PW => (p % 32) as u64,
                WN => (p / 32) as u64,
                WF => (p % 32 == 0) as u64,
                WL => (p % 32 == 31) as u64,
                SF => (p == 0) as u64,
                SL => (p == 63) as u64,
                CID => ch.id as u64,
                CLEN => ch.len as u64,
                MI => (2 * ii + p / 32) as u64,
                GM => (p % 32 == 0) as u64,
                GO => (p == 0) as u64,
                OID => if p == 0 { msg_id(K_MRK, qq) as u64 } else { 0 },
                OLEN => if p == 0 { 64 } else { 0 },
                _ if (REG..REG + 32).contains(&col) => ch.dig.get(p % 32 + col - REG).copied().unwrap_or(0) as u64,
                _ => 0,
            },
            PR => 1,
            CID | OID => c(2 * ii).id as u64,
            CLEN | OLEN => c(2 * ii).len as u64,
            MI => (2 * ii) as u64,
            GM | GO => 1,
            _ => 0,
        }
    })
}

/// `mrkMsgs I`: `MRK(q)` (hashed nodes in table order).
pub fn mrk_msgs(i: &Info) -> Vec<Msg> {
    let n = i.n_rcpt();
    let lv = mrk_levels(i);
    mrk_shape(n)
        .into_iter()
        .filter(|x| x.2)
        .map(|(j, ii, _)| Msg {
            id: msg_id(K_MRK, qbase(n, j) + ii) as u32,
            bytes: [lv[j - 1][2 * ii].dig.as_slice(), lv[j - 1][2 * ii + 1].dig.as_slice()].concat(),
        })
        .collect()
}
