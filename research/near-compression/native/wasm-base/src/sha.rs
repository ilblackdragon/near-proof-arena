//! SHA-256 trace generation for the `SHA256` table of `wasmBaseHashAir` (`WasmBase/ShaAir.lean`).
//!
//! The rows are exactly `ZkFormal.Sha.Gen`'s: one start row per message, then per padded block
//! sixteen round rows `R0..R15` and one digest row `D`.  Column values are computed with the same
//! formulas as `ZkFormal.Sha.Gen` (`roundCell`, `digestCell`, `startCell`), mirrored here in Rust
//! because the prover needs the numbers, not a Lean term.  The *constraints* are not mirrored: they
//! are the Lean export, interpreted by `src/air.rs`.
//!
//! Layout: `ZkFormal.Sha.Layout` (544 columns) + the five message columns of `Chips.Sha`
//! (`sh_ts`, `sh_tp`, `sh_hid`, `sh_rin`, `sh_len`).

pub const WIDTH: usize = 544;
pub const SH_TS: usize = WIDTH;
pub const SH_TP: usize = WIDTH + 1;
pub const SH_HID: usize = WIDTH + 2;
pub const SH_RIN: usize = WIDTH + 3;
pub const SH_LEN: usize = WIDTH + 4;
pub const NCOLS: usize = WIDTH + 5;

pub fn col_a(i: usize, b: usize) -> usize { 32 * i + b }
pub fn col_e(i: usize, b: usize) -> usize { 128 + 32 * i + b }
pub fn col_w(i: usize, b: usize) -> usize { 256 + 32 * i + b }
pub fn col_ca(i: usize, l: usize, k: usize) -> usize { 384 + 6 * i + 3 * l + k }
pub fn col_ce(i: usize, l: usize, k: usize) -> usize { 408 + 6 * i + 3 * l + k }
pub fn col_cw(i: usize, l: usize, k: usize) -> usize { 432 + 6 * i + 3 * l + k }
pub fn col_i4(i: usize, l: usize) -> usize { 456 + 2 * i + l }
pub fn col_i8(i: usize, l: usize) -> usize { 464 + 2 * i + l }
pub fn col_i12(i: usize, l: usize) -> usize { 472 + 2 * i + l }
pub fn col_w3(i: usize, l: usize) -> usize { 480 + 2 * i + l }
pub fn col_hin(w: usize, l: usize) -> usize { 486 + 2 * w + l }
pub fn col_r(j: usize) -> usize { 502 + j }
pub const COL_D: usize = 518;
pub const COL_S: usize = 519;
pub fn col_f(k: usize) -> usize { 520 + k }
pub const COL_FPREV: usize = 536;
pub const COL_ND: usize = 537;
pub const COL_ID: usize = 538;
pub const COL_LAST: usize = 539;
pub const COL_P80: usize = 540;
pub const COL_SEEN: usize = 541;
pub const COL_PN: usize = 542;
pub const COL_DMULT: usize = 543;

pub fn col_st(w: usize, b: usize) -> usize {
    if w < 4 { col_a(3 - w, b) } else { col_e(7 - w, b) }
}
pub fn col_cst(w: usize, l: usize, k: usize) -> usize {
    if w < 4 { col_ca(3 - w, l, k) } else { col_ce(7 - w, l, k) }
}

pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];
pub const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

fn rotr(x: u32, r: u32) -> u32 { x.rotate_right(r) }
fn bsig0(x: u32) -> u32 { rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22) }
fn bsig1(x: u32) -> u32 { rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25) }
fn ssig0(x: u32) -> u32 { rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3) }
fn ssig1(x: u32) -> u32 { rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10) }
fn chf(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ (!x & z) }
fn majf(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ (x & z) ^ (y & z) }

fn lo16(x: u64) -> u64 { x % 65536 }
fn hi16(x: u64) -> u64 { x / 65536 }
fn limb_n(x: u64, l: usize) -> u64 { if l == 0 { lo16(x) } else { hi16(x) } }
fn carry(xs: &[u64], l: usize) -> u64 {
    let c0 = xs.iter().map(|&x| lo16(x)).sum::<u64>() / 65536;
    if l == 0 { c0 } else { (xs.iter().map(|&x| hi16(x)).sum::<u64>() + c0) / 65536 }
}

/// `ZkFormal.Sha.Gen.pad`: `m ‖ 0x80 ‖ 0… ‖ be64(8·len)`, a multiple of 64 bytes.
pub fn pad(m: &[u8]) -> Vec<u8> {
    let mut p = m.to_vec();
    p.push(0x80);
    while p.len() % 64 != 56 {
        p.push(0);
    }
    p.extend_from_slice(&((m.len() as u64) * 8).to_be_bytes());
    p
}

/// One message of the table: its register id, its bytes, and whether the digest is announced.
#[derive(Clone, Debug)]
pub struct Msg {
    pub id: u64,
    pub bytes: Vec<u8>,
    pub dmult: bool,
}

struct Blk {
    id: u64,
    len: usize,
    idx: usize,
    nblk: usize,
    hin: [u32; 8],
    dmult: u64,
    a: [u32; 68],
    e: [u32; 68],
    w: [u32; 64],
}

impl Blk {
    fn new(id: u64, len: usize, idx: usize, nblk: usize, hin: [u32; 8], blk: &[u8], dmult: u64) -> Blk {
        let mut w = [0u32; 64];
        for t in 0..16 {
            w[t] = u32::from_be_bytes(blk[4 * t..4 * t + 4].try_into().unwrap());
        }
        for t in 16..64 {
            w[t] = ssig1(w[t - 2])
                .wrapping_add(w[t - 7])
                .wrapping_add(ssig0(w[t - 15]))
                .wrapping_add(w[t - 16]);
        }
        let mut a = [0u32; 68];
        let mut e = [0u32; 68];
        a[..4].copy_from_slice(&[hin[3], hin[2], hin[1], hin[0]]);
        e[..4].copy_from_slice(&[hin[7], hin[6], hin[5], hin[4]]);
        for t in 0..64 {
            let t1 = e[t]
                .wrapping_add(bsig1(e[t + 3]))
                .wrapping_add(chf(e[t + 3], e[t + 2], e[t + 1]))
                .wrapping_add(K[t])
                .wrapping_add(w[t]);
            let t2 = bsig0(a[t + 3]).wrapping_add(majf(a[t + 3], a[t + 2], a[t + 1]));
            a[t + 4] = t1.wrapping_add(t2);
            e[t + 4] = a[t].wrapping_add(t1);
        }
        Blk { id, len, idx, nblk, hin, dmult, a, e, w }
    }
    fn is_data(&self, kk: usize) -> bool { 64 * self.idx + kk < self.len }
    fn last(&self) -> bool { self.idx + 1 == self.nblk }
    fn p80(&self) -> bool { 64 * self.idx <= self.len && self.len < 64 * self.idx + 64 }
    fn seen(&self) -> bool { self.len < 64 * self.idx }
    fn terms_a(&self, t: usize) -> [u64; 7] {
        let (a, e) = (&self.a, &self.e);
        [
            e[t],
            bsig1(e[t + 3]),
            chf(e[t + 3], e[t + 2], e[t + 1]),
            K[t],
            self.w[t],
            bsig0(a[t + 3]),
            majf(a[t + 3], a[t + 2], a[t + 1]),
        ]
        .map(|x| x as u64)
    }
    fn terms_e(&self, t: usize) -> [u64; 6] {
        let (a, e) = (&self.a, &self.e);
        [a[t], e[t], bsig1(e[t + 3]), chf(e[t + 3], e[t + 2], e[t + 1]), K[t], self.w[t]].map(|x| x as u64)
    }
    fn help(&self, m: usize, l: usize) -> u64 {
        limb_n(ssig0(self.w[m + 1]) as u64, l) + limb_n(self.w[m] as u64, l)
    }
    fn sched_carry(&self, t: usize, l: usize) -> u64 {
        let s1 = ssig1(self.w[t - 2]) as u64;
        let w7 = self.w[t - 7] as u64;
        let c0 = (lo16(s1) + lo16(w7) + self.help(t - 16, 0)) / 65536;
        if l == 0 { c0 } else { (hi16(s1) + hi16(w7) + self.help(t - 16, 1) + c0) / 65536 }
    }
    fn fin(&self, w: usize) -> u32 { if w < 4 { self.a[67 - w] } else { self.e[71 - w] } }
    fn hout(&self, w: usize) -> u32 { self.hin[w].wrapping_add(self.fin(w)) }
    fn nd_row(&self, j: usize) -> u64 { self.len.min(64 * self.idx + 16 * (j.min(3) + 1)) as u64 }
    fn framing(&self, row: &mut [u64]) {
        row[COL_ID] = self.id;
        row[COL_LAST] = self.last() as u64;
        row[COL_P80] = self.p80() as u64;
        row[COL_SEEN] = self.seen() as u64;
        row[COL_PN] = (self.p80() && !self.last()) as u64;
    }
    fn round_row(&self, j: usize, row: &mut [u64]) {
        let t0 = 4 * j;
        let bit = |x: u64, b: usize| (x >> b) & 1;
        for i in 0..4 {
            for b in 0..32 {
                row[col_a(i, b)] = bit(self.a[t0 + 4 + i] as u64, b);
                row[col_e(i, b)] = bit(self.e[t0 + 4 + i] as u64, b);
                row[col_w(i, b)] = bit(self.w[t0 + i] as u64, b);
            }
            for l in 0..2 {
                let ca = carry(&self.terms_a(t0 + i), l);
                let ce = carry(&self.terms_e(t0 + i), l);
                let cw = if j >= 4 { self.sched_carry(t0 + i, l) } else { 0 };
                for kk in 0..3 {
                    row[col_ca(i, l, kk)] = bit(ca, kk);
                    row[col_ce(i, l, kk)] = bit(ce, kk);
                    row[col_cw(i, l, kk)] = bit(cw, kk);
                }
                for (d, col) in [(1, col_i4(i, l)), (2, col_i8(i, l)), (3, col_i12(i, l))] {
                    row[col] = if d <= j { self.help(4 * (j - d) + i, l) } else { 0 };
                }
                if i < 3 {
                    row[col_w3(i, l)] = if j >= 1 { limb_n(self.w[4 * (j - 1) + i + 1] as u64, l) } else { 0 };
                }
            }
        }
        for w in 0..8 {
            for l in 0..2 {
                row[col_hin(w, l)] = limb_n(self.hin[w] as u64, l);
            }
        }
        row[col_r(j)] = 1;
        for q in 0..16 {
            row[col_f(q)] = (j < 4 && self.is_data(16 * j + q)) as u64;
        }
        row[COL_FPREV] = if j == 0 { 1 } else { (j < 4 && self.is_data(16 * j - 1)) as u64 };
        row[COL_ND] = self.nd_row(j);
        self.framing(row);
    }
    fn digest_row(&self, row: &mut [u64]) {
        for w in 0..8 {
            let h = self.hout(w) as u64;
            for b in 0..32 {
                row[col_st(w, b)] = (h >> b) & 1;
            }
            for l in 0..2 {
                let cv = carry(&[self.hin[w] as u64, self.fin(w) as u64], l);
                for kk in 0..3 {
                    row[col_cst(w, l, kk)] = (cv >> kk) & 1;
                }
            }
        }
        row[COL_D] = 1;
        row[COL_ND] = self.nd_row(4);
        self.framing(row);
        row[COL_DMULT] = if self.last() { self.dmult } else { 0 };
    }
}

fn start_row(id: u64, row: &mut [u64]) {
    for w in 0..8 {
        for b in 0..32 {
            row[col_st(w, b)] = ((H0[w] >> b) & 1) as u64;
        }
    }
    row[COL_S] = 1;
    row[COL_ID] = id;
}

enum RowDesc {
    Start(u64),
    Round(usize, usize),
    Digest(usize),
}

/// The rows of the table, in message order, with the message-level columns
/// (`sh_ts`, `sh_tp`, `sh_hid`, `sh_rin`, `sh_len`) attached to every row of a message.
pub struct ShaRows {
    pub rows: Vec<[u64; NCOLS]>,
    /// the number of live rows (the rest of the power-of-two height is padding)
    pub live: usize,
}

/// Build the SHA rows.  `ts` is the Wasm clock of the call; `tp` the producer time of the input
/// register's bytes; `hid` the host id; `rin` the input register (`ptr`); `len` the byte length.
pub fn rows(msgs: &[Msg], ts: u64, tp: u64, hid: u64, rin: u64, len: u64) -> ShaRows {
    let mut blks: Vec<Blk> = vec![];
    let mut descs: Vec<RowDesc> = vec![];
    for m in msgs {
        let p = pad(&m.bytes);
        let nblk = p.len() / 64;
        descs.push(RowDesc::Start(m.id));
        let mut h = H0;
        for b in 0..nblk {
            let blk = Blk::new(m.id, m.bytes.len(), b, nblk, h, &p[64 * b..64 * b + 64], m.dmult as u64);
            for (w, hw) in h.iter_mut().enumerate() {
                *hw = blk.hout(w);
            }
            for j in 0..16 {
                descs.push(RowDesc::Round(j, blks.len()));
            }
            descs.push(RowDesc::Digest(blks.len()));
            blks.push(blk);
        }
    }
    let live = descs.len();
    let mut rows: Vec<[u64; NCOLS]> = descs
        .iter()
        .map(|d| {
            let mut row = [0u64; NCOLS];
            match *d {
                RowDesc::Start(id) => start_row(id, &mut row),
                RowDesc::Round(j, b) => blks[b].round_row(j, &mut row),
                RowDesc::Digest(b) => blks[b].digest_row(&mut row),
            }
            row[SH_TS] = ts;
            row[SH_TP] = tp;
            row[SH_HID] = hid;
            row[SH_RIN] = rin;
            row[SH_LEN] = len;
            row
        })
        .collect();
    // padding: all-zero rows (`Gen.Row.pad`); the message columns are 0 too, so `cConst` holds
    let h = live.max(4).next_power_of_two();
    rows.resize(h, [0u64; NCOLS]);
    ShaRows { rows, live }
}

/// The 32 digest bytes of a message (for the differential test against `sha2`).
pub fn digest_bytes(m: &[u8]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let d = Sha256::digest(m);
    let mut out = [0u8; 32];
    out.copy_from_slice(&d);
    out
}

/// The digest bytes a digest row carries, read back through the AIR's own layout
/// (`col_st w b` = bit `b` of word `w`, big-endian bytes).  This is the value the AIR proves on
/// that row, not a re-computation: the cells come from the trace, the byte order from the layout.
pub fn digest_of_row(row: &[u64; NCOLS]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for p in 0..32 {
        let w = p / 4;
        let q = p % 4;
        let mut v = 0u64;
        for b in 0..32 {
            v |= row[col_st(w, b)] << b;
        }
        out[p] = ((v >> (8 * (3 - q))) & 0xff) as u8;
    }
    out
}

/// The last digest row of a message's rows (the row `dmult = 1` sits on).
pub fn last_digest_row(rows: &[[u64; NCOLS]]) -> Option<&[u64; NCOLS]> {
    rows.iter().rev().find(|r| r[COL_DMULT] == 1 && r[COL_D] == 1)
}

/// The message bytes the rows of one message consume, read back from the `W` columns and the data
/// flags: byte `q` of round row `Rj` is data iff `F q = 1`, and its value is the big-endian byte of
/// `W_{4j+q}`.  Independent of the generator's `Msg` (it reads the cells).
pub fn message_of_rows(rows: &[[u64; NCOLS]]) -> Vec<u8> {
    let mut out = vec![];
    // rows[0] is the start row; then blocks of `R0..R15, D`, so a block starts at `1 + 17*b`
    let mut b = 0usize;
    while 1 + 17 * b + 16 < rows.len() && rows[1 + 17 * b][col_r(0)] == 1 {
        for j in 0..16 {
            let row = &rows[1 + 17 * b + j];
            for q in 0..16 {
                if row[col_f(q)] == 1 {
                    let mut v = 0u64;
                    for bit in 0..32 {
                        v |= row[col_w(q / 4, bit)] << bit;
                    }
                    out.push(((v >> (8 * (3 - q % 4))) & 0xff) as u8);
                }
            }
        }
        b += 1;
    }
    out
}

// ---------------------------------------------------------------------------
// The spec's observed `sha256` calls, for the differential test
// ---------------------------------------------------------------------------

/// The input bytes of every `sha256` call the spec made, in call order, read from a `prep.json`
/// (the `hosts` events' `args` and the post-call register file).
pub fn spec_vectors(prep_path: &str) -> Vec<Vec<u8>> {
    let text = std::fs::read_to_string(prep_path).expect("prep json");
    let v: serde_json::Value = serde_json::from_str(&text).expect("prep json");
    let mut out = vec![];
    for h in v["hosts"].as_array().map(|a| a.as_slice()).unwrap_or(&[]) {
        if h["hid"].as_u64() != Some(53) {
            continue;
        }
        let args: Vec<u64> = h["args"].as_array().unwrap().iter().map(|x| x.as_u64().unwrap()).collect();
        let (len, ptr) = (args[0], args[1]);
        let regs: Vec<(u64, Vec<u8>)> = h["regs"]
            .as_array()
            .map(|a| {
                a.iter()
                    .map(|e| {
                        (
                            e[0].as_u64().unwrap(),
                            e[1].as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as u8).collect(),
                        )
                    })
                    .collect()
            })
            .unwrap_or_default();
        if len == u64::MAX {
            out.push(regs.iter().find(|(r, _)| *r == ptr).map(|(_, b)| b.clone()).unwrap_or_default());
        } else {
            // the memory branch: the bytes are the initial image at `[ptr, ptr + len)`, which the
            // prep carries as `data` (the data segment) padded with zeros up to `dataEnd`
            let data: Vec<u8> = v["data"]
                .as_array()
                .map(|a| a.iter().map(|x| x.as_u64().unwrap() as u8).collect())
                .unwrap_or_default();
            out.push(
                (0..len)
                    .map(|j| *data.get((ptr + j) as usize).unwrap_or(&0))
                    .collect(),
            );
        }
    }
    out
}

/// The digest of every `sha256` call the spec made, in call order (the `regs` entry the call
/// filled with register id `args[2]`).
pub fn spec_events(prep_path: &str) -> Vec<[u8; 32]> {
    let text = std::fs::read_to_string(prep_path).expect("prep json");
    let v: serde_json::Value = serde_json::from_str(&text).expect("prep json");
    let mut out = vec![];
    for h in v["hosts"].as_array().map(|a| a.as_slice()).unwrap_or(&[]) {
        if h["hid"].as_u64() != Some(53) {
            continue;
        }
        let args: Vec<u64> = h["args"].as_array().unwrap().iter().map(|x| x.as_u64().unwrap()).collect();
        let reg = args[2];
        let mut dg = [0u8; 32];
        if let Some(a) = h["regs"].as_array() {
            if let Some(e) = a.iter().find(|e| e[0].as_u64() == Some(reg)) {
                for (k, x) in e[1].as_array().unwrap().iter().enumerate().take(32) {
                    dg[k] = x.as_u64().unwrap() as u8;
                }
            }
        }
        out.push(dg);
    }
    out
}
