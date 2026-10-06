//! `prove --public <dir> --request <request.bin> --witness <witness.bin>
//!        --claim-out <claim.bin> --proof-out <proof.bin>`
//!
//! PROVER-ONLY child of `examples/reexec-v3-d0`: a native re-implementation of the
//! reference's Lean prover. It must write **byte-identical** proofs: `proof.bin` =
//! the witness file whose state witness is `ReexecV3D0.normSW K R sw`
//! (`formal/ReexecV3D0/NormBytesDefs.lean`), with the keys `K` and root `R` that
//! `ReexecV3D0.keysD0` computes. Nothing here is trusted: the verifier (unchanged,
//! formally certified) accepts a proof only if its state witness is a fixed point of
//! `normSW`, so a divergence can only make `prove` fail, never make a wrong claim pass.
//! `tests/byte_match.rs` gates this binary against the Lean prover on every public
//! positive case.
//!
//! What it mirrors, definition by definition:
//! * `keysD0`'s result only: `R` = `prev_state_root` of the shard's slot in the last
//!   new-chunk block `B2` of the claim's segment; `K` = `mainKeys receipts bshards`
//!   (`NearSpecV3.RuntimeD0`), where `bshards` comes from the `BufferedReceiptIndices`
//!   value in the partial main trie (`partialTrie … [keyBufferedIdx]`, `PTrie.find`) and
//!   `receipts` are the receipts of the receipt-proof entries (last value per key). On an
//!   accepted witness every deduplicated entry is used (`extra proofs` check) and every
//!   receipt is routed to the shard (it is bound by the merkle proof to the source chunk's
//!   outgoing receipts for that shard), so the per-block walk and the routing filter do
//!   not change the key *set*; `qFor`'s read set depends only on that set.
//! * `qFor`, `normVals`, `normPairs`, `normMain`, `normT`, `encTr`, `normSW` exactly.
//! On anything it cannot process it refuses (exit 2), as the Lean prover does.

use std::collections::HashMap;

fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    std::process::exit(2)
}

// ---------------------------------------------------------------- sha256 (FIPS 180-4)

fn sha256(data: &[u8]) -> [u8; 32] {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut msg = data.to_vec();
    let bits = (data.len() as u64).wrapping_mul(8);
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bits.to_be_bytes());
    let mut w = [0u32; 64];
    for chunk in msg.chunks(64) {
        for i in 0..16 {
            w[i] = u32::from_be_bytes(chunk[4 * i..4 * i + 4].try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (x, y) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *x = x.wrapping_add(y);
        }
    }
    let mut out = [0u8; 32];
    for i in 0..8 {
        out[4 * i..4 * i + 4].copy_from_slice(&h[i].to_be_bytes());
    }
    out
}

// ---------------------------------------------------------------- byte reader

struct R<'a> {
    b: &'a [u8],
    p: usize,
}

type Res<T> = Result<T, String>;

impl<'a> R<'a> {
    fn new(b: &'a [u8]) -> Self {
        R { b, p: 0 }
    }
    fn take(&mut self, n: usize) -> Res<&'a [u8]> {
        if self.b.len() - self.p < n {
            return Err(format!("truncated at {}", self.p));
        }
        let s = &self.b[self.p..self.p + n];
        self.p += n;
        Ok(s)
    }
    fn u8(&mut self) -> Res<u8> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> Res<u32> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Res<u64> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn bytes(&mut self) -> Res<&'a [u8]> {
        let n = self.u32()? as usize;
        self.take(n)
    }
    fn tagged(&mut self, tag: &[u8]) -> Res<()> {
        if self.bytes()? != tag {
            return Err("format tag".into());
        }
        Ok(())
    }
    /// `PublicKey` (tag ‖ data) bytes.
    fn pk(&mut self) -> Res<&'a [u8]> {
        let at = self.p;
        let n = match self.u8()? {
            0 => 32,
            1 => 64,
            2 => 1952,
            t => return Err(format!("public key tag {t}")),
        };
        self.take(n)?;
        Ok(&self.b[at..self.p])
    }
    fn signature(&mut self) -> Res<()> {
        let n = match self.u8()? {
            0 => 64,
            1 => 65,
            2 => 3309,
            t => return Err(format!("signature tag {t}")),
        };
        self.take(n).map(|_| ())
    }
    /// Tagged `ShardChunkHeaderInner` V4 (3) / V5 (4) (`NearSpecV3.pChunkInner`).
    fn chunk_inner(&mut self) -> Res<()> {
        let tag = self.u8()?;
        if tag != 3 && tag != 4 {
            return Err(format!("chunk inner version {tag}"));
        }
        self.take(4 * 32 + 5 * 8 + 16 + 2 * 32)?;
        for _ in 0..self.u32()? {
            if self.u8()? != 0 {
                return Err("ValidatorStake tag".into());
            }
            self.bytes()?;
            self.pk()?;
            self.take(16)?;
        }
        if self.u8()? != 0 {
            return Err("CongestionInfo tag".into());
        }
        self.take(42)?;
        if self.u8()? != 0 {
            return Err("BandwidthRequests tag".into());
        }
        for _ in 0..self.u32()? {
            self.take(7)?;
        }
        if tag == 4 {
            match self.u8()? {
                0 => {}
                1 => {
                    self.bytes()?;
                    self.take(16)?;
                }
                t => return Err(format!("proposed_split option tag {t}")),
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------- the state witness

struct Transition {
    block_hash: Vec<u8>,
    values: Vec<Vec<u8>>,
    post: Vec<u8>,
}

struct Receipt {
    predecessor: Vec<u8>,
    receiver: Vec<u8>,
    signer: Vec<u8>,
    signer_pk: Vec<u8>,
}

struct Entry {
    key: Vec<u8>,
    receipts: Vec<Receipt>,
    bytes: Vec<u8>,
}

struct Sw {
    head: Vec<u8>, // bytes up to and including the tagged chunk inner
    inner: Vec<u8>, // the tagged chunk inner
    main: Transition,
    entries: Vec<Entry>,
    arh_ntx: Vec<u8>, // applied_receipts_hash ‖ u32 transactions (= 0)
    implicit: Vec<Transition>,
    tail: Vec<u8>, // u32 new_transactions (= 0)
}

fn transition(r: &mut R) -> Res<Transition> {
    let block_hash = r.take(32)?.to_vec();
    if r.u8()? != 0 {
        return Err("PartialState tag".into());
    }
    let n = r.u32()?;
    let mut values = Vec::with_capacity(n.min(1 << 16) as usize);
    for _ in 0..n {
        values.push(r.bytes()?.to_vec());
    }
    let post = r.take(32)?.to_vec();
    Ok(Transition { block_hash, values, post })
}

fn receipt(r: &mut R) -> Res<Receipt> {
    let predecessor = r.bytes()?.to_vec();
    let receiver = r.bytes()?.to_vec();
    r.take(32)?;
    if r.u8()? != 0 {
        return Err("ReceiptEnum tag".into());
    }
    let signer = r.bytes()?.to_vec();
    let signer_pk = r.pk()?.to_vec();
    r.take(16)?;
    if r.u32()? != 0 || r.u32()? != 0 || r.u32()? != 1 || r.u8()? != 3 {
        return Err("receipt shape".into());
    }
    r.take(16)?;
    Ok(Receipt { predecessor, receiver, signer, signer_pk })
}

fn state_witness(sw: &[u8]) -> Res<Sw> {
    let mut r = R::new(sw);
    if r.u8()? != 1 {
        return Err("ChunkStateWitness tag".into());
    }
    r.take(32)?;
    if r.u8()? != 2 {
        return Err("ShardChunkHeader tag".into());
    }
    let inner_at = r.p;
    r.chunk_inner()?;
    let head = sw[..r.p].to_vec();
    let inner = sw[inner_at..r.p].to_vec();
    r.take(8)?;
    r.signature()?;
    let main = transition(&mut r)?;
    let mut entries = vec![];
    for _ in 0..r.u32()? {
        let at = r.p;
        let key = r.take(32)?.to_vec();
        let mut receipts = vec![];
        for _ in 0..r.u32()? {
            receipts.push(receipt(&mut r)?);
        }
        r.take(16)?;
        for _ in 0..r.u32()? {
            r.take(32)?;
            if r.u8()? > 1 {
                return Err("merkle path direction".into());
            }
        }
        entries.push(Entry { key, receipts, bytes: sw[at..r.p].to_vec() });
    }
    let arh_at = r.p;
    r.take(32)?;
    if r.u32()? != 0 {
        return Err("transactions (outside D0)".into());
    }
    let arh_ntx = sw[arh_at..r.p].to_vec();
    let mut implicit = vec![];
    for _ in 0..r.u32()? {
        implicit.push(transition(&mut r)?);
    }
    let tail_at = r.p;
    if r.u32()? != 0 {
        return Err("new_transactions (outside D0)".into());
    }
    if r.p != sw.len() {
        return Err("trailing bytes".into());
    }
    Ok(Sw { head, inner, main, entries, arh_ntx, implicit, tail: sw[tail_at..].to_vec() })
}

// ---------------------------------------------------------------- the claim (keysD0's R)

fn le_nat(b: &[u8]) -> u128 {
    b.iter().rev().fold(0u128, |a, &x| a.wrapping_mul(256) + x as u128)
}

/// `shard_id` and `prev_state_root` of a tagged chunk inner.
fn inner_fields(inner: &[u8]) -> Res<(u64, Vec<u8>)> {
    let mut r = R::new(inner);
    r.chunk_inner()?;
    if r.p != inner.len() {
        return Err("trailing bytes after chunk inner".into());
    }
    let psr = inner[33..65].to_vec();
    let sid = u64::from_le_bytes(inner[145..153].try_into().unwrap());
    Ok((sid, psr))
}

/// `slotB2.prevStateRoot`: the shard's slot in the first block (newest first) whose slot
/// for the shard is new (`height_included == height`).
fn main_root(claim: &[u8], shard_id: u64) -> Res<Vec<u8>> {
    let mut r = R::new(claim);
    r.tagged(b"near-arena-claim-v3")?;
    r.bytes()?; // statement id
    r.u32()?;
    r.bytes()?;
    r.take(32)?;
    r.bytes()?;
    let mut blocks = vec![];
    for _ in 0..r.u32()? {
        let version = r.u8()?;
        if version != 5 {
            return Err("block header is not V6".into());
        }
        r.take(32)?;
        let lite = r.bytes()?;
        r.bytes()?;
        if lite.len() < 8 {
            return Err("inner_lite".into());
        }
        let height = u64::from_le_bytes(lite[..8].try_into().unwrap());
        let mut slots = vec![];
        for _ in 0..r.u32()? {
            let inner = r.bytes()?;
            let hi = r.u64()?;
            slots.push((inner, hi));
        }
        blocks.push((height, slots));
    }
    let Some((_, slots0)) = blocks.first() else {
        return Err("empty chain segment".into());
    };
    let mut idx = None;
    for (i, (inner, _)) in slots0.iter().enumerate() {
        if inner_fields(inner)?.0 == shard_id {
            idx = Some(i);
            break;
        }
    }
    let idx = idx.ok_or("shard not in the segment's slots")?;
    for (height, slots) in &blocks {
        let (inner, hi) = slots.get(idx).ok_or("slot count")?;
        if hi == height {
            return Ok(inner_fields(inner)?.1);
        }
    }
    Err("segment has no new chunk".into())
}

// ---------------------------------------------------------------- tries (NearSpecV3.TrieBuild)

const TRIE_FUEL: usize = 400;

type Store = HashMap<[u8; 32], Vec<u8>>;

fn mk_store(values: &[Vec<u8>]) -> Store {
    let mut s = Store::new();
    for v in values {
        s.entry(sha256(v)).or_insert_with(|| v.clone());
    }
    s
}

fn store_get<'a>(s: &'a Store, h: &[u8]) -> Option<&'a Vec<u8>> {
    let k: [u8; 32] = h.try_into().ok()?;
    s.get(&k)
}

fn nibbles(b: &[u8]) -> Vec<u8> {
    b.iter().flat_map(|x| [x / 16, x % 16]).collect()
}

/// `TrieBuild.hpDecode`.
fn hp_decode(b: &[u8]) -> Option<(Vec<u8>, bool)> {
    let (&f, rest) = b.split_first()?;
    let hi = f / 16;
    let odd = hi % 2 == 1;
    let leaf = (hi / 2) % 2 == 1;
    if hi > 3 || (!odd && f % 16 != 0) {
        return None;
    }
    let mut k = if odd { vec![f % 16] } else { vec![] };
    k.extend(nibbles(rest));
    Some((k, leaf))
}

fn take(b: &[u8], n: usize) -> &[u8] {
    &b[..n.min(b.len())]
}
fn drop(b: &[u8], n: usize) -> &[u8] {
    &b[n.min(b.len())..]
}

/// `kidHashes 16 bm bs`.
fn kid_hashes(mut bm: u128, mut bs: &[u8]) -> Vec<Option<Vec<u8>>> {
    let mut out = vec![];
    for _ in 0..16 {
        if bm % 2 == 1 {
            out.push(Some(take(bs, 32).to_vec()));
            bs = drop(bs, 32);
        } else {
            out.push(None);
        }
        bm /= 2;
    }
    out
}

fn is_prefix(k: &[u8], key: &[u8]) -> bool {
    key.len() >= k.len() && &key[..k.len()] == k
}

/// The node of `h` split as (`body` tag, `body` rest), or `None` when `buildFor` would stop.
fn node_body<'a>(s: &'a Store, h: &[u8]) -> Option<&'a [u8]> {
    let node = store_get(s, h)?;
    if node.len() < 9 {
        return None;
    }
    Some(&node[..node.len() - 8])
}

/// `qBranch`.
fn q_branch(s: &Store, fuel: usize, rest: &[u8], keys: &[Vec<u8>], out: &mut Vec<Vec<u8>>) {
    let bm = le_nat(take(rest, 2));
    let hs = kid_hashes(bm, drop(rest, 2));
    let nkids = hs.iter().filter(|x| x.is_some()).count();
    if rest.len() != 2 + 32 * nkids {
        return;
    }
    for (i, ch) in hs.iter().enumerate() {
        if let Some(ch) = ch {
            let ks: Vec<Vec<u8>> = keys
                .iter()
                .filter(|k| k.first() == Some(&(i as u8)))
                .map(|k| k[1..].to_vec())
                .collect();
            q_for(s, fuel, ch, &ks, out);
        }
    }
}

/// `qFor s fuel h keys`, appended to `out`.
fn q_for(s: &Store, fuel: usize, h: &[u8], keys: &[Vec<u8>], out: &mut Vec<Vec<u8>>) {
    if fuel == 0 || keys.is_empty() {
        return;
    }
    let fuel = fuel - 1;
    out.push(h.to_vec());
    let Some(body) = node_body(s, h) else { return };
    let Some((&tag, rest)) = body.split_first() else { return };
    match tag {
        0 => {
            let klen = le_nat(take(rest, 4));
            let klen = usize::try_from(klen).unwrap_or(usize::MAX);
            if let Some((k, true)) = hp_decode(take(drop(rest, 4), klen)) {
                let r2 = drop(rest, 4usize.saturating_add(klen));
                if r2.len() == 36 && keys.iter().any(|x| *x == k) {
                    out.push(r2[4..].to_vec());
                }
            }
        }
        3 => {
            let klen = le_nat(take(rest, 4));
            let klen = usize::try_from(klen).unwrap_or(usize::MAX);
            if let Some((k, false)) = hp_decode(take(drop(rest, 4), klen)) {
                let child = drop(rest, 4usize.saturating_add(klen));
                if child.len() == 32 {
                    let ks: Vec<Vec<u8>> = keys
                        .iter()
                        .filter(|x| is_prefix(&k, x))
                        .map(|x| x[k.len()..].to_vec())
                        .collect();
                    q_for(s, fuel, child, &ks, out);
                }
            }
        }
        1 => q_branch(s, fuel, rest, keys, out),
        2 => {
            if rest.len() < 36 {
                return;
            }
            if keys.iter().any(|x| x.is_empty()) {
                out.push(rest[4..36].to_vec());
            }
            q_branch(s, fuel, &rest[36..], keys, out);
        }
        _ => {}
    }
}

/// `mkSlot` then `Slot.get`: the value if wanted, present and of the declared length.
fn slot_get(s: &Store, len: u128, vh: &[u8], want: bool) -> Option<Vec<u8>> {
    if !want {
        return None;
    }
    let v = store_get(s, vh)?;
    (v.len() as u128 == len).then(|| v.clone())
}

/// `(buildFor s fuel h [key]).find key` (`PTrie.find`): `None` = not revealed,
/// `Some(None)` = absent, `Some(Some v)` = value.
fn find(s: &Store, fuel: usize, h: &[u8], key: &[u8]) -> Option<Option<Vec<u8>>> {
    if fuel == 0 {
        return None;
    }
    let fuel = fuel - 1;
    let body = node_body(s, h)?;
    let (&tag, rest) = body.split_first()?;
    let branch = |rest: &[u8], key: &[u8]| -> Option<Option<Vec<u8>>> {
        let bm = le_nat(take(rest, 2));
        let hs = kid_hashes(bm, drop(rest, 2));
        let nkids = hs.iter().filter(|x| x.is_some()).count();
        if rest.len() != 2 + 32 * nkids {
            return None;
        }
        // key ≠ [] here
        match hs.get(key[0] as usize) {
            Some(Some(ch)) => find(s, fuel, ch, &key[1..]),
            _ => Some(None),
        }
    };
    match tag {
        0 => {
            let klen = usize::try_from(le_nat(take(rest, 4))).unwrap_or(usize::MAX);
            let (k, leaf) = hp_decode(take(drop(rest, 4), klen))?;
            if !leaf {
                return None;
            }
            let r2 = drop(rest, 4usize.saturating_add(klen));
            if r2.len() != 36 {
                return None;
            }
            if k == key {
                slot_get(s, le_nat(&r2[..4]), &r2[4..], true).map(Some)
            } else {
                Some(None)
            }
        }
        3 => {
            let klen = usize::try_from(le_nat(take(rest, 4))).unwrap_or(usize::MAX);
            let (k, leaf) = hp_decode(take(drop(rest, 4), klen))?;
            if leaf {
                return None;
            }
            let child = drop(rest, 4usize.saturating_add(klen));
            if child.len() != 32 {
                return None;
            }
            if is_prefix(&k, key) {
                find(s, fuel, child, &key[k.len()..])
            } else {
                Some(None)
            }
        }
        1 => {
            // branch without value: the empty key has no value
            let bm = le_nat(take(rest, 2));
            let hs = kid_hashes(bm, drop(rest, 2));
            let nkids = hs.iter().filter(|x| x.is_some()).count();
            if rest.len() != 2 + 32 * nkids {
                return None;
            }
            if key.is_empty() {
                Some(None)
            } else {
                branch(rest, key)
            }
        }
        2 => {
            if rest.len() < 36 {
                return None;
            }
            let r = &rest[36..];
            let bm = le_nat(take(r, 2));
            let hs = kid_hashes(bm, drop(r, 2));
            let nkids = hs.iter().filter(|x| x.is_some()).count();
            if r.len() != 2 + 32 * nkids {
                return None;
            }
            if key.is_empty() {
                slot_get(s, le_nat(&rest[..4]), &rest[4..36], true).map(Some)
            } else {
                branch(r, key)
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------- keys (RuntimeD0.mainKeys)

fn key_buffered_idx() -> Vec<u8> {
    nibbles(&[13])
}

/// `bufferedShards`.
fn buffered_shards(v: Option<Vec<u8>>) -> Res<Vec<u64>> {
    let Some(b) = v else { return Ok(vec![]) };
    let mut r = R::new(&b);
    let mut out = vec![];
    for _ in 0..r.u32()? {
        let s = r.u64()?;
        let f = r.u64()?;
        let n = r.u64()?;
        if f != n {
            return Err("outgoing buffer not empty (outside D0)".into());
        }
        out.push(s);
    }
    if r.p != b.len() {
        return Err("BufferedReceiptIndices trailing bytes".into());
    }
    Ok(out)
}

/// The receipt-proof entries in normal form (`normPairs`): last value per key, keys
/// increasing (`bytesLe` = lexicographic order of byte strings).
fn norm_entries(es: &[Entry]) -> Vec<&Entry> {
    let mut out: Vec<&Entry> = vec![];
    for (i, e) in es.iter().enumerate() {
        if !es[i + 1..].iter().any(|x| x.key == e.key) {
            out.push(e);
        }
    }
    out.sort_by(|a, b| a.key.cmp(&b.key));
    out
}

fn main_keys(entries: &[&Entry], bshards: &[u64]) -> Vec<Vec<u8>> {
    let mut k = vec![nibbles(&[7]), nibbles(&[15]), nibbles(&[13]), nibbles(&[10])];
    for s in bshards {
        let mut b = vec![16u8];
        b.extend_from_slice(&s.to_le_bytes());
        k.push(nibbles(&b));
    }
    let receipts: Vec<&Receipt> = entries.iter().flat_map(|e| e.receipts.iter()).collect();
    for r in &receipts {
        let mut b = vec![0u8];
        b.extend_from_slice(&r.receiver);
        k.push(nibbles(&b));
    }
    for r in &receipts {
        if r.predecessor == b"system" && r.signer == r.receiver {
            let mut b = vec![2u8];
            b.extend_from_slice(&r.receiver);
            b.push(2);
            b.extend_from_slice(&r.signer_pk);
            k.push(nibbles(&b));
        }
    }
    k
}

// ---------------------------------------------------------------- normal form

/// `normVals values q`: the found values, deduplicated, in byte order.
fn norm_vals(values: &[Vec<u8>], q: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let s = mk_store(values);
    let mut vs: Vec<Vec<u8>> = q.iter().filter_map(|h| store_get(&s, h).cloned()).collect();
    vs.sort();
    vs.dedup();
    vs
}

fn enc_tr(values: &[Vec<u8>], post: &[u8], out: &mut Vec<u8>) {
    out.extend_from_slice(&[0u8; 32]);
    out.push(0);
    out.extend_from_slice(&(values.len() as u32).to_le_bytes());
    for v in values {
        out.extend_from_slice(&(v.len() as u32).to_le_bytes());
        out.extend_from_slice(v);
    }
    out.extend_from_slice(post);
}

fn normal_proof(claim: &[u8], witness: &[u8]) -> Res<Vec<u8>> {
    let mut f = R::new(witness);
    f.tagged(b"near-arena-witness-v3")?;
    let sw = f.bytes()?;
    if f.u32()? != 0 || f.p != witness.len() {
        return Err("contract code or trailing bytes (outside D0)".into());
    }
    let w = state_witness(sw)?;
    let (shard_id, _) = inner_fields(&w.inner)?;
    let root = main_root(claim, shard_id)?;
    // keysD0: BufferedReceiptIndices in the main trie, then mainKeys
    let store = mk_store(&w.main.values);
    let bv = find(&store, TRIE_FUEL, &root, &key_buffered_idx())
        .ok_or("MissingTrieValue (BufferedReceiptIndices)")?;
    let bshards = buffered_shards(bv)?;
    let entries = norm_entries(&w.entries);
    let keys = main_keys(&entries, &bshards);
    // normMain
    let mut q = vec![];
    q_for(&store, TRIE_FUEL, &root, &[key_buffered_idx()], &mut q);
    q_for(&store, TRIE_FUEL, &root, &keys, &mut q);
    let main_vals = norm_vals(&w.main.values, &q);
    // normSW
    let mut out = w.head.clone();
    out.extend_from_slice(&[0u8; 8]);
    out.push(0);
    out.extend_from_slice(&[0u8; 64]);
    enc_tr(&main_vals, &w.main.post, &mut out);
    out.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    for e in &entries {
        out.extend_from_slice(&e.bytes);
    }
    out.extend_from_slice(&w.arh_ntx);
    out.extend_from_slice(&(w.implicit.len() as u32).to_le_bytes());
    let mut r = w.main.post.clone();
    for t in &w.implicit {
        let s = mk_store(&t.values);
        let mut q = vec![];
        q_for(&s, TRIE_FUEL, &r, &[nibbles(&[7]), nibbles(&[15])], &mut q);
        enc_tr(&norm_vals(&t.values, &q), &t.post, &mut out);
        r = t.post.clone();
    }
    out.extend_from_slice(&w.tail);
    let _ = &w.main.block_hash;
    // wrapW
    let tag = b"near-arena-witness-v3";
    let mut file = Vec::with_capacity(out.len() + 33);
    file.extend_from_slice(&(tag.len() as u32).to_le_bytes());
    file.extend_from_slice(tag);
    file.extend_from_slice(&(out.len() as u32).to_le_bytes());
    file.extend_from_slice(&out);
    file.extend_from_slice(&0u32.to_le_bytes());
    Ok(file)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |name: &str| -> String {
        let i = args
            .iter()
            .position(|a| a == &format!("--{name}"))
            .unwrap_or_else(|| die(&format!("missing --{name}")));
        args.get(i + 1).cloned().unwrap_or_else(|| die(&format!("--{name} needs a value")))
    };
    let (_public, request, witness, claim_out, proof_out) =
        (get("public"), get("request"), get("witness"), get("claim-out"), get("proof-out"));
    if args.len() != 10 {
        die("usage: prove --public DIR --request FILE --witness FILE --claim-out FILE --proof-out FILE");
    }
    let claim = std::fs::read(&request).unwrap_or_else(|e| die(&format!("request: {e}")));
    let wit = std::fs::read(&witness).unwrap_or_else(|e| die(&format!("witness: {e}")));
    let proof = normal_proof(&claim, &wit).unwrap_or_else(|e| die(&e));
    std::fs::write(&claim_out, &claim).unwrap_or_else(|e| die(&format!("claim-out: {e}")));
    std::fs::write(&proof_out, &proof).unwrap_or_else(|e| die(&format!("proof-out: {e}")));
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sha256_vectors() {
        let hex = |b: [u8; 32]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        assert_eq!(
            hex(sha256(b"")),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hex(sha256(b"abc")),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        let m = vec![b'a'; 1000];
        assert_eq!(
            hex(sha256(&m)),
            "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
        );
    }
}
