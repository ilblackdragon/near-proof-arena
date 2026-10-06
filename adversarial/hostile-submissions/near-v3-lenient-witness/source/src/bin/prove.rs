//! `prove --public <dir> --request <request.bin> --witness <witness.bin>
//!        --claim-out <claim.bin> --proof-out <proof.bin>`
//!
//! `near/pv86/chunk-validation/v0` has no request file: the request IS the
//! claim (`near-arena-claim-v3`), so `claim.bin` = `request.bin`.
//!
//! The proof is the witness in **canonical form** (`formal/ReexecV3D0/CanonDefs.lean`):
//! the three fields nearcore's validator never reads are overwritten with fixed
//! values — the chunk header's `height_included` (0), its signature (ED25519, 64
//! zero bytes) and every `ChunkStateTransition.block_hash` (32 zero bytes). The
//! verifier accepts only canonical proofs and decides `RelD0 claim proof`
//! (`formal/ReexecV3D0/Model.lean`); the certificate proves that canonicalising a
//! valid witness keeps it valid (`Canon.lean`, `relD0_canonical`).
//!
//! The prover does not decide the relation. A witness whose layout it cannot walk
//! (not `ChunkStateWitness::V2`, a non-D0 receipt or inner shape, transactions)
//! is refused (exit 2); otherwise it emits the canonical bytes, which the
//! verifier rejects if the claim is false or out of domain.

fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    std::process::exit(2)
}

struct R<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> R<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        if self.b.len() - self.p < n {
            return Err(format!("truncated at {}", self.p));
        }
        let s = &self.b[self.p..self.p + n];
        self.p += n;
        Ok(s)
    }
    fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn bytes(&mut self) -> Result<&'a [u8], String> {
        let n = self.u32()? as usize;
        self.take(n)
    }
    fn public_key(&mut self) -> Result<(), String> {
        match self.u8()? {
            0 => self.take(32).map(|_| ()),
            1 => self.take(64).map(|_| ()),
            2 => self.take(1952).map(|_| ()),
            t => Err(format!("unknown public key tag {t}")),
        }
    }
    fn signature(&mut self) -> Result<(), String> {
        match self.u8()? {
            0 => self.take(64).map(|_| ()),
            1 => self.take(65).map(|_| ()),
            2 => self.take(3309).map(|_| ()),
            t => Err(format!("unknown signature tag {t}")),
        }
    }
    /// Tagged `ShardChunkHeaderInner` V4 (3) / V5 (4) (`NearSpecV3.pChunkInner`).
    fn chunk_inner(&mut self) -> Result<(), String> {
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
            self.public_key()?;
            self.take(16)?;
        }
        if self.u8()? != 0 {
            return Err("CongestionInfo tag".into());
        }
        self.take(16 + 16 + 8 + 2)?;
        if self.u8()? != 0 {
            return Err("BandwidthRequests tag".into());
        }
        for _ in 0..self.u32()? {
            self.take(2 + 5)?;
        }
        if tag == 4 {
            match self.u8()? {
                0 => {}
                1 => {
                    self.bytes()?;
                    self.take(16)?;
                }
                t => return Err(format!("option tag {t}")),
            }
        }
        Ok(())
    }
    /// D0 receipt shape (`NearSpecV3.pReceipt`).
    fn receipt(&mut self) -> Result<(), String> {
        self.bytes()?;
        self.bytes()?;
        self.take(32)?;
        if self.u8()? != 0 {
            return Err("receipt is not Action".into());
        }
        self.bytes()?;
        self.public_key()?;
        self.take(16)?;
        if self.u32()? != 0 || self.u32()? != 0 || self.u32()? != 1 || self.u8()? != 3 {
            return Err("receipt is not a single Transfer".into());
        }
        self.take(16).map(|_| ())
    }
    /// A `ChunkStateTransition`; returns the offset of its `block_hash`.
    fn transition(&mut self) -> Result<usize, String> {
        let at = self.p;
        self.take(32)?;
        if self.u8()? != 0 {
            return Err("PartialState tag".into());
        }
        for _ in 0..self.u32()? {
            self.bytes()?;
        }
        self.take(32)?;
        Ok(at)
    }
}

/// Byte ranges of the validator-ignored fields of a `ChunkStateWitness::V2`
/// (offsets into the state-witness bytes) and the signature range to replace.
struct Ignored {
    height: usize,
    sig: (usize, usize),
    block_hashes: Vec<usize>,
}

fn walk(sw: &[u8]) -> Result<Ignored, String> {
    let mut r = R { b: sw, p: 0 };
    if r.u8()? != 1 {
        return Err("not ChunkStateWitness::V2".into());
    }
    r.take(32)?; // epoch_id
    if r.u8()? != 2 {
        return Err("chunk header is not V3".into());
    }
    r.chunk_inner()?;
    let height = r.p;
    r.take(8)?;
    let s0 = r.p;
    r.signature()?;
    let sig = (s0, r.p);
    let mut block_hashes = vec![r.transition()?];
    for _ in 0..r.u32()? {
        r.take(32)?;
        for _ in 0..r.u32()? {
            r.receipt()?;
        }
        r.take(16)?;
        for _ in 0..r.u32()? {
            r.take(33)?;
        }
    }
    r.take(32)?; // applied_receipts_hash
    if r.u32()? != 0 {
        return Err("transactions present (outside D0)".into());
    }
    for _ in 0..r.u32()? {
        block_hashes.push(r.transition()?);
    }
    if r.u32()? != 0 {
        return Err("new_transactions present (outside D0)".into());
    }
    if r.p != sw.len() {
        return Err("trailing bytes".into());
    }
    Ok(Ignored { height, sig, block_hashes })
}

/// The canonical witness file (`ReexecV3D0.wrapW` of the canonical state witness).
fn canonical(witness: &[u8]) -> Result<Vec<u8>, String> {
    let tag = b"near-arena-witness-v3";
    let mut r = R { b: witness, p: 0 };
    if r.bytes()? != tag {
        return Err("not a near-arena-witness-v3 file".into());
    }
    let sw = r.bytes()?;
    if r.u32()? != 0 || r.p != witness.len() {
        return Err("contract code or trailing bytes (outside D0)".into());
    }
    let ig = walk(sw)?;
    let mut out = sw[..ig.height].to_vec();
    out.extend_from_slice(&[0u8; 8]);
    out.push(0); // ED25519
    out.extend_from_slice(&[0u8; 64]);
    out.extend_from_slice(&sw[ig.sig.1..]);
    // block hashes after the signature shift by the signature length change
    let shift = (ig.sig.1 - ig.sig.0) as isize - 65;
    for at in ig.block_hashes {
        let at = (at as isize - shift) as usize;
        out[at..at + 32].fill(0);
    }
    let mut f = Vec::with_capacity(out.len() + 33);
    f.extend_from_slice(&(tag.len() as u32).to_le_bytes());
    f.extend_from_slice(tag);
    f.extend_from_slice(&(out.len() as u32).to_le_bytes());
    f.extend_from_slice(&out);
    f.extend_from_slice(&0u32.to_le_bytes());
    Ok(f)
}

fn tagged(b: &[u8], tag: &[u8]) -> bool {
    b.len() >= 4 + tag.len()
        && u32::from_le_bytes([b[0], b[1], b[2], b[3]]) as usize == tag.len()
        && &b[4..4 + tag.len()] == tag
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
    if !tagged(&claim, b"near-arena-claim-v3") {
        die("request: not a near-arena-claim-v3 claim");
    }
    let proof = canonical(&wit).unwrap_or_else(|e| die(&format!("witness: {e}")));
    std::fs::write(&claim_out, &claim).unwrap_or_else(|e| die(&format!("claim-out: {e}")));
    std::fs::write(&proof_out, &proof).unwrap_or_else(|e| die(&format!("proof-out: {e}")));
}
