//! `prepare --params <approved_params.bin> --out <public_dir>`
//!
//! Validates the approved parameters (`spec/claim-v1.md` §5) and writes them
//! unchanged as `public_dir/public.bin`, the single public tape whose SHA-256
//! is `publicDigest` in the admission statement. The verifier ignores it (the
//! relation fixes every parameter), so it carries no trust.
//!
//! Self-contained (std only, no dependency on the prover library) so that
//! prover-only changes can never change this artifact.

fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    std::process::exit(2)
}

fn take<'a>(b: &mut &'a [u8], n: usize) -> Option<&'a [u8]> {
    if b.len() < n {
        return None;
    }
    let (h, t) = b.split_at(n);
    *b = t;
    Some(h)
}

fn bytes<'a>(b: &mut &'a [u8]) -> Option<&'a [u8]> {
    let n = u32::from_le_bytes(take(b, 4)?.try_into().ok()?) as usize;
    take(b, n)
}

fn valid(mut b: &[u8]) -> bool {
    (|| {
        let ok = bytes(&mut b)? == b"near-arena-params-v1"
            && bytes(&mut b)? == b"near/pv86/receipt-transfer-batch/v0"
            && take(&mut b, 4)? == 86u32.to_le_bytes()
            && bytes(&mut b)? == b"mainnet";
        take(&mut b, 32)?;
        Some(ok && b.is_empty())
    })()
    .unwrap_or(false)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (params, out) = match args.as_slice() {
        [a, p, b, o] if a == "--params" && b == "--out" => (p, o),
        [b, o, a, p] if a == "--params" && b == "--out" => (p, o),
        _ => die("usage: prepare --params <params.bin> --out <public_dir>"),
    };
    let bytes = std::fs::read(params).unwrap_or_else(|e| die(&format!("params: {e}")));
    if !valid(&bytes) {
        die("params: not near-arena-params-v1 for near/pv86/receipt-transfer-batch/v0 (pv 86, mainnet)");
    }
    let out = std::path::Path::new(out);
    std::fs::create_dir_all(out).unwrap_or_else(|e| die(&format!("out: {e}")));
    // ATTACK: deploy a key for protocol version 85 (the certificate covers pv 86).
    let mut bytes = bytes;
    bytes[63] = 85;
    std::fs::write(out.join("public.bin"), &bytes).unwrap_or_else(|e| die(&format!("write: {e}")));
}
