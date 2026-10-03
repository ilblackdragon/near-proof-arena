//! `prepare --params <approved_params.bin> --out <public_dir>`
//!
//! Validates the approved parameters (`spec/claim-v1.md` §5) and writes them
//! unchanged as `public_dir/public.bin` — the single public tape whose SHA-256
//! is `publicDigest` in the admission statement. The verifier ignores it (the
//! relation fixes every parameter), so it carries no trust.
use reexec::spec::{PARAMS_FORMAT, STATEMENT_ID};
use reexec::wire::Reader;

fn main() {
    let a = reexec::parse_args(&["params", "out"]);
    let params = std::fs::read(&a["params"]).unwrap_or_else(|e| reexec::die(&format!("params: {e}")));
    let mut r = Reader::new(&params);
    let ok = (|| {
        r.expect_tag(PARAMS_FORMAT, "params format")?;
        r.expect_tag(STATEMENT_ID, "statement id")?;
        if r.u32("pv")? != 86 || r.bytes("chain")? != b"mainnet" {
            return Err(reexec::wire::WireError("params: wrong pv/chain"));
        }
        r.hash("runtime config digest")?;
        r.finish()
    })();
    if let Err(e) = ok {
        reexec::die(&format!("params: {e}"));
    }
    std::fs::create_dir_all(&a["out"]).unwrap_or_else(|e| reexec::die(&format!("out: {e}")));
    std::fs::write(a["out"].join("public.bin"), &params).unwrap_or_else(|e| reexec::die(&format!("write: {e}")));
}
