//! check <case-dir>...: print derive_claim result vs expected_claim/claim.bin per case.
fn main() {
    let mut bad = 0;
    let (mut ok, mut ood) = (0, 0);
    for a in std::env::args().skip(1) {
        let d = std::path::Path::new(&a);
        let req = std::fs::read(d.join("request.bin")).unwrap();
        let wit = std::fs::read(d.join("witness.bin")).unwrap_or_default();
        let want = std::fs::read(d.join("expected_claim.bin")).or_else(|_| std::fs::read(d.join("claim.bin"))).ok();
        match (transfer_core::derive_claim(&req, &wit), want) {
            (Ok((c, _)), Some(w)) if c == w => ok += 1,
            (Err(e), None) => { ood += 1; println!("{a}: out ({})", e.reason()) }
            (r, w) => { bad += 1; println!("{a}: MISMATCH got={:?} want_present={}", r.map(|x| x.0.len()), w.is_some()) }
        }
    }
    println!("ok={ok} out_of_domain={ood} inconsistent={bad}");
    std::process::exit(if bad == 0 { 0 } else { 1 });
}
