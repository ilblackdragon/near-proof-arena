//! Development tool (not an entry point): execute the guest without proving
//! and report RISC-V cycle counts. `zkexec <case-dir>...`
use sp1_sdk::blocking::{Prover, ProverClient};
use sp1_sdk::SP1Stdin;
use zk_prover::GUEST_ELF;

fn main() {
    let client = ProverClient::builder().light().build();
    println!("case\treceipts\twitness_bytes\tcycles\tsyscalls\texec_ms\tclaim_ok");
    for a in std::env::args().skip(1) {
        let d = std::path::Path::new(&a);
        let req = std::fs::read(d.join("request.bin")).unwrap();
        let wit = std::fs::read(d.join("witness.bin")).unwrap();
        let want = std::fs::read(d.join("expected_claim.bin")).or_else(|_| std::fs::read(d.join("claim.bin"))).ok();
        let stats = transfer_core::derive_claim(&req, &wit).map(|x| x.1).unwrap_or_default();
        let mut stdin = SP1Stdin::new();
        stdin.write_vec(req);
        stdin.write_vec(wit);
        let t = std::time::Instant::now();
        let (pv, report) = client.execute(GUEST_ELF, stdin).run().expect("execute");
        let ms = t.elapsed().as_millis();
        let ok = want.as_deref() == Some(pv.as_slice());
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}",
            d.file_name().unwrap().to_string_lossy(),
            stats.receipts,
            stats.witness_bytes,
            report.total_instruction_count(),
            report.total_syscall_count(),
            ms,
            ok
        );
    }
}
