//! `seccalc [log2 heights: sha rcpt mrk sort acct node path]`: soundness
//! estimate of the configured parameters plus a query-count sweep.
use npstark::config::*;
use npstark::security::*;
fn main() {
    let a: Vec<usize> = std::env::args().skip(1).filter_map(|s| s.parse().ok()).collect();
    // default: the largest public-fixture shape (256 receipts)
    let mut h = vec![12, 8, 8, 8, 7, 7, 13, 8, 12];
    for (i, x) in a.iter().enumerate() {
        h[i] = *x;
    }
    let shapes = table_shapes(&h);
    println!("table  log_n  constraints  deg  qchunks  main  aux_ef  interactions  max_msg");
    for s in &shapes {
        println!(
            "{:5} {:5} {:12} {:4} {:8} {:5} {:7} {:13} {:8}",
            s.name, s.log_n, s.num_constraints, s.max_degree, s.num_quotient_chunks, s.main_width, s.aux_cols,
            s.interactions, s.max_msg_width
        );
    }
    let r = report(&shapes, NUM_QUERIES, QUERY_POW_BITS);
    println!("\nconfigured: q={} query_pow={} log_blowup={} ext=KoalaBear^8", NUM_QUERIES, QUERY_POW_BITS, LOG_BLOWUP);
    for (n, b) in &r.per_table {
        println!("  {n:5} proven_udr={:5.1} proven_ldr={:5.1} conjectured={:5.1}", b.proven_udr, b.proven_ldr, b.conjectured);
    }
    println!("  logup fingerprint term: {:.1} bits", r.logup_bits);
    println!(
        "  TOTAL (CR-capped 128): proven_udr={:.1} proven_ldr={:.1} conjectured={:.1}",
        r.total.proven_udr, r.total.proven_ldr, r.total.conjectured
    );
    println!(
        "  TOTAL rbr (cap lifted): proven_udr={:.1} proven_ldr={:.1} conjectured={:.1}",
        r.total_rbr.proven_udr, r.total_rbr.proven_ldr, r.total_rbr.conjectured
    );
    println!(
        "  profile accounting (q_H=2^64): proven_udr={:.1} proven_ldr={:.1} conjectured={:.1}",
        profile_bits(r.total_rbr.proven_udr, 64.0),
        profile_bits(r.total_rbr.proven_ldr, 64.0),
        profile_bits(r.total_rbr.conjectured, 64.0)
    );
    println!("\nsweep (query_pow={}):", QUERY_POW_BITS);
    println!("  q   | capped: udr  ldr  conj | rbr: udr  ldr  conj | profile(q_H=2^64): udr  ldr  conj");
    for q in [28, 36, 40, 48, 56, 64, 72, 80, 96, 104, 112, 128, 160, 200, 240] {
        let r = report(&shapes, q, QUERY_POW_BITS);
        println!(
            "  {q:3} | {:5.1} {:5.1} {:5.1} | {:5.1} {:5.1} {:5.1} | {:5.1} {:5.1} {:5.1}",
            r.total.proven_udr, r.total.proven_ldr, r.total.conjectured,
            r.total_rbr.proven_udr, r.total_rbr.proven_ldr, r.total_rbr.conjectured,
            profile_bits(r.total_rbr.proven_udr, 64.0), profile_bits(r.total_rbr.proven_ldr, 64.0),
            profile_bits(r.total_rbr.conjectured, 64.0)
        );
    }
}
