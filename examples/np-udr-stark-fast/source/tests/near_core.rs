//! NEAR core on the public fixtures: claim bytes = expected_claim.bin; the
//! records of `ext_of` re-hash to the claim's roots (`Good.preRoot`,
//! `postRoot`, `outRoot`, `rfCommit`, `tokens`), walks reach the slots.
use npudr::near::{ext, info, spec};

fn cases() -> Vec<std::path::PathBuf> {
    let d = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../oracle/fixtures/public/cases");
    let mut v: Vec<_> = std::fs::read_dir(d).unwrap().map(|e| e.unwrap().path()).collect();
    v.sort();
    v
}

#[test]
fn fixtures_core() {
    for d in cases() {
        let req = std::fs::read(d.join("request.bin")).unwrap();
        let wit = std::fs::read(d.join("witness.bin")).unwrap();
        let exp = std::fs::read(d.join("expected_claim.bin")).unwrap();
        let inp = spec::load_inputs(&req, &wit).unwrap_or_else(|e| panic!("{d:?}: {e}"));
        let c = &inp.claim;
        assert_eq!(c.encode(), exp, "{d:?}: claim");
        assert_eq!(inp.witness.trie.hash_of(), c.pre_state_root.to_vec(), "{d:?}: witness root");
        let e = ext::ext_of(c, &inp.witness);
        assert_eq!(e.pre_trie().hash_of(), c.pre_state_root.to_vec(), "{d:?}: preRoot");
        let n = e.rs.len();
        let post = ext::trie_of(&e.ns, &|k| e.vals_at(n, k));
        assert_eq!(post.hash_of(), c.slice_post_root.to_vec(), "{d:?}: postRoot");
        assert_eq!(spec::outcome_root(&e.outcomes(c)), c.outcome_root.to_vec(), "{d:?}: outRoot");
        assert_eq!(spec::refunds_commitment(&e.refunds(c)), c.refunds_commitment.to_vec());
        assert_eq!(e.refunds(c).len(), c.refund_count as usize);
        assert_eq!(e.tok_at(c, n), c.tokens_burnt_total);
        assert!(ext::revealed_of(&e.ns) <= 3_000_000);
        let i = info::mk_info(c, &e);
        assert_eq!(info::sha_n(&i.pre[0]), c.pre_state_root.to_vec(), "{d:?}: info pre root");
        assert_eq!(info::sha_n(&i.post[0]), c.slice_post_root.to_vec(), "{d:?}: info post root");
        assert!(info::walk_errors(&i).is_empty(), "{d:?}: {:?}", info::walk_errors(&i));
        let ws = info::walks_of(&i);
        for (r, w) in ws.iter().enumerate() {
            assert_eq!(info::final_of(w), e.slot(r), "{d:?}: walk {r} final");
        }
        eprintln!("{}: nodes={} touched={} receipts={} ok", d.file_name().unwrap().to_string_lossy(), e.ns.len(), i.touched.len(), n);
    }
}
