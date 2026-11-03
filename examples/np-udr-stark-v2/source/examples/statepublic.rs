//! Recompute the D0a public statement from the claim and transmitted hint, without a witness.
//! The logic is `npudr::v3::statement::public_statement` (the chunk verifier calls it in-process).
use npudr::{air::Air, airpub::AirPublic, v3::statement::public_statement};
fn main() {
    let a: Vec<String> = std::env::args().collect();
    assert_eq!(a.len(), 5, "statepublic AIR CLAIM HINT OUT");
    let air = Air::from_json(&std::fs::read_to_string(&a[1]).unwrap()).unwrap();
    let claim = std::fs::read(&a[2]).unwrap();
    let hint = std::fs::read(&a[3]).unwrap();
    let st = public_statement(&AirPublic::of(&air), &claim, &hint).expect("claim/hint preparation");
    let out = std::path::Path::new(&a[4]);
    std::fs::create_dir_all(out).unwrap();
    let pubs: Vec<u8> = st.pubs.iter().flat_map(|x| x.to_le_bytes()).collect();
    std::fs::write(out.join("pubs.bin"), pubs).unwrap();
    let msgs: Vec<_> = st
        .msgs
        .iter()
        .map(|(b, s, m)| serde_json::json!([b, s, m]))
        .collect();
    std::fs::write(out.join("pubmsgs.json"), serde_json::to_vec(&msgs).unwrap()).unwrap();
    println!("PUBLIC_PREPARATION_OK");
}
