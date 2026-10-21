//! Recompute the D0a public statement from the claim and transmitted hint, without a witness.
use npudr::{air::Air, v3, verifier};
use p3_field::PrimeField32;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    assert_eq!(a.len(), 5, "statepublic AIR CLAIM HINT OUT");
    let air = Air::from_json(&std::fs::read_to_string(&a[1]).unwrap()).unwrap();
    assert_eq!(air.tables.len(), 25);
    let claim = std::fs::read(&a[2]).unwrap();
    let hint = v3::prep::Hint::decode(&std::fs::read(&a[3]).unwrap()).unwrap();
    let prep = v3::d0::prep(&claim, &hint).expect("claim/hint preparation");
    let tape = v3::public::prepared_bytes(&prep, 0);
    assert!(verifier::pub_fit(&air, &tape));
    let out = std::path::Path::new(&a[4]);
    std::fs::create_dir_all(out).unwrap();
    let pubs: Vec<u8> = verifier::public_inputs(&air, &tape)
        .iter()
        .flat_map(|x| x.as_canonical_u32().to_le_bytes())
        .collect();
    std::fs::write(out.join("pubs.bin"), pubs).unwrap();
    let msgs: Vec<_> = verifier::pub_msgs(&air, &tape)
        .iter()
        .map(|(b, s, m)| {
            serde_json::json!([
                b,
                s,
                m.iter().map(|x| x.as_canonical_u32()).collect::<Vec<_>>()
            ])
        })
        .collect();
    std::fs::write(out.join("pubmsgs.json"), serde_json::to_vec(&msgs).unwrap()).unwrap();
    println!("PUBLIC_PREPARATION_OK");
}
