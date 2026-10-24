use labinius_binius::{Circuit, Hash, Session, Opening};
use labinius::scheme::SUITES;
use labinius_bench::pin;
use std::time::Instant;

fn main() {
    pin(8);
    let message: Vec<u8> = (0..65536u32).map(|i| i.wrapping_mul(2654435761) as u8).collect();
    let start=Instant::now();
    let circuit=Circuit::new_private(Hash::Sha256,message.len());
    let circuit_s=start.elapsed().as_secs_f64();
    let start=Instant::now();
    let mut session=Session::new(circuit.constraint_system().clone(),&SUITES[0],true,[0x5A;32]);
    let setup_s=start.elapsed().as_secs_f64();
    println!("NEAR_SHA_SETUP {{\"circuit_s\":{circuit_s},\"setup_s\":{setup_s}}}");
    for repeat in 0..3 {
        let start=Instant::now();
        let witness=circuit.witness(&message);
        let witness_s=start.elapsed().as_secs_f64();
        let start=Instant::now();
        let (mut proof,_timing,sizes)=session.prove(&witness,None);
        let prove_s=start.elapsed().as_secs_f64();
        let start=Instant::now();
        session.verify(witness.inout(),&proof).expect("honest private-message proof");
        let verify_s=start.elapsed().as_secs_f64();
        let public_bytes=witness.inout().len()*8;
        let mut bad_claim=witness.inout().to_vec();
        // Change every public word, including the digest, to avoid depending on layout.
        for x in &mut bad_claim { x.0 ^= 1; }
        assert!(session.verify(&bad_claim,&proof).is_err(),"changed claim accepted");
        let index=proof.tape.len()/2;proof.tape[index]^=1;
        assert!(session.verify(witness.inout(),&proof).is_err(),"changed tape accepted");
        proof.tape[index]^=1;
        match &mut proof.opening {
            Opening::Recursive {proof,..} => {proof.norms_mut()[0]+=1;},
            _=>panic!("expected recursive compressor"),
        }
        assert!(session.verify(witness.inout(),&proof).is_err(),"changed norm accepted");
        println!("NEAR_SHA_RESULT {{\"repeat\":{repeat},\"message_bytes\":65536,\"sha256_compressions\":1025,\"public_bytes\":{public_bytes},\"witness_s\":{witness_s},\"prove_s\":{prove_s},\"verify_s\":{verify_s},\"analytic_proof_bytes\":{},\"tape_bytes\":{},\"negative_checks\":3}}",sizes.total(),proof.tape.len());
    }
}
