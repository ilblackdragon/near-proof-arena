use arena_npai::asm::{assemble, assemble_image, disassemble};
use arena_npai::interp::{self, decode, Inputs, Outcome};

const SUM: &str = r#"
; sum 1..10 == 55, then OUT the claim's first byte and hash a data string
.mem 64
.dlabel msg
.ascii "abc"
.equ N 10
    const r1, N
    const r2, 0
loop:
    add r2, r2, r1
    addi r1, r1, 0xffffffff   # r1 -= 1 (wraps to 2^64-1 when 0 ... masked below)
    const r6, 0xffffffff
    const r7, 32
    shl r6, r6, r7
    or r1, r1, r6
    xor r1, r1, r6
    jnz r1, loop
    const r3, 55
    eq r4, r2, r3
    const r8, msg
    const r9, 3
    const r10, 32
    sha256 r10, r8, r9
    const r11, 32
    out 1, r10, r11
    halt r4
"#;

#[test]
fn assemble_run_roundtrip() {
    let p = assemble(SUM).unwrap();
    let img = assemble_image(SUM).unwrap();
    assert_eq!(decode(&img).unwrap(), p);
    let (o, s) = interp::run_full(
        &p,
        &Inputs {
            public: &[],
            claim: &[],
            proof: &[],
        },
        1000,
        true,
    );
    assert_eq!(o, Outcome::Accept);
    // sha256("abc")
    assert_eq!(
        arena_npai::report::to_hex(&s.out1),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    // disassembly reassembles to the identical image
    assert_eq!(assemble_image(&disassemble(&p)).unwrap(), img);
}

#[test]
fn asm_errors() {
    for bad in [
        "halt r16",
        "const r1, 0x100000000",
        "jmp nowhere",
        "out 2, r0, r0",
        "frob r1",
        "a:\na:\nhalt r0",
        "tlen r0, tape9",
    ] {
        assert!(assemble(bad).is_err(), "{bad:?} should fail");
    }
}
