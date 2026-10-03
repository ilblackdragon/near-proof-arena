; toy npai verifier: claim 24 B, proof = "TOYPRF01" || claim || sha256(pub||claim)[0..8]
.mem 1024
.dlabel magic
.ascii "TOYPRF01"
    const r0, 0
    tlen r1, 1
    const r2, 24
    eq r3, r1, r2
    jz r3, reject
    tlen r1, 2
    const r2, 40
    eq r3, r1, r2
    jz r3, reject
    tlen r4, 0
    const r5, 200
    ltu r6, r5, r4
    jnz r6, reject
    const r7, 64
    tcopy r7, r0, r4, 0
    add r8, r7, r4
    const r11, 24
    tcopy r8, r0, r11, 1
    add r12, r4, r11
    const r13, 300
    sha256 r13, r7, r12
    const r14, 400
    const r15, 40
    tcopy r14, r0, r15, 2
    const r9, 8
    memeq r2, r14, r0, r9
    jz r2, reject
    const r1, 408
    memeq r2, r1, r8, r11
    jz r2, reject
    const r1, 432
    memeq r2, r1, r13, r9
    jz r2, reject
    const r1, 1
    halt r1
reject:
    halt r0
