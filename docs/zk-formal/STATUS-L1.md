# Lane L1 (algebra) status

Interface: `zk-formal/ZkFormal/Algebra/` — definitions frozen in `Fp`, `Fp8`,
`Poly`, `RS`, `Decode`; open obligations are the `…Stmt` props in
`Algebra/Statements.lean`; `Algebra/Compose.lean` builds `RS.code : LinCode`.

## Proved (no sorry; axioms ⊆ {propext, Classical.choice, Quot.sound})

| Theorem / instance | Module |
|---|---|
| `IsPrime`, `isPrime_of_trialDiv`, `euclid`, `fermat` | `Algebra.NatPrime` |
| `CommRing.ofEmbedding`, `Field.ofInv`, `binPow_eq`, `pow_inj_of_half` | `Algebra.Transport` |
| `p_prime` (kernel trial division, ~5 s), `Fp.pow_card_sub_one`, `Fp.eleven_nonsquare`, `Fp.sqrtNegOne_sq`, `instance Field Fp`, `IsCharP Fp P`, `Fp.twoAdicGen_pow`, `Fp.twoAdicGen_pow_half`, `Fp.twoAdicGen_pow_inj`, `Fp.mem_all`/`nodup_all` | `Algebra.Fp` |
| `QuadExt.field`, `QuadExt.t_nonsquare` | `Algebra.QuadExt` |
| `instance Field Fp8` (flat exec repr, refinement `toT_mul` into tower), `IsCharP Fp8 P`, `Fp8.mem_all`, `Fp8.nodup_all`, `Fp8.length_all = P^8`, `isBase_iff` | `Algebra.Fp8` |
| `decodeOod_not_base`, `decodeOod_ne_ofBase` | `Algebra.Decode` |

## Open obligations (Statements.lean)

| Statement | Owner | State |
|---|---|---|
| `PolyEvalStmt`, `PolyDegStmt`, `PolySizeStmt`, `IsZeroEvalStmt`, `QuotStmt` | sub-agent L1-poly | in progress |
| `CardRootsLeStmt`, `EqZeroOfRootsStmt`, `LagrangeStmt` | sub-agent L1-roots | in progress |
| `RSLinStmt`, `RSSepStmt` | sub-agent L1-rs | in progress |
| `DecodeChalCountStmt`, `DecodeOodCountStmt` | sub-agent L1-decode | in progress |

## Elaboration times (this host)

| Module | Time |
|---|---|
| `Algebra.Fp` | ~6 s (5 s is `p_prime`) |
| others | < 1 s each |
