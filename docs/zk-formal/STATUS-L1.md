# Lane L1 (algebra) status

Interface: `zk-formal/ZkFormal/Algebra/` — definitions frozen in `Fp`, `Fp8`,
`Poly`, `RS`, `Decode`; open obligations are the `…Stmt` props in
`Algebra/Statements.lean`; `Algebra/Compose.lean` builds `RS.code : LinCode`.

## Proved (no sorry; axioms ⊆ {propext, Classical.choice, Quot.sound})

| Theorem / instance | Module |
|---|---|
| `IsPrime`, `isPrime_of_trialDiv`, `euclid`, `fermat` | `Algebra.NatPrime` |
| `CommRing.ofEmbedding`, `Field.ofInv`, `binPow_eq`, `pow_inj_of_half` | `Algebra.Transport` |
| `p_prime` (Pocklington certificate `31^((p−1)/2) ≡ −1`, `Algebra.Pocklington`; checked by leanchecker, nanoda, lean4lean in < 1 s), `Fp.pow_card_sub_one`, `Fp.eleven_nonsquare`, `Fp.sqrtNegOne_sq`, `instance Field Fp`, `IsCharP Fp P`, `Fp.twoAdicGen_pow`, `Fp.twoAdicGen_pow_half`, `Fp.twoAdicGen_pow_inj`, `Fp.mem_all`/`nodup_all` | `Algebra.Fp` |
| `QuadExt.field`, `QuadExt.t_nonsquare` | `Algebra.QuadExt` |
| `instance Field Fp8` (flat exec repr, refinement `toT_mul` into tower), `IsCharP Fp8 P`, `Fp8.mem_all`, `Fp8.nodup_all`, `Fp8.length_all = P^8`, `isBase_iff` | `Algebra.Fp8` |
| `decodeOod_not_base`, `decodeOod_ne_ofBase` | `Algebra.Decode` |

## Formerly open obligations (Statements.lean): all closed

| Statement | Theorem | Module |
|---|---|---|
| `PolyEvalStmt`, `PolyDegStmt`, `PolySizeStmt`, `IsZeroEvalStmt`, `QuotStmt` | `polyEval`, `polyDeg`, `polySize`, `isZeroEval`, `quotFacts` (+ `Poly.eval_*`, `Poly.coeff_*`, `Poly.degLt_*`) | `Algebra.PolyLemmas` |
| `CardRootsLeStmt`, `EqZeroOfRootsStmt`, `LagrangeStmt` | `Poly.card_roots_le`, `Poly.eq_zero_of_roots`, `Poly.lagrange_spec` | `Algebra.PolyRoots` + `Algebra.Main` |
| `RSLinStmt`, `RSSepStmt` | `RS.lin`, `RS.sep`; `RS.code' : LinCode K n (n - D + 1)` | `Algebra.RSProofs` + `Algebra.Main` |
| `DecodeChalCountStmt`, `DecodeOodCountStmt` | `decodeChal_count` (≤ b·3^8), `decodeOod_count` (≤ b·2·3^8) | `Algebra.DecodeCount` |

## Elaboration times (this host)

| Module | Time |
|---|---|
| `Algebra.Fp` | < 1 s (was ~6 s with trial division) |
| others (PolyLemmas, PolyRoots, RSProofs, DecodeCount, …) | < 1 s each |
