# Interface requests

## From L3 (IOP math) — 2026-10-05

### R-L3-1 (to L2, L4): `RbrFacts` shape (`zk-formal/ZkFormal/Udr/Rbr.lean`)
`RbrFacts V InLang Kall bad agree := ∃ Doomed, RbrWith V InLang Kall bad agree Doomed`
with fields `init`, `prover`, `chal`, `query` over L4's `IopSpec`/`PT K (Oracle F)`.
Changes w.r.t. DESIGN.md §6.4:
* `Doomed` is existential (L2 should not depend on its definition).
* `Agree τ x` is `V.ChecksPass τ x (V.trueOpenings τ x)`; the draft `local` field is gone.
* `query` additionally assumes `Shaped V τ` (every entry fits its slot, header admissible —
  the BCS parser guarantees this for extracted transcripts) and `V.global (V.prep τ.erase) = true`
  (an accepting run passes the clear-text checks). L2's query-phase event should therefore be
  "doomed ∧ shaped ∧ global passes ∧ all chunk positions pass".
* L2's `Bcs/Extract.lean` has its own `PT`/`IopSpec`; L2 and L4 need to agree on one (L3 uses L4's).

### R-L3-2 (to lead / Params): unique-decoding radius must be `(n - D)/2 - 1`
DEEP decoding needs `n - 2e ≥ D + 1` (the DEEP preimage `v + (X - z)·g` has length `D + 1`); with
`e = (n - D)/2` exactly, a wrong OOD claim can coexist with a close DEEP word (off by one).
L3 uses `e_i = (n_i - D_i)/2 - 1` at every FRI layer (FRI now only needs `e_i ≤ 2e_{i+1} + 1`).
`Params.e2` should become `(n - D)/2 - 1`; the effect on the bound is a factor ≈ (1 + 2^-25)^216.

### R-L3-3 (to lead / Params, L6): grand-product round error is the total multiplicity
The γ round (`∏(γ - fp)^mult` equality) can be escaped by up to `deg` challenges, where `deg` is the
total multiplicity on a bus side: up to `Σ_t 2^log_t · Σ_i (2^{bits_i} - 1)` (≈ 2^47 per interaction
at 2^22 rows × 25 bits), not `#messages`. `commitBad = 2^36` is too small unless the AIR bounds
total multiplicities; with `2^48` the bound is ≈ 2^-131 (udr2_ok still holds, udr2_margin does not).
Please fix the AIR's multiplicity budget (L6) and `commitBad` accordingly.

### R-L3-4 (to L1): limb linearity laws
Decoding a base-field trace from an extension-field codeword needs `limbs (x + y) = limbs x + limbs y`
(coordinatewise), `limbs (embed a * y) = a • limbs y`, `limbs (embed a) = [a, 0, …, 0]`
(as `StarkFieldLaws` fields or L1 lemmas about the `Fp`/`Fp8` instance).
