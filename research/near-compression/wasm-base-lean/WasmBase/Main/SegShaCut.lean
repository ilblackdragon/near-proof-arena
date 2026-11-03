import WasmBase.Main.SegShaMemb

/-!
# WasmBase.Main.SegShaCut — the CUT stream's digest, and a canonicity gap in CUTO's filler (E2E M4b)

CUTO hashes the consumed small-state messages two per SHA-512 block (8 words each: the 7 fields as
`lo + 2^21·hi + 2^42·mark` and a zero word); an odd count is completed by one **filler** row
(`kD = 1`, `act = 0`, `j = 1`), then the padding group (`kP`).  `cutWords L` (`Main/SegRows.lean`)
completes the last block with the all-zero message, and `cutDigest L = sha384 (cutBytes L)`.

**The filler row was not forced to zero** (`cuto_filler_counterexample`, against the pre-fix words
`rowWordsKD`; fixed in M4b, `cuto_filler_fixed`).  On a filler row every
CUTO constraint and every non-chip interaction is satisfied with `lo_1 = 1` (and `slot = 1`, which
`F_1 = slot` asks for); its block words carry `lo_k`, `hi_k` multiplied by `kD = 1`, so the filler
message it hashes is `[0, 1, 0, …]`-shaped instead of zero.  The digest CUTO publishes is then
SHA-384 of `msgWords L ++ fillerWords` with *prover-chosen* filler words, not `cutDigest L`: the
boundary digest is not a function of the boundary state.  (Binding is not lost by itself — CUTI's
filler is ignored the same way — but `ctx_out = cutDigest L` is false for satisfying traces.)
**Fix** (AIR change, degree unchanged): in `Cut.rowWords` multiply `lo_k`, `hi_k` by `act` instead
of `kD` (`act ≤ kD`; data rows have `act = 1`), so a filler row hashes the zero message.

The padding block is as FIPS 180-4 requires (`r16 gl` is in place since `gl_padding_counterexample`):
word 0 of the `j = 0` padding row is `2^63`, word 15 of the `j = 1` row is `1024·gl + 2^21·gh =
1024·gi` with `gl < 2^11`, `gh < 2^16`, and `gi` the number of data groups — proved inside
`cut_stream_digest` (`hpad : … = padBlk (1024·N)`, then `pad_whole`).

## What is proved (both CUTI, `t = 30`, `ctx_in` = pub 31–48, and CUTO, `t = 31`, `ctx_out` = pub 49–66)

* `cut_shape` / `cut_rows`: the table is `2N` data rows (`kD = 1`, `j = r mod 2`, `gi = r / 2`, a group
  shares `cid`, the chaining value passes from row `2g + 1` to `2g + 2`, row 0 starts at `IV384`),
  then the padding group at rows `2N`, `2N + 1`, then dead rows (from the stream constraints alone);
* `cut_group`: under `HoldsX` + `ChipIf compressW`, rows `2g`, `2g + 1` are one chip compression;
* **`cut_stream_digest`**: the public digest limbs are `limbsF d` with
  `wbytes d = sha384 (wbytes Ws)`, `Ws = (List.range (2N)).flatMap (streamW …)` the 8 decoded block
  words of every data row in row order (all `< 2^64`).

## Open

* Linking `Ws` to `cutWords L` for CUTO's consumed list `L` (fields `F_k = lo_k + 2^16·hi_k` of the
  `act` rows in row order): an `act` row's `streamW` is `msgWords` of its fields (needs `lo < 2^16` from
  `r16 lo`, `hi < 2^14` from `r16 (4·hi)` and the chip limb bound — `cut_hi`), and `cutBytes = wbytes ∘
  cutWords` (`wordBytes = beN 8`).  With the filler as in the AIR today, `Ws = L.flatMap msgWords ++
  fillerWords` with prover-chosen `fillerWords` (`cuto_filler_counterexample`), so `ctx_out = cutDigest L`
  holds only after the `act`-for-`kD` fix (or under the hypothesis that the filler row's `lo`, `hi` are 0).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

/-- The filler counterexample's row: `j = kD = 1`, `act = 0`, `lo_1 = 1`, `slot = 1`; the next row
starts the padding group (`kP = 1`, `gi = 1`). -/
def cexCur (i : Nat) : F := if i = 1 ∨ i = 2 ∨ i = 6 ∨ i = 48 then 1 else 0
def cexNxt (i : Nat) : F := if i = 3 ∨ i = 19 then 1 else 0
def cexRow : Row := ⟨cexCur, cexNxt, fun _ => 0, false, false⟩

theorem cuto_ix_cex : ix Cut.Out.cols "act" = 0 ∧ ix Cut.Out.cols "j" = 1 ∧ ix Cut.Out.cols "kD" = 2 ∧
    ix Cut.Out.cols "kP" = 3 ∧ ix Cut.Out.cols "lo1" = 6 ∧ ix Cut.Out.cols "gi" = 19 ∧ ix Cut.Out.cols "slot" = 48 := by
  decide

/-- The block words as `Cut.rowWords` defined them before the M4b fix (message limbs gated by `kD`
instead of `act`); kept to state the counterexample. -/
def rowWordsKD (cs : List String) : List W3 :=
  let kD := Cut.c cs "kD"; let kP := Cut.c cs "kP"; let j := Cut.c cs "j"
  ((List.range 7).map fun k =>
    [kD * Cut.c cs s!"lo{k}", kD * Cut.c cs s!"hi{k}",
     if k = 0 then Cut.c cs "act" + kP * (1 - j) * Expr.c (2 ^ 21) else 0]) ++
  [[kP * j * 1024 * Cut.c cs "gl", kP * j * Cut.c cs "gh", 0]]

/-- **CUTO's filler row was not forced to the zero message** (before the M4b fix).  `cexRow`
satisfies every CUTO constraint, every interaction of CUTO other than the chip's (bus 103) has count
0 on it, the chip receives have count 1, and the eight block words the pre-fix AIR hashed
(`rowWordsKD`) are not all zero (word 1 is `[1, 0, 0]`, i.e. the 64-bit word 1). -/
theorem cuto_filler_counterexample :
    (∀ e ∈ Cut.Out.constraints, e.eval cexRow = 0) ∧
    (∀ i ∈ Cut.Out.inters, i.bus ≠ busIf → i.count.eval cexRow = 0) ∧
    (∀ i ∈ Cut.Out.inters, i.bus = busIf → i.count.eval cexRow = 1) ∧
    (Cut.Out.c "act").eval cexRow = 0 ∧ (Cut.Out.c "kD").eval cexRow = 1 ∧ (Cut.Out.c "j").eval cexRow = 1 ∧
    (Cut.Out.n "kP").eval cexRow = 1 ∧
    (rowWordsKD Cut.Out.cols).map (·.map (·.eval cexRow)) =
      [[0, 0, 0], [1, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]] := by
  decide

/-- **The fix**: with the message limbs gated by `act` (`Cut.rowWords` now), the same row hashes the
all-zero message. -/
theorem cuto_filler_fixed :
    (Cut.rowWords Cut.Out.cols).map (·.map (·.eval cexRow)) =
      [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]] := by
  decide



/-! ## The CUT stream: row structure -/

theorem cut_ixs {cs : List String} (hcs : cs = Cut.In.cols ∨ cs = Cut.Out.cols) :
    ix cs "act" = 0 ∧ ix cs "j" = 1 ∧ ix cs "kD" = 2 ∧ ix cs "kP" = 3 ∧ ix cs "kX" = 4 ∧
    ix cs "gi" = 19 ∧ ix cs "gl" = 20 ∧ ix cs "gh" = 21 ∧ ix cs "cid" = 22 ∧
    (∀ i, i < 24 → ix cs s!"h{i}" = 23 + i) ∧ (∀ k, k < 7 → ix cs s!"lo{k}" = 5 + k ∧ ix cs s!"hi{k}" = 12 + k) := by
  rcases hcs with rfl | rfl <;> decide

section stream
variable {t : Nat} {cs : List String} {base : Nat} {pub : List F} {tr : Trace}
  (hcs : cs = Cut.In.cols ∨ cs = Cut.Out.cols)
  (hC : ∀ r, r < tr.height t → ∀ e ∈ Cut.streamConstraints cs base, e.eval (tr.row pub t r) = 0)

/-- Cell `i` of row `r` of the CUT table. -/
abbrev kc (tr : Trace) (t r i : Nat) : F := tr.cell t r i

theorem kc_c (r : Nat) (s : String) : (Cut.c cs s).eval (tr.row pub t r) = kc tr t r (ix cs s) := rfl

theorem kc_n {r : Nat} (hr : r + 1 < tr.height t) (s : String) :
    (Cut.n cs s).eval (tr.row pub t r) = kc tr t (r + 1) (ix cs s) := by
  simp only [Cut.n, nv, Expr.eval_nxt, Trace.row, Nat.mod_eq_of_lt hr]

theorem sel_trans {r : Nat} (hr : r + 1 < tr.height t) : Expr.trans.eval (tr.row pub t r) = 1 := by
  have : (r + 1 == tr.height t) = false := by simp; omega
  simp [Expr.eval, Trace.row, this]

theorem sel_first : Expr.first.eval (tr.row pub t 0) = 1 := by simp [Expr.eval, Trace.row]

theorem sel_last {r : Nat} (hr : r + 1 = tr.height t) : Expr.last.eval (tr.row pub t r) = 1 := by
  simp [Expr.eval, Trace.row, hr]

include hcs hC in
/-- The row kinds are bits, one-hot. -/
theorem cut_bits {r : Nat} (hr : r < tr.height t) :
    (kc tr t r 0 = 0 ∨ kc tr t r 0 = 1) ∧ (kc tr t r 1 = 0 ∨ kc tr t r 1 = 1) ∧
    ((kc tr t r 2 = 1 ∧ kc tr t r 3 = 0 ∧ kc tr t r 4 = 0) ∨ (kc tr t r 2 = 0 ∧ kc tr t r 3 = 1 ∧ kc tr t r 4 = 0) ∨
      (kc tr t r 2 = 0 ∧ kc tr t r 3 = 0 ∧ kc tr t r 4 = 1)) ∧
    (kc tr t r 2 = 0 → kc tr t r 0 = 0) := by
  obtain ⟨ia, ij, iD, iP, iX, -⟩ := cut_ixs hcs
  have C := hC r hr
  have b : ∀ s, Chips.bool (Cut.c cs s) ∈ Cut.streamConstraints cs base →
      kc tr t r (ix cs s) = 0 ∨ kc tr t r (ix cs s) = 1 := by
    intro s hs; have := C _ hs
    simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', kc_c] at this
    exact bool_cases (by simpa [cast_one] using this)
  have ba := b "act" (by simp [Cut.streamConstraints]); have bj := b "j" (by simp [Cut.streamConstraints])
  have bD := b "kD" (by simp [Cut.streamConstraints]); have bP := b "kP" (by simp [Cut.streamConstraints])
  have bX := b "kX" (by simp [Cut.streamConstraints])
  have hs := C (Cut.c cs "kD" + Cut.c cs "kP" + Cut.c cs "kX" - 1) (by simp [Cut.streamConstraints])
  have ha := C ((1 - Cut.c cs "kD") * Cut.c cs "act") (by simp [Cut.streamConstraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', kc_c] at hs ha
  rw [ia, ij, iD, iP, iX] at *
  refine ⟨ba, bj, ?_, fun h0 => ?_⟩
  · rcases bD with d | d <;> rcases bP with p | p <;> rcases bX with x | x <;> rw [d, p, x] at hs <;>
      first | (exfalso; revert hs; decide) | simp_all
  · rw [h0] at ha; grind

include hcs hC in
/-- The CUT transition facts between rows `r` and `r + 1`. -/
theorem cut_trans {r : Nat} (hr1 : r + 1 < tr.height t) :
    (kc tr t r 4 = 0 → kc tr t r 1 = 0 → kc tr t (r + 1) 1 = 1 ∧ kc tr t (r + 1) 2 = kc tr t r 2 ∧
      kc tr t (r + 1) 3 = kc tr t r 3 ∧ kc tr t (r + 1) 22 = kc tr t r 22) ∧
    (kc tr t r 1 = 1 → kc tr t r 2 = 1 → kc tr t (r + 1) 4 = 0) ∧
    (kc tr t r 1 = 1 → kc tr t r 3 = 1 → kc tr t (r + 1) 4 = 1) ∧
    (kc tr t r 4 = 1 → kc tr t (r + 1) 4 = 1) ∧
    (kc tr t r 1 = 1 → kc tr t (r + 1) 4 = 0 → kc tr t (r + 1) 1 = 0) ∧
    (kc tr t (r + 1) 4 = 0 → kc tr t (r + 1) 19 = kc tr t r 19 + kc tr t r 1) ∧
    (kc tr t r 1 = 1 → kc tr t (r + 1) 4 = 0 → ∀ i, i < 24 → kc tr t (r + 1) (23 + i) = kc tr t r (23 + i)) := by
  obtain ⟨ia, ij, iD, iP, iX, igi, -, -, icid, ih, -⟩ := cut_ixs hcs
  have C := hC r (by omega)
  have tr1 := sel_trans (pub := pub) hr1
  have g : ∀ e ∈ Cut.streamConstraints cs base, e.eval (tr.row pub t r) = 0 := C
  have e1 := g (.trans * (1 - Cut.c cs "kX") * (1 - Cut.c cs "j") * (Cut.n cs "j" - 1)) (by simp [Cut.streamConstraints])
  have e2 := g (.trans * (1 - Cut.c cs "kX") * (1 - Cut.c cs "j") * (Cut.n cs "kD" - Cut.c cs "kD")) (by simp [Cut.streamConstraints])
  have e3 := g (.trans * (1 - Cut.c cs "kX") * (1 - Cut.c cs "j") * (Cut.n cs "kP" - Cut.c cs "kP")) (by simp [Cut.streamConstraints])
  have e4 := g (.trans * Cut.c cs "j" * Cut.c cs "kD" * Cut.n cs "kX") (by simp [Cut.streamConstraints])
  have e5 := g (.trans * Cut.c cs "j" * Cut.c cs "kP" * (1 - Cut.n cs "kX")) (by simp [Cut.streamConstraints])
  have e6 := g (.trans * Cut.c cs "kX" * (1 - Cut.n cs "kX")) (by simp [Cut.streamConstraints])
  have e7 := g (.trans * Cut.c cs "j" * (1 - Cut.n cs "kX") * Cut.n cs "j") (by simp [Cut.streamConstraints])
  have e8 := g (.trans * (1 - Cut.n cs "kX") * (Cut.n cs "gi" - Cut.c cs "gi" - Cut.c cs "j")) (by simp [Cut.streamConstraints])
  have e9 := g (.trans * (1 - Cut.c cs "kX") * (1 - Cut.c cs "j") * (Cut.n cs "cid" - Cut.c cs "cid")) (by simp [Cut.streamConstraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', kc_c, kc_n hr1, tr1, cast_one,
    ia, ij, iD, iP, iX, igi, icid] at e1 e2 e3 e4 e5 e6 e7 e8 e9
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_, fun h1 h2 => ?_, fun h1 => ?_,
    fun h1 h2 i hi => ?_⟩
  · rw [h1, h2] at e1 e2 e3 e9
    refine ⟨by grind, by grind, by grind, by grind⟩
  · rw [h1, h2] at e4; grind
  · rw [h1, h2] at e5; grind
  · rw [h1] at e6; grind
  · rw [h1, h2] at e7; grind
  · rw [h1] at e8; grind
  · have e := g (.trans * Cut.c cs "j" * (1 - Cut.n cs "kX") * (Cut.n cs s!"h{i}" - Cut.c cs s!"h{i}")) (by
      simp only [Cut.streamConstraints, List.mem_append]
      left; right
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', kc_c, kc_n hr1, tr1, cast_one,
      ij, iX, ih i hi, h1, h2] at e
    grind

include hcs hC in
theorem cut_first (h0 : 0 < tr.height t) :
    kc tr t 0 1 = 0 ∧ kc tr t 0 4 = 0 ∧ kc tr t 0 19 = 0 ∧
      ∀ i, i < 24 → kc tr t 0 (23 + i) = ((ivLimbs.getD i 0 : Nat) : F) := by
  obtain ⟨ia, ij, iD, iP, iX, igi, -, -, icid, ih, -⟩ := cut_ixs hcs
  have g := hC 0 h0
  have f1 := sel_first (t := t) (tr := tr) (pub := pub)
  have e1 := g (.first * Cut.c cs "j") (by simp [Cut.streamConstraints])
  have e2 := g (.first * Cut.c cs "kX") (by simp [Cut.streamConstraints])
  have e3 := g (.first * Cut.c cs "gi") (by simp [Cut.streamConstraints])
  simp only [Expr.eval_mul', kc_c, f1, ij, iX, igi] at e1 e2 e3
  refine ⟨by grind, by grind, by grind, fun i hi => ?_⟩
  have e := g (.first * (Cut.c cs s!"h{i}" - Expr.c (ivLimbs.getD i 0))) (by
    simp only [Cut.streamConstraints, List.mem_append]
    left; left; right
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_c, kc_c, f1, ih i hi] at e
  grind

/-- `r mod 2` in the field. -/
abbrev jF (r : Nat) : F := ((r % 2 : Nat) : F)

include hcs hC in
/-- **The shape of a CUT stream**: `2N` data rows (`kD = 1`, `j = r mod 2`), then the padding group
(`kP = 1`, `j = 0, 1`) at rows `2N`, `2N + 1`. -/
theorem cut_shape (hh : 4 ≤ tr.height t) :
    ∃ N, 2 * N + 2 ≤ tr.height t ∧ (∀ r, r < 2 * N → kc tr t r 2 = 1 ∧ kc tr t r 1 = jF r) ∧
      kc tr t (2 * N) 3 = 1 ∧ kc tr t (2 * N) 1 = 0 ∧ kc tr t (2 * N + 1) 3 = 1 ∧ kc tr t (2 * N + 1) 1 = 1 := by
  have inv : ∀ r, r < tr.height t →
      (∀ r', r' ≤ r → kc tr t r' 2 = 1 ∧ kc tr t r' 1 = jF r') ∨
      (∃ N, 2 * N ≤ r ∧ (∀ r', r' < 2 * N → kc tr t r' 2 = 1 ∧ kc tr t r' 1 = jF r') ∧
        kc tr t (2 * N) 3 = 1 ∧ kc tr t (2 * N) 1 = 0 ∧
        (r = 2 * N ∨ (kc tr t (2 * N + 1) 3 = 1 ∧ kc tr t (2 * N + 1) 1 = 1 ∧ (r = 2 * N + 1 ∨ kc tr t r 4 = 1)))) := by
    intro r
    induction r with
    | zero =>
      intro h0
      obtain ⟨j0, x0, -, -⟩ := cut_first hcs hC h0
      obtain ⟨-, -, k0, -⟩ := cut_bits hcs hC h0
      rcases k0 with ⟨d, -, -⟩ | ⟨-, p, -⟩ | ⟨-, -, x⟩
      · left; intro r' hr'; rw [show r' = 0 by omega]; exact ⟨d, j0⟩
      · right; exact ⟨0, Nat.le_refl _, fun r' h => absurd h (by omega), p, j0, Or.inl rfl⟩
      · rw [x0] at x; exact absurd x (by decide)
    | succ r ih =>
      intro hr1
      have T := cut_trans hcs hC hr1
      obtain ⟨-, -, kr, -⟩ := cut_bits hcs hC (r := r) (by omega)
      obtain ⟨-, -, kr1, -⟩ := cut_bits hcs hC hr1
      rcases ih (by omega) with hl | ⟨N, hN, hd, hp, hj, hcase⟩
      · obtain ⟨d, jr⟩ := hl r (Nat.le_refl _)
        have x0 : kc tr t r 4 = 0 := by
          rcases kr with ⟨-, -, x⟩ | ⟨-, -, x⟩ | ⟨d', -, -⟩
          · exact x
          · exact x
          · rw [d] at d'; exact absurd d' (by decide)
        rcases Nat.mod_two_eq_zero_or_one r with e | e
        · have j0 : kc tr t r 1 = 0 := by rw [jr, jF, e]; rfl
          obtain ⟨j1, dd, -, -⟩ := T.1 x0 j0
          left; intro r' hr'
          rcases (by omega : r' ≤ r ∨ r' = r + 1) with h' | rfl
          · exact hl r' h'
          · refine ⟨dd.trans d, ?_⟩; rw [j1, jF, show (r + 1) % 2 = 1 by omega]; rfl
        · have j1 : kc tr t r 1 = 1 := by rw [jr, jF, e]; rfl
          have x1 := T.2.1 j1 d
          have jn := T.2.2.2.2.1 j1 x1
          rcases kr1 with ⟨d1, -, -⟩ | ⟨-, p1, -⟩ | ⟨-, -, xx⟩
          · left; intro r' hr'
            rcases (by omega : r' ≤ r ∨ r' = r + 1) with h' | rfl
            · exact hl r' h'
            · refine ⟨d1, ?_⟩; rw [jn, jF, show (r + 1) % 2 = 0 by omega]; rfl
          · right
            refine ⟨(r + 1) / 2, by omega, fun r' h' => hl r' (by omega), ?_, ?_, Or.inl (by omega)⟩
            · rw [show 2 * ((r + 1) / 2) = r + 1 by omega]; exact p1
            · rw [show 2 * ((r + 1) / 2) = r + 1 by omega]; exact jn
          · rw [x1] at xx; exact absurd xx (by decide)
      · right
        refine ⟨N, by omega, hd, hp, hj, Or.inr ?_⟩
        rcases hcase with e | ⟨p1, j1, e | x⟩
        · subst e
          have x0 : kc tr t (2 * N) 4 = 0 := by
            rcases kr with ⟨-, -, x⟩ | ⟨-, -, x⟩ | ⟨-, p', -⟩
            · exact x
            · exact x
            · rw [hp] at p'; exact absurd p' (by decide)
          obtain ⟨j1, -, pp, -⟩ := T.1 x0 hj
          exact ⟨pp.trans hp, j1, Or.inl rfl⟩
        · subst e
          exact ⟨p1, j1, Or.inr (T.2.2.1 j1 p1)⟩
        · exact ⟨p1, j1, Or.inr (T.2.2.2.1 x)⟩
  have hl1 : tr.height t - 1 + 1 = tr.height t := by omega
  have l1 := sel_last (pub := pub) hl1
  have g := hC (tr.height t - 1) (by omega)
  have e1 := g (.last * Cut.c cs "kD") (by simp [Cut.streamConstraints])
  have e2 := g (.last * (1 - Cut.c cs "kX") * (1 - Cut.c cs "j")) (by simp [Cut.streamConstraints])
  obtain ⟨ia, ij, iD, iP, iX, -⟩ := cut_ixs hcs
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', kc_c, l1, ij, iD, iX] at e1 e2
  obtain ⟨-, -, kl, -⟩ := cut_bits hcs hC (r := tr.height t - 1) (by omega)
  rcases inv (tr.height t - 1) (by omega) with hl | ⟨N, hN, hd, hp, hj, hcase⟩
  · have := (hl _ (Nat.le_refl _)).1; rw [this] at e1; exact absurd e1 (by decide)
  · rcases hcase with e | ⟨p1, j1, hcase⟩
    · exfalso
      rw [← e] at hp hj
      have x0 : kc tr t (tr.height t - 1) 4 = 0 := by
        rcases kl with ⟨-, -, x⟩ | ⟨-, -, x⟩ | ⟨-, p', -⟩
        · exact x
        · exact x
        · rw [hp] at p'; exact absurd p' (by decide)
      rw [x0, hj] at e2; revert e2; decide
    · refine ⟨N, ?_, hd, hp, hj, p1, j1⟩
      rcases (by omega : tr.height t - 1 = 2 * N ∨ 2 * N + 2 ≤ tr.height t) with h | h
      · exfalso
        rcases hcase with e | x
        · omega
        · rw [h] at x
          obtain ⟨-, -, k2, -⟩ := cut_bits hcs hC (r := 2 * N) (by omega)
          rcases k2 with ⟨-, p', -⟩ | ⟨-, -, x'⟩ | ⟨-, p', -⟩
          · rw [hp] at p'; exact absurd p' (by decide)
          · rw [x] at x'; exact absurd x' (by decide)
          · rw [hp] at p'; exact absurd p' (by decide)
      · exact h

include hcs hC in
/-- The rows of a CUT stream with their counters: `j = r mod 2`, `gi = r / 2`, a group shares `cid`,
and the chaining value passes from a group's `j = 1` row to the next group's `j = 0` row. -/
theorem cut_rows (hh : 4 ≤ tr.height t) :
    ∃ N, 2 * N + 2 ≤ tr.height t ∧ (∀ r, r < 2 * N → kc tr t r 2 = 1) ∧
      kc tr t (2 * N) 3 = 1 ∧ kc tr t (2 * N + 1) 3 = 1 ∧
      (∀ r, r ≤ 2 * N + 1 → kc tr t r 1 = jF r ∧ kc tr t r 4 = 0 ∧ (kc tr t r 2 = 0 → kc tr t r 3 = 1) ∧
        kc tr t r 19 = ((r / 2 : Nat) : F)) ∧
      (∀ g, g ≤ N → kc tr t (2 * g + 1) 22 = kc tr t (2 * g) 22) ∧
      (∀ g, g < N → ∀ i, i < 24 → kc tr t (2 * g + 2) (23 + i) = kc tr t (2 * g + 1) (23 + i)) := by
  obtain ⟨N, hN, hd, hp0, hj0, hp1, hj1⟩ := cut_shape hcs hC hh
  have kinds : ∀ r, r ≤ 2 * N + 1 → kc tr t r 1 = jF r ∧ kc tr t r 4 = 0 ∧ (kc tr t r 2 = 0 → kc tr t r 3 = 1) := by
    intro r hr
    obtain ⟨-, -, k, -⟩ := cut_bits hcs hC (r := r) (by omega)
    have hx : (kc tr t r 2 = 1 ∨ kc tr t r 3 = 1) → kc tr t r 4 = 0 ∧ (kc tr t r 2 = 0 → kc tr t r 3 = 1) := by
      intro h
      rcases k with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact ⟨c, fun h0 => by rw [a] at h0; exact absurd h0 (by decide)⟩
      · exact ⟨c, fun _ => b⟩
      · rcases h with h | h
        · rw [a] at h; exact absurd h (by decide)
        · rw [b] at h; exact absurd h (by decide)
    rcases (by omega : r < 2 * N ∨ r = 2 * N ∨ r = 2 * N + 1) with h | rfl | rfl
    · exact ⟨(hd r h).2, hx (Or.inl (hd r h).1)⟩
    · exact ⟨by rw [hj0, jF, show 2 * N % 2 = 0 by omega]; rfl, hx (Or.inr hp0)⟩
    · exact ⟨by rw [hj1, jF, show (2 * N + 1) % 2 = 1 by omega]; rfl, hx (Or.inr hp1)⟩
  refine ⟨N, hN, fun r h => (hd r h).1, hp0, hp1, fun r hr => ⟨(kinds r hr).1, (kinds r hr).2.1, (kinds r hr).2.2, ?_⟩,
    fun g hg => ?_, fun g hg i hi => ?_⟩
  · induction r with
    | zero => exact (cut_first hcs hC (by omega)).2.2.1
    | succ r ih =>
      have T := cut_trans hcs hC (r := r) (by omega)
      rw [T.2.2.2.2.2.1 (kinds (r + 1) hr).2.1, ih (by omega), (kinds r (by omega)).1, jF,
        ← Lean.Grind.Semiring.natCast_add, show r / 2 + r % 2 = (r + 1) / 2 by omega]
  · have T := cut_trans hcs hC (r := 2 * g) (by omega)
    have j0 : kc tr t (2 * g) 1 = 0 := by rw [(kinds (2 * g) (by omega)).1, jF, show 2 * g % 2 = 0 by omega]; rfl
    exact (T.1 (kinds (2 * g) (by omega)).2.1 j0).2.2.2
  · have T := cut_trans hcs hC (r := 2 * g + 1) (by omega)
    have j1 : kc tr t (2 * g + 1) 1 = 1 := by
      rw [(kinds (2 * g + 1) (by omega)).1, jF, show (2 * g + 1) % 2 = 1 by omega]; rfl
    exact T.2.2.2.2.2.2 j1 (kinds (2 * g + 2) (by omega)).2.1 i hi

end stream

/-! ## The CUT stream digest -/

/-- Read a field triple as a word `l0 + 2^21·l1 + 2^42·l2`. -/
def decW (x : List F) : Nat := (x.getD 0 0).toNat + 2 ^ 21 * (x.getD 1 0).toNat + 2 ^ 42 * (x.getD 2 0).toNat

theorem decW_wF {y : Nat} (hy : y < 2 ^ 64) : decW (wF y) = y := by
  have hP := P_val
  simp only [decW, wF, StateM5a.wlimbs, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  rw [Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega)]
  omega

/-- The chaining-value triple `k` (columns `h{3k} h{3k+1} h{3k+2}`) of row `r`. -/
def hwF (tr : Trace) (pub : List F) (t : Nat) (cs : List String) (r k : Nat) : List F :=
  ((wordsAt (Cut.c cs) "h" 8).getD k zeroW).map (·.eval (tr.row pub t r))

/-- The block-word triple `w` (`Cut.rowWords`) of row `r`. -/
def bwF (tr : Trace) (pub : List F) (t : Nat) (cs : List String) (r w : Nat) : List F :=
  ((Cut.rowWords cs).getD w zeroW).map (·.eval (tr.row pub t r))

/-- **The words a CUT row hashes** (its 8 block words, decoded). -/
def streamW (tr : Trace) (pub : List F) (t : Nat) (cs : List String) (r : Nat) : List Nat :=
  (List.range 8).map fun w => decW (bwF tr pub t cs r w)

theorem hwF_len (tr : Trace) (pub : List F) (t : Nat) (cs : List String) (r k : Nat) :
    (hwF tr pub t cs r k).length = 3 := by
  unfold hwF; rw [List.length_map, List.getD_eq_getElem?_getD]
  rcases h : (wordsAt (Cut.c cs) "h" 8)[k]? with _ | x
  · rfl
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? h); rfl

theorem bwF_len (tr : Trace) (pub : List F) (t : Nat) (cs : List String) (r w : Nat) :
    (bwF tr pub t cs r w).length = 3 := by
  unfold bwF; rw [List.length_map, List.getD_eq_getElem?_getD]
  rcases h : (Cut.rowWords cs)[w]? with _ | x
  · rfl
  · have hm := List.mem_of_getElem? h
    simp only [Cut.rowWords, List.mem_append, List.mem_map, List.mem_singleton] at hm
    rcases hm with ⟨k, -, rfl⟩ | rfl <;> rfl

theorem cast_pair (a b c : Nat) : ((a : Nat) : F) + ((b : Nat) : F) * ((c : Nat) : F) = ((a + b * c : Nat) : F) := by
  rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]

theorem range2_flatMap {α : Type} (f : Nat → List α) : ∀ N,
    (List.range (2 * N)).flatMap f = (List.range N).flatMap fun g => f (2 * g) ++ f (2 * g + 1)
  | 0 => rfl
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, List.range_succ, List.range_succ, List.flatMap_append,
      List.flatMap_append, range2_flatMap f N, List.range_succ (n := N), List.flatMap_append]
    simp [List.append_assoc]

theorem hwF_eq {tr : Trace} {pub : List F} {t : Nat} {cs : List String} (hcs : cs = Cut.In.cols ∨ cs = Cut.Out.cols)
    (r : Nat) {k : Nat} (hk : k < 8) :
    hwF tr pub t cs r k = [kc tr t r (23 + 3 * k), kc tr t r (23 + (3 * k + 1)), kc tr t r (23 + (3 * k + 2))] := by
  have ih := (cut_ixs hcs).2.2.2.2.2.2.2.2.2.1
  simp only [hwF, wordsAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some, List.map_cons, List.map_nil, kc_c]
  rw [ih _ (by omega), ih _ (by omega), ih _ (by omega)]

theorem bwF_eq {tr : Trace} {pub : List F} {t : Nat} {cs : List String} (hcs : cs = Cut.In.cols ∨ cs = Cut.Out.cols)
    (r : Nat) {w : Nat} (hw : w < 8) :
    bwF tr pub t cs r w =
      if w < 7 then [kc tr t r 0 * kc tr t r (5 + w), kc tr t r 0 * kc tr t r (12 + w),
        if w = 0 then kc tr t r 0 + kc tr t r 3 * (1 - kc tr t r 1) * ((2 ^ 21 : Nat) : F) else 0]
      else [kc tr t r 3 * kc tr t r 1 * ((1024 : Nat) : F) * kc tr t r 20, kc tr t r 3 * kc tr t r 1 * kc tr t r 21, 0] := by
  rcases hcs with rfl | rfl <;>
  match w, hw with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl

section digest
variable {nloc ngl : Nat} {t : Nat} {cs : List String} {base : Nat} {pub : List F} {tr : Trace}
  {chip : List StateM5a.Sha512If.IfMsg} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
  (hC : ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip)
  (hT : (t = 30 ∧ cs = Cut.In.cols ∧ base = pubCtxIn) ∨ (t = 31 ∧ cs = Cut.Out.cols ∧ base = pubCtxOut))

include hT in
theorem cutT_lt : t < (wasmBaseSegAir nloc ngl).tables.length := by
  rcases hT with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [seg_air_len]

include hT in
theorem cutT_cs : cs = Cut.In.cols ∨ cs = Cut.Out.cols := by
  rcases hT with ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact Or.inl h
  · exact Or.inr h

include hT in
theorem cutT_tab :
    (∀ e ∈ Cut.streamConstraints cs base, e ∈ ((wasmBaseSegAir nloc ngl).tables[t]'(cutT_lt hT)).constraints) ∧
    (∀ i ∈ Cut.ifInters cs, i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'(cutT_lt hT)).inters) ∧
    (∀ i ∈ Cut.padR16 cs, i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'(cutT_lt hT)).inters) := by
  rcases hT with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨fun e he => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;> rw [seg_t30]
    · exact he
    · simp only [Cut.In.table, List.mem_append]; left; right; exact hi
    · simp only [Cut.In.table, List.mem_append]; right; exact hi
  · refine ⟨fun e he => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;> rw [seg_t31']
    · simp only [Cut.Out.table, Cut.Out.constraints, List.mem_append]; left; left; exact he
    · simp only [Cut.Out.table, Cut.Out.inters, List.mem_append]; left; right; exact hi
    · simp only [Cut.Out.table, Cut.Out.inters, List.mem_append]; right; exact hi

include H hT in
theorem cutT_C : ∀ r, r < tr.height t → ∀ e ∈ Cut.streamConstraints cs base, e.eval (tr.row pub t r) = 0 :=
  fun r hr e he => H.constr t (cutT_lt hT) r hr e ((cutT_tab hT).1 e he)

include H hC hT in
/-- The 8 chip receives of a CUT row whose count `kD + kP` is 1 are chip messages. -/
theorem cut_msgs {r : Nat} (hr : r < tr.height t) (hcnt : kc tr t r 2 + kc tr t r 3 = 1) :
    (∀ i, i < 4 → (kc tr t r 22 :: (((i : Nat) : F) + ((12 : Nat) : F) * kc tr t r 1) ::
      (hwF tr pub t cs r (2 * i) ++ hwF tr pub t cs r (2 * i + 1))) ∈ chip.map ifF) ∧
    (∀ i, i < 4 → (kc tr t r 22 :: (((4 + i : Nat) : F) + ((4 : Nat) : F) * kc tr t r 1) ::
      (bwF tr pub t cs r (2 * i) ++ bwF tr pub t cs r (2 * i + 1))) ∈ chip.map ifF) := by
  obtain ⟨ia, ij, iD, iP, iX, igi, -, -, icid, -, -⟩ := cut_ixs (cutT_cs hT)
  have ht := cutT_lt (nloc := nloc) (ngl := ngl) hT
  have hc1 : ((Cut.c cs "kD" + Cut.c cs "kP").eval (tr.row pub t r)).toNat = 1 := by
    rw [Expr.eval_add', kc_c, kc_c, iD, iP, hcnt]; decide
  have mem : ∀ i ∈ Cut.ifInters cs, i.bus = busIf → i.count = Cut.c cs "kD" + Cut.c cs "kP" →
      i.msg.map (·.eval (tr.row pub t r)) ∈ chip.map ifF := by
    intro i hi hb hcount
    have hocc := occ_of_inter ht hr ((cutT_tab hT).2.1 i hi) (by rw [hcount]; exact hc1)
    exact if_recv_mem H hC hocc hb rfl
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := mem _ (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)) rfl rfl
    simpa [hwF, kc_c, ij, icid, List.map_append] using this
  · have := mem _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)) rfl rfl
    simpa [bwF, kc_c, ij, icid, List.map_append] using this

theorem iv_limbs' : ∀ k, k < 8 →
    [((ivLimbs.getD (3 * k) 0 : Nat) : F), ((ivLimbs.getD (3 * k + 1) 0 : Nat) : F), ((ivLimbs.getD (3 * k + 2) 0 : Nat) : F)] =
      wF (NearSpecV3.E2E.Bnd.IV384.getD k 0) := by
  intro k hk
  have e0 := iv_limbs k hk 0 (by decide)
  simp only [Nat.add_zero] at e0
  rw [← iv_eq', wF, e0, iv_limbs k hk 1 (by decide), iv_limbs k hk 2 (by decide)]
  rfl

theorem mem_congr {a b : List F} {L : List (List F)} (h : a ∈ L) (e : a = b) : b ∈ L := e ▸ h

include H hC hT in
/-- **One CUT group is one chip compression**: rows `2g` (`j = 0`: `h_in`, block words 0–7) and
`2g + 1` (`j = 1`: block words 8–15, `h_out`) under one `cid`. -/
theorem cut_group {g : Nat} (hr : 2 * g + 1 < tr.height t)
    (hj0 : kc tr t (2 * g) 1 = 0) (hj1 : kc tr t (2 * g + 1) 1 = 1)
    (hcid : kc tr t (2 * g + 1) 22 = kc tr t (2 * g) 22)
    (hc0 : kc tr t (2 * g) 2 + kc tr t (2 * g) 3 = 1) (hc1 : kc tr t (2 * g + 1) 2 + kc tr t (2 * g + 1) 3 = 1) :
    ∃ h blk : List Nat, h.length = 8 ∧ blk.length = 16 ∧ StateM5a.Sha512If.W64 h ∧ StateM5a.Sha512If.W64 blk ∧
      (∀ k, k < 8 → hwF tr pub t cs (2 * g) k = wF (h.getD k 0)) ∧
      (∀ w, w < 8 → bwF tr pub t cs (2 * g) w = wF (blk.getD w 0)) ∧
      (∀ w, w < 8 → bwF tr pub t cs (2 * g + 1) w = wF (blk.getD (8 + w) 0)) ∧
      (∀ k, k < 8 → hwF tr pub t cs (2 * g + 1) k = wF ((compressW h blk).getD k 0)) := by
  let W : Nat → List F := fun k =>
    if k < 8 then hwF tr pub t cs (2 * g) k else if k < 16 then bwF tr pub t cs (2 * g) (k - 8)
    else if k < 24 then bwF tr pub t cs (2 * g + 1) (k - 16) else hwF tr pub t cs (2 * g + 1) (k - 24)
  have hW3 : ∀ k, k < 32 → (W k).length = 3 := by
    intro k _; simp only [W]
    split
    · exact hwF_len ..
    · split
      · exact bwF_len ..
      · split
        · exact bwF_len ..
        · exact hwF_len ..
  obtain ⟨m0a, m0b⟩ := cut_msgs H hC hT (r := 2 * g) (by omega) hc0
  obtain ⟨m1a, m1b⟩ := cut_msgs H hC hT (r := 2 * g + 1) hr hc1
  have hin : ∀ m, m < 16 → (kc tr t (2 * g) 22 :: ((m : Nat) : F) :: (W (2 * m) ++ W (2 * m + 1))) ∈ chip.map ifF := by
    intro m hm
    rcases (by omega : m < 4 ∨ (4 ≤ m ∧ m < 8) ∨ (8 ≤ m ∧ m < 12) ∨ (12 ≤ m ∧ m < 16)) with h | h | h | h
    · refine mem_congr (m0a m h) ?_
      simp only [W, hj0, show 2 * m < 8 by omega, show 2 * m + 1 < 8 by omega, if_true]
      congr 2; grind
    · refine mem_congr (m0b (m - 4) (by omega)) ?_
      simp only [W, hj0, show ¬ 2 * m < 8 by omega, show ¬ 2 * m + 1 < 8 by omega, show 2 * m < 16 by omega,
        show 2 * m + 1 < 16 by omega, if_true, if_false, show 2 * m - 8 = 2 * (m - 4) by omega,
        show 2 * m + 1 - 8 = 2 * (m - 4) + 1 by omega]
      congr 2; rw [show m = 4 + (m - 4) by omega]; grind
    · refine mem_congr (m1b (m - 8) (by omega)) ?_
      simp only [W, hj1, hcid, show ¬ 2 * m < 8 by omega, show ¬ 2 * m + 1 < 8 by omega, show ¬ 2 * m < 16 by omega,
        show ¬ 2 * m + 1 < 16 by omega, show 2 * m < 24 by omega, show 2 * m + 1 < 24 by omega, if_true, if_false,
        show 2 * m - 16 = 2 * (m - 8) by omega, show 2 * m + 1 - 16 = 2 * (m - 8) + 1 by omega]
      congr 2; rw [← cast_one, cast_pair]; congr 1; omega
    · refine mem_congr (m1a (m - 12) (by omega)) ?_
      simp only [W, hj1, hcid, show ¬ 2 * m < 8 by omega, show ¬ 2 * m + 1 < 8 by omega, show ¬ 2 * m < 16 by omega,
        show ¬ 2 * m + 1 < 16 by omega, show ¬ 2 * m < 24 by omega, show ¬ 2 * m + 1 < 24 by omega, if_false,
        show 2 * m - 24 = 2 * (m - 12) by omega, show 2 * m + 1 - 24 = 2 * (m - 12) + 1 by omega]
      congr 2; rw [← cast_one, cast_pair]; congr 1; omega
  obtain ⟨h, blk, h8, h16, wh, wb, hW⟩ := consumer_sound compressW_ok hC.contract hC.cidLt hW3 hin
  refine ⟨h, blk, h8, h16, wh, wb, fun k hk => ?_, fun w hw => ?_, fun w hw => ?_, fun k hk => ?_⟩
  · have := hW k (by omega); simp only [W, hk, if_true] at this
    rw [this, words_getD_h h8 hk]
  · have := hW (8 + w) (by omega)
    simp only [W, show ¬ 8 + w < 8 by omega, show 8 + w < 16 by omega, if_true, if_false,
      show 8 + w - 8 = w by omega] at this
    rw [this, words_getD_b h8 h16 (by omega)]
  · have := hW (16 + w) (by omega)
    simp only [W, show ¬ 16 + w < 8 by omega, show ¬ 16 + w < 16 by omega, show 16 + w < 24 by omega, if_true,
      if_false, show 16 + w - 16 = w by omega] at this
    rw [this, show 16 + w = 8 + (8 + w) by omega, words_getD_b h8 h16 (by omega)]
  · have := hW (24 + k) (by omega)
    simp only [W, show ¬ 24 + k < 8 by omega, show ¬ 24 + k < 16 by omega, show ¬ 24 + k < 24 by omega,
      if_false, show 24 + k - 24 = k by omega] at this
    rw [this, words_getD_o h8 h16]

include H hC hT in
/-- **The CUT stream digest.**  A CUT table (CUTI with `ctx_in`, CUTO with `ctx_out`) has `2N` data
rows followed by the padding group, and its public digest limbs (`pub[base … base+18)`) are the
limbs of six 64-bit words `d` whose bytes are `sha384 (wbytes Ws)`, where `Ws` is the concatenation
of the 8 words every data row hashes (`streamW`, in row order; all `< 2^64`).  The padding block the
AIR hashes is exactly FIPS 180-4's for the `8·|Ws|`-byte message (`pad_whole`; `gi`, `gl`, `gh`). -/
theorem cut_stream_digest :
    ∃ N, 2 * N + 2 ≤ tr.height t ∧ (∀ r, r < 2 * N → kc tr t r 2 = 1) ∧
      (∀ w ∈ (List.range (2 * N)).flatMap (streamW tr pub t cs), w < 2 ^ 64) ∧
      ∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub base = limbsF d ∧
        wbytes d = NearSpecV3.E2E.Bnd.sha384 (wbytes ((List.range (2 * N)).flatMap (streamW tr pub t cs))) := by
  have hcs := cutT_cs hT
  have hC' := cutT_C H hT
  have ht := cutT_lt (nloc := nloc) (ngl := ngl) hT
  have hh : 4 ≤ tr.height t := H.heightPos t ht
  obtain ⟨N, hN, hd, hp0, hp1, rows, hcid, hch⟩ := cut_rows hcs hC' hh
  have hP := P_val
  have hle := H.heightLe t ht
  unfold maxLogHeight at hle
  -- counts and `j`
  have cnt : ∀ r, r ≤ 2 * N + 1 → kc tr t r 2 + kc tr t r 3 = 1 := by
    intro r hr
    obtain ⟨-, -, k, -⟩ := cut_bits hcs hC' (r := r) (by omega)
    have x := (rows r hr).2.1
    rcases k with ⟨a, b, -⟩ | ⟨a, b, -⟩ | ⟨-, -, c⟩
    · rw [a, b]; grind
    · rw [a, b]; grind
    · rw [x] at c; exact absurd c (by decide)
  have j0 : ∀ g, g ≤ N → kc tr t (2 * g) 1 = 0 := by
    intro g hg; rw [(rows (2 * g) (by omega)).1, jF, show 2 * g % 2 = 0 by omega]; rfl
  have j1 : ∀ g, g ≤ N → kc tr t (2 * g + 1) 1 = 1 := by
    intro g hg; rw [(rows (2 * g + 1) (by omega)).1, jF, show (2 * g + 1) % 2 = 1 by omega]; rfl
  have grp := fun g (hg : g ≤ N) => cut_group H hC hT (g := g) (by omega) (j0 g hg) (j1 g hg) (hcid g hg)
    (cnt _ (by omega)) (cnt _ (by omega))
  -- a group's block is the two rows' decoded words
  let Bk : Nat → List Nat := fun g => streamW tr pub t cs (2 * g) ++ streamW tr pub t cs (2 * g + 1)
  have getw : ∀ (l : List Nat), StateM5a.Sha512If.W64 l → ∀ k, l.getD k 0 < 2 ^ 64 := by
    intro l hl k
    rw [List.getD_eq_getElem?_getD]
    rcases e : l[k]? with _ | w
    · simp
    · exact hl w (List.mem_of_getElem? e)
  have blkEq : ∀ g, g ≤ N → ∀ blk : List Nat, blk.length = 16 → StateM5a.Sha512If.W64 blk →
      (∀ w, w < 8 → bwF tr pub t cs (2 * g) w = wF (blk.getD w 0)) →
      (∀ w, w < 8 → bwF tr pub t cs (2 * g + 1) w = wF (blk.getD (8 + w) 0)) → blk = Bk g := by
    intro g _ blk h16 wb e0 e1
    apply List.ext_getElem (by simp [Bk, streamW, h16]); intro k hk1 hk2
    have gk : blk[k] = blk.getD k 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]
    rw [gk]
    simp only [Bk, streamW]
    by_cases hk : k < 8
    · rw [List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_range, e0 k hk,
        decW_wF (getw blk wb k)]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      rw [e1 (k - 8) (by omega), show 8 + (k - 8) = k by omega, decW_wF (getw blk wb k)]
  let Hf : Nat → List Nat := fun g => ((List.range g).map Bk).foldl compressW NearSpecV3.E2E.Bnd.IV384
  have Hok : ∀ g, (Hf g).length = 8 ∧ StateM5a.Sha512If.W64 (Hf g) := fun g => foldl_ok _ _ iv_ok.1 iv_ok.2
  have claim : ∀ g, g ≤ N → ∀ k, k < 8 → hwF tr pub t cs (2 * g) k = wF ((Hf g).getD k 0) := by
    intro g
    induction g with
    | zero =>
      intro _ k hk
      rw [hwF_eq hcs 0 hk]
      have f := (cut_first hcs hC' (by omega)).2.2.2
      rw [f _ (by omega), f _ (by omega), f _ (by omega), iv_limbs' k hk]
      rfl
    | succ g ih =>
      intro hg k hk
      obtain ⟨h, blk, h8, h16, wh, wb, eh, e0, e1, eo⟩ := grp g (by omega)
      have hh' : h = Hf g := list_eq_of_wF h8 (Hok g).1 wh (Hok g).2 (fun k hk => by
        rw [← eh k hk, ih (by omega) k hk])
      have hb := blkEq g (by omega) blk h16 wb e0 e1
      have step : hwF tr pub t cs (2 * (g + 1)) k = hwF tr pub t cs (2 * g + 1) k := by
        rw [hwF_eq hcs _ hk, hwF_eq hcs _ hk, show 2 * (g + 1) = 2 * g + 2 by omega,
          hch g (by omega) _ (by omega), hch g (by omega) _ (by omega), hch g (by omega) _ (by omega)]
      rw [step, eo k hk, hh', hb]
      simp only [Hf, List.range_succ, List.map_append, List.foldl_append, List.map_cons, List.map_nil,
        List.foldl_cons, List.foldl_nil]
  -- the padding group
  obtain ⟨h, blk, h8, h16, wh, wb, eh, e0, e1, eo⟩ := grp N (Nat.le_refl _)
  have hh' : h = Hf N := list_eq_of_wF h8 (Hok N).1 wh (Hok N).2 (fun k hk => by rw [← eh k hk, claim N (by omega) k hk])
  have hb := blkEq N (Nat.le_refl _) blk h16 wb e0 e1
  -- `gl`, `gh` and the length word
  obtain ⟨ia, ij, iD, iP, iX, igi, igl, igh, icid, ih, -⟩ := cut_ixs hcs
  have r1 : 2 * N + 1 < tr.height t := by omega
  have kD1 : kc tr t (2 * N + 1) 2 = 0 := by
    have := cnt _ (Nat.le_refl _); rw [hp1] at this; grind
  have kD0 : kc tr t (2 * N) 2 = 0 := by
    have := cnt (2 * N) (by omega); rw [hp0] at this; grind
  have act1 := (cut_bits hcs hC' (r := 2 * N + 1) r1).2.2.2 kD1
  have act0 := (cut_bits hcs hC' (r := 2 * N) (by omega)).2.2.2 kD0
  have g1 : ((Cut.c cs "kP" * Cut.c cs "j").eval (tr.row pub t (2 * N + 1))).toNat = 1 := by
    rw [Expr.eval_mul', kc_c, kc_c, iP, ij, hp1, j1 N (Nat.le_refl _)]; decide
  have q : ∀ e, r16 e (Cut.c cs "kP" * Cut.c cs "j") ∈ Cut.padR16 cs → (e.eval (tr.row pub t (2 * N + 1))).toNat < 65536 :=
    fun e he => seg_r16_lt H (seg_hsend_r16 H) ht r1 ((cutT_tab hT).2.2 _ he) g1
  have q1 := q (32 * Cut.c cs "gl") (by simp [Cut.padR16])
  have q2 := q (Cut.c cs "gh") (by simp [Cut.padR16])
  have q3 := q (Cut.c cs "gl") (by simp [Cut.padR16])
  simp only [Expr.eval_mul', Expr.eval_ofNat', kc_c, igl, igh] at q1 q2 q3
  rw [← Fp.cast_toNat (kc tr t (2 * N + 1) 20), mulq_toNat (by omega)] at q1
  have hgi := hC' (2 * N + 1) r1 (Cut.c cs "kP" * Cut.c cs "j" * (Cut.c cs "gi" - Cut.c cs "gl" - 2048 * Cut.c cs "gh"))
    (by simp [Cut.streamConstraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', kc_c, iP, ij, igi, igl, igh, hp1, j1 N (Nat.le_refl _),
    (rows (2 * N + 1) (Nat.le_refl _)).2.2.2, show (2 * N + 1) / 2 = N by omega] at hgi
  have hNg : N = (kc tr t (2 * N + 1) 20).toNat + 2048 * (kc tr t (2 * N + 1) 21).toNat := by
    have e : ((N : Nat) : F) = (((kc tr t (2 * N + 1) 20).toNat + 2048 * (kc tr t (2 * N + 1) 21).toNat : Nat) : F) := by
      rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat, Fp.cast_toNat]
      grind
    exact natEq e (by omega) (by omega)
  have z : ∀ x : F, 0 * x = 0 := by intro x; grind
  have toN0 : (0 : F).toNat = 0 := rfl
  have w0 : (0 : F) + 1 * (1 - 0) * ((2 ^ 21 : Nat) : F) = ((2 ^ 21 : Nat) : F) := by grind
  have w0' : (0 : F) + 1 * (1 - 1) * ((2 ^ 21 : Nat) : F) = 0 := by grind
  have gl' : kc tr t (2 * N + 1) 20 = (((kc tr t (2 * N + 1) 20).toNat : Nat) : F) := (Fp.cast_toNat _).symm
  have w7 : (1 : F) * 1 * ((1024 : Nat) : F) * kc tr t (2 * N + 1) 20 =
      ((1024 * (kc tr t (2 * N + 1) 20).toNat : Nat) : F) := by
    rw [Lean.Grind.Semiring.natCast_mul, ← gl']; grind
  have w7' : (1 : F) * 1 * kc tr t (2 * N + 1) 21 = kc tr t (2 * N + 1) 21 := by grind
  have w7z : (1 : F) * 0 * ((1024 : Nat) : F) * kc tr t (2 * N) 20 = 0 := by grind
  have w7z' : (1 : F) * 0 * kc tr t (2 * N) 21 = 0 := by grind
  have range8 : ∀ (f : Nat → Nat), (List.range 8).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := fun f => rfl
  have sw0 : streamW tr pub t cs (2 * N) = [2 ^ 63, 0, 0, 0, 0, 0, 0, 0] := by
    rw [streamW, range8]
    simp only [bwF_eq hcs (2 * N) (show (0 : Nat) < 8 by decide), bwF_eq hcs (2 * N) (show (1 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N) (show (2 : Nat) < 8 by decide), bwF_eq hcs (2 * N) (show (3 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N) (show (4 : Nat) < 8 by decide), bwF_eq hcs (2 * N) (show (5 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N) (show (6 : Nat) < 8 by decide), bwF_eq hcs (2 * N) (show (7 : Nat) < 8 by decide),
      kD0, hp0, act0, j0 N (Nat.le_refl _), z, w0, w7z, w7z']
    simp only [decW, List.getD_cons_zero, List.getD_cons_succ, toN0, Fp.toNat_cast_of_lt (show 2 ^ 21 < P by omega)]
    decide
  have sw1 : streamW tr pub t cs (2 * N + 1) = [0, 0, 0, 0, 0, 0, 0, 1024 * N] := by
    rw [streamW, range8]
    simp only [bwF_eq hcs (2 * N + 1) (show (0 : Nat) < 8 by decide), bwF_eq hcs (2 * N + 1) (show (1 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N + 1) (show (2 : Nat) < 8 by decide), bwF_eq hcs (2 * N + 1) (show (3 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N + 1) (show (4 : Nat) < 8 by decide), bwF_eq hcs (2 * N + 1) (show (5 : Nat) < 8 by decide),
      bwF_eq hcs (2 * N + 1) (show (6 : Nat) < 8 by decide), bwF_eq hcs (2 * N + 1) (show (7 : Nat) < 8 by decide),
      kD1, hp1, act1, j1 N (Nat.le_refl _), z, w0', w7, w7']
    simp only [decW, List.getD_cons_zero, List.getD_cons_succ, toN0, ↓reduceIte, Nat.reduceLT, ite_true, ite_false, ite_self,
      Fp.toNat_cast_of_lt (show 1024 * (kc tr t (2 * N + 1) 20).toNat < P by omega)]
    simp only [Nat.mul_zero, Nat.add_zero, List.cons.injEq, and_true, true_and]
    omega
  have hpad : Bk N = padBlk (1024 * N) := by
    simp only [Bk, sw0, sw1, padBlk, show 1024 * N / 2 ^ 64 % 2 ^ 64 = 0 by omega,
      show 1024 * N % 2 ^ 64 = 1024 * N by omega]
    rfl
  -- the digest
  let out := compressW (Hf N) (Bk N)
  have hco := compressW_ok (Hf N) (Bk N)
  have hfin : ∀ k, k < 8 → hwF tr pub t cs (2 * N + 1) k = wF (out.getD k 0) := by
    intro k hk; rw [eo k hk, hh', hb]
  have h6 : (out.take 6).length = 6 := by rw [List.length_take, show out.length = 8 from hco.1]; rfl
  have hBk : ∀ g, g < N → (Bk g).length = 16 ∧ StateM5a.Sha512If.W64 (Bk g) := by
    intro g hg
    obtain ⟨-, blk', -, h16', -, wb', -, e0', e1', -⟩ := grp g (by omega)
    have := blkEq g (by omega) blk' h16' wb' e0' e1'
    rw [← this]; exact ⟨h16', wb'⟩
  have hWs : (List.range (2 * N)).flatMap (streamW tr pub t cs) = ((List.range N).map Bk).flatten := by
    rw [range2_flatMap, List.flatMap_def]
  have hlen : ((List.range N).map Bk).flatten.length = 16 * N := by
    rw [List.length_flatten, List.map_map]
    have : ((List.range N).map (List.length ∘ Bk)) = List.replicate N 16 := by
      apply List.ext_getElem (by simp); intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, Function.comp]
      exact (hBk i (by simpa using h1)).1
    rw [this]
    clear this
    induction N with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, List.sum_cons]; omega
  refine ⟨N, hN, hd, ?_, out.take 6, h6, fun w hw => hco.2 w (List.mem_of_mem_take hw), ?_, ?_⟩
  · intro w hw
    rw [hWs] at hw
    obtain ⟨B, hB, hwB⟩ := List.mem_flatten.1 hw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hB
    exact (hBk g (List.mem_range.1 hg)).2 w hwB
  · have hpub : ∀ i, i < 18 → pub.getD (base + i) 0 = kc tr t (2 * N + 1) (23 + i) := by
      intro i hi
      have e := hC' (2 * N + 1) r1 (Cut.c cs "kP" * Cut.c cs "j" * (Cut.c cs s!"h{i}" - pv (base + i))) (by
        simp only [Cut.streamConstraints, List.mem_append]
        right
        exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
      simp only [Expr.eval_mul', Expr.eval_sub', kc_c, iP, ij, ih i (by omega), hp1, j1 N (Nat.le_refl _),
        pv, Expr.eval_pub] at e
      have e' : ∀ x y : F, 1 * 1 * (x - y) = 0 → y = x := by intro x y h; grind
      exact e' _ _ e
    have hf := flat_triples (out.take 6) (fun i => kc tr t (2 * N + 1) (23 + i)) (fun k hk6 => by
      have hk6' : k < 6 := by rw [h6] at hk6; exact hk6
      rw [show (out.take 6).getD k 0 = out.getD k 0 by
        simp [List.getD_eq_getElem?_getD, List.getElem?_take, hk6'], ← hfin k (by omega), hwF_eq hcs _ (by omega)]
      rfl)
    rw [h6] at hf
    rw [← hf]
    simp only [pubDig]
    apply List.map_congr_left; intro i hi
    exact hpub i (List.mem_range.1 hi)
  · rw [hWs, sha384_whole N _ hlen]
    have hc : chunks16 N ((List.range N).map Bk).flatten = (List.range N).map Bk := by
      have := chunks16_flatten ((List.range N).map Bk) (fun B hB => by
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hB
        exact (hBk g (List.mem_range.1 hg)).1)
      simpa using this
    rw [hc, ← hpad]

end digest

end SegSha

#print axioms SegSha.cuto_filler_counterexample
#print axioms SegSha.cut_shape
#print axioms SegSha.cut_group
#print axioms SegSha.cut_stream_digest

end WasmBase
