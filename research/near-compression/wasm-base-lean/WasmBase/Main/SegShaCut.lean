import WasmBase.Main.SegShaMemb

/-!
# WasmBase.Main.SegShaCut — the CUT stream's digest, and a canonicity gap in CUTO's filler (E2E M4b)

CUTO hashes the consumed small-state messages two per SHA-512 block (8 words each: the 7 fields as
`lo + 2^21·hi + 2^42·mark` and a zero word); an odd count is completed by one **filler** row
(`kD = 1`, `act = 0`, `j = 1`), then the padding group (`kP`).  `cutWords L` (`Main/SegRows.lean`)
completes the last block with the all-zero message, and `cutDigest L = sha384 (cutBytes L)`.

**The filler row is not forced to zero** (`cuto_filler_counterexample`).  On a filler row every
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
1024·gi` with `gl < 2^11`, `gh < 2^16`, and `gi` the number of data groups.
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

/-- **CUTO's filler row is not forced to the zero message.**  `cexRow` satisfies every CUTO
constraint, every interaction of CUTO other than the chip's (bus 103) has count 0 on it, the chip
receives have count 1, and the eight block words it hashes are not all zero (word 1 is `[1, 0, 0]`,
i.e. the 64-bit word 1). -/
theorem cuto_filler_counterexample :
    (∀ e ∈ Cut.Out.constraints, e.eval cexRow = 0) ∧
    (∀ i ∈ Cut.Out.inters, i.bus ≠ busIf → i.count.eval cexRow = 0) ∧
    (∀ i ∈ Cut.Out.inters, i.bus = busIf → i.count.eval cexRow = 1) ∧
    (Cut.Out.c "act").eval cexRow = 0 ∧ (Cut.Out.c "kD").eval cexRow = 1 ∧ (Cut.Out.c "j").eval cexRow = 1 ∧
    (Cut.Out.n "kP").eval cexRow = 1 ∧
    (Cut.rowWords Cut.Out.cols).map (·.map (·.eval cexRow)) =
      [[0, 0, 0], [1, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]] := by
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

end stream

end SegSha

#print axioms SegSha.cuto_filler_counterexample

end WasmBase
