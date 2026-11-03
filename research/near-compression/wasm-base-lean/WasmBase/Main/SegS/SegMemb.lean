import WasmBase.Main.SegMemb
import WasmBase.Main.SegS.SegRows
/-!
# WasmBase.Main.SegS.SegMemb — `SegMemb`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegMemb.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- `p8` is a bit on a MEMB row. -/
theorem memb_p_bitS {r : Nat} (hr : r < tr.height 19) {i : Nat} (hi : i < 9) :
    bc tr r (1 + i) = 0 ∨ bc tr r (1 + i) = 1 := by
  have h := H.constr 19 (by simp [seg_air_len]) r hr (Chips.bool (Memb.p i))
    (by
      rw [seg_t19]
      show _ ∈ Memb.constraints
      unfold Memb.constraints
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ ?_))))))))
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  simp only [Chips.bool, Memb.p, Memb.c, mb_ix_p i hi, Expr.eval_mul', Expr.eval_sub', v, Expr.eval_col,
    Expr.eval_ofNat', Trace.row] at h
  exact bool_cases (by simpa [cast_one] using h)

end

/-- An R16 query with count 1 on a segment trace is `< 2^16`, given the R16 send bound `hsend`. -/
theorem seg_r16_ltS {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) {r : Nat} (hr : r < tr.height t)
    {e c : Expr} (hi : r16 e c ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) :
    (e.eval (tr.row pub t r)).toNat < 65536 := by
  have hocc := occ_of_inter ht hr hi hc
  obtain ⟨x, hx, hxl⟩ := lookup_r16GXS H hsend (regG_r16_recvXS H (regAt_seg nloc ngl)) hocc rfl rfl rfl
  simp only [r16, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
  rw [hx]; exact hxl

theorem memb_CS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {r : Nat} (hr : r < tr.height 19) : ∀ e ∈ Memb.constraints, e.eval (tr.row pub 19 r) = 0 := by
  intro e he
  exact H.constr 19 (by simp [seg_air_len]) r hr e (by rw [seg_t19]; exact he)

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- **A MEMB row as naturals**: `act` and the nine position flags are bits, and they sum to `act`. -/
theorem memb_rowS {r : Nat} (hr : r < tr.height 19) :
    mbN tr r 0 ≤ 1 ∧ (∀ i, i < 9 → mbN tr r (1 + i) ≤ 1) ∧
      mbN tr r 1 + mbN tr r 2 + mbN tr r 3 + mbN tr r 4 + mbN tr r 5 + mbN tr r 6 + mbN tr r 7 +
        mbN tr r 8 + mbN tr r 9 = mbN tr r 0 := by
  have C := memb_CS H hr
  have ha := C (Chips.bool (Memb.c "act")) (by simp [Memb.constraints])
  rw [Chips.bool, Expr.eval_mul', Expr.eval_sub', memb_c_eval, mb_ix.1, Expr.eval_ofNat'] at ha
  have ba := bool_nat (rowNat_lt tr 19 r 0) ha
  have bp : ∀ i, i < 9 → mbN tr r (1 + i) ≤ 1 := by
    intro i hi
    rcases memb_p_bitS H hr hi with h | h
    · have := natEq (R := 0) (show ((mbN tr r (1 + i) : Nat) : F) = ((0 : Nat) : F) by rw [← cell_cast]; exact h)
        (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
      omega
    · have := natEq (R := 1) (show ((mbN tr r (1 + i) : Nat) : F) = ((1 : Nat) : F) by rw [← cell_cast]; exact h)
        (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
      omega
  have ha1 : mbN tr r 0 ≤ 1 := by rcases ba with h | h <;> (show rowNat tr 19 r 0 ≤ 1; omega)
  refine ⟨ha1, bp, ?_⟩
  have hs := C (sumE ((List.range 9).map Memb.p) - Memb.c "act") (by simp [Memb.constraints])
  have e9 : sumE ((List.range 9).map Memb.p) =
      0 + Memb.p 0 + Memb.p 1 + Memb.p 2 + Memb.p 3 + Memb.p 4 + Memb.p 5 + Memb.p 6 + Memb.p 7 + Memb.p 8 := rfl
  rw [e9] at hs
  simp only [Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
    memb_p_eval tr pub r (show 0 < 9 by decide), memb_p_eval tr pub r (show 1 < 9 by decide),
    memb_p_eval tr pub r (show 2 < 9 by decide), memb_p_eval tr pub r (show 3 < 9 by decide),
    memb_p_eval tr pub r (show 4 < 9 by decide), memb_p_eval tr pub r (show 5 < 9 by decide),
    memb_p_eval tr pub r (show 6 < 9 by decide), memb_p_eval tr pub r (show 7 < 9 by decide),
    memb_p_eval tr pub r (show 8 < 9 by decide)] at hs
  have b1 : mbN tr r 1 ≤ 1 := bp 0 (by decide)
  have b2 : mbN tr r 2 ≤ 1 := bp 1 (by decide)
  have b3 : mbN tr r 3 ≤ 1 := bp 2 (by decide)
  have b4 : mbN tr r 4 ≤ 1 := bp 3 (by decide)
  have b5 : mbN tr r 5 ≤ 1 := bp 4 (by decide)
  have b6 : mbN tr r 6 ≤ 1 := bp 5 (by decide)
  have b7 : mbN tr r 7 ≤ 1 := bp 6 (by decide)
  have b8 : mbN tr r 8 ≤ 1 := bp 7 (by decide)
  have b9 : mbN tr r 9 ≤ 1 := bp 8 (by decide)
  simp only [mbN] at b1 b2 b3 b4 b5 b6 b7 b8 b9 ha1 ⊢
  have hP := P_val
  refine natEq ?_ (by omega) (rowNat_lt _ _ _ _)
  simp only [Lean.Grind.Semiring.natCast_add]
  grind

/-- The position flag of an active row is one-hot: `p_k = 1` forces every other flag to 0. -/
theorem memb_onehotS {r : Nat} (hr : r < tr.height 19) {k j : Nat} (hk : k < 9) (hj : j < 9) (hkj : k ≠ j)
    (hpk : mbN tr r (1 + k) = 1) : mbN tr r (1 + j) = 0 := by
  obtain ⟨ha, bp, hs⟩ := memb_rowS H hr
  have := bp j hj
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> omega

/-- **The block walk.**  Active rows form a prefix, and active row `r` is row `r mod 9` of its block:
`p_{r mod 9} = 1`. -/
theorem memb_posS : ∀ r, r < tr.height 19 → mbN tr r 0 = 1 →
    (∀ r', r' ≤ r → mbN tr r' 0 = 1) ∧ mbN tr r (1 + r % 9) = 1 := by
  intro r
  induction r with
  | zero =>
    intro hr ha
    refine ⟨fun r' h => by rw [show r' = 0 by omega]; exact ha, ?_⟩
    have h := memb_CS H hr (Expr.first * Memb.c "act" * (1 - Memb.p 0)) (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
      memb_p_eval tr pub 0 (show 0 < 9 by decide), ha] at h
    simp only [Expr.eval, Trace.row, beq_self_eq_true, ite_true] at h
    show mbN tr 0 (1 + 0) = 1
    exact natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
  | succ r ih =>
    intro hr ha
    -- the previous row is active (`trans·(1 − act)·nxt.act = 0`)
    have hpre := memb_CS H (r := r) (by omega) (Expr.trans * (1 - Memb.c "act") * Memb.n "act")
      (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
      memb_n_eval tr pub r hr, trans_eval_one tr pub 19 r hr, ha, cast_one] at hpre
    have ha0 : mbN tr r 0 = 1 :=
      natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
    obtain ⟨hpref, hp⟩ := ih (by omega) ha0
    refine ⟨fun r' h => by
      rcases (by omega : r' ≤ r ∨ r' = r + 1) with h' | rfl
      · exact hpref r' h'
      · exact ha, ?_⟩
    have hm : r % 9 < 9 := Nat.mod_lt _ (by decide)
    by_cases h8 : r % 9 = 8
    · -- the next row after a padding row starts a block
      rw [h8] at hp
      have h := memb_CS H (r := r) (by omega) (Expr.trans * Memb.p 8 * Memb.n "act" * (1 - Memb.n "p0"))
        (by simp [Memb.constraints])
      simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_p_eval tr pub r (show 8 < 9 by decide),
        memb_n_eval tr pub r hr, mb_ix.1, trans_eval_one tr pub 19 r hr, hp, ha, cast_one] at h
      rw [mb_ix_p0] at h
      have : (r + 1) % 9 = 0 := by omega
      rw [this]
      exact natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
    · have hlt : r % 9 < 8 := by omega
      have hmem : Expr.trans * Memb.p (r % 9) * (1 - nv (ix Memb.cols s!"p{r % 9 + 1}")) ∈ Memb.constraints := by
        unfold Memb.constraints
        refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))))))
        exact List.mem_map.mpr ⟨r % 9, List.mem_range.mpr hlt, rfl⟩
      have h := memb_CS H (r := r) (by omega) _ hmem
      rw [mb_ix_p (r % 9 + 1) (by omega)] at h
      simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_p_eval tr pub r hm, nv,
        Expr.eval_nxt, trans_eval_one tr pub 19 r hr, hp, cast_one] at h
      simp only [Trace.row, Nat.mod_eq_of_lt hr, cell_cast] at h
      have : (r + 1) % 9 = r % 9 + 1 := by omega
      rw [this, show 1 + (r % 9 + 1) = 1 + (r % 9 + 1) from rfl]
      exact natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)

/-- **`blk` is constant inside a block**: rows `9b … 9b+8` carry the padding row's `blk`. -/
theorem memb_blk_constS {b : Nat} (hr : 9 * b + 8 < tr.height 19) (ha : mbN tr (9 * b + 8) 0 = 1) :
    ∀ k, k ≤ 8 → mbN tr (9 * b + k) 10 = mbN tr (9 * b + 8) 10 := by
  have step : ∀ k, k < 8 → mbN tr (9 * b + k + 1) 10 = mbN tr (9 * b + k) 10 := by
    intro k hk
    have hr1 : 9 * b + k + 1 < tr.height 19 := by omega
    have ha1 := (memb_posS H (9 * b + 8) hr ha).1 (9 * b + k + 1) (by omega)
    have hp := (memb_posS H (9 * b + k + 1) hr1 ha1).2
    have hmod : (9 * b + k + 1) % 9 = k + 1 := by omega
    rw [hmod] at hp
    have hp0 : mbN tr (9 * b + k + 1) (1 + 0) = 0 := memb_onehotS H hr1 (k := k + 1) (by omega) (by decide) (by omega) hp
    have h := memb_CS H (r := 9 * b + k) (by omega)
      (Expr.trans * Memb.n "act" * (1 - Memb.n "p0") * (Memb.n "blk" - Memb.c "blk")) (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_n_eval tr pub _ hr1, memb_c_eval,
      trans_eval_one tr pub 19 _ hr1, mb_ix.1, mb_ix.2.1, mb_ix_p0, ha1, cast_one] at h
    rw [show (1 : Nat) = 1 + 0 from rfl, hp0] at h
    exact natEq (by grind) (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _)
  intro k hk
  induction k with
  | zero =>
    -- walk up from 0 to 8
    have : ∀ j, j ≤ 8 → mbN tr (9 * b + j) 10 = mbN tr (9 * b) 10 := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ihj => rw [← ihj (by omega)]; exact step j (by omega)
    exact (this 8 (Nat.le_refl _)).symm
  | succ k ihk =>
    rw [← ihk (by omega)]; exact step k (by omega)

/-- **Consecutive blocks have strictly increasing `blk`** (from `R16(nxt.blk − blk − 1)` at the
padding row and `blk < 2^16` on both padding rows). -/
theorem memb_blk_stepS
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {b : Nat} (hr : 9 * (b + 1) + 8 < tr.height 19) (ha : mbN tr (9 * (b + 1) + 8) 0 = 1) :
    mbN tr (9 * b + 8) 10 < mbN tr (9 * (b + 1) + 8) 10 ∧ mbN tr (9 * (b + 1) + 8) 10 < 65536 := by
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hpref := (memb_posS H _ hr ha).1
  have hr8 : 9 * b + 8 < tr.height 19 := by omega
  have ha8 := hpref (9 * b + 8) (by omega)
  have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
    have := (memb_posS H _ hr8 ha8).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
  have hp8' : mbN tr (9 * (b + 1) + 8) (1 + 8) = 1 := by
    have := (memb_posS H _ hr ha).2; rwa [show (9 * (b + 1) + 8) % 9 = 8 by omega] at this
  have hn1 : 9 * b + 8 + 1 < tr.height 19 := by omega
  have ha9 := hpref (9 * b + 9) (by omega)
  have hp9 : mbN tr (9 * b + 8 + 1) (1 + 0) = 1 := by
    have := (memb_posS H (9 * b + 9) (by omega) ha9).2
    rwa [show (9 * b + 9) % 9 = 0 by omega] at this
  -- the R16 queries of MEMB's last three interactions
  have mem : ∀ x ∈ [r16 (Memb.n "blk" - Memb.c "blk" - 1) (.trans * Memb.p 8 * Memb.n "p0"),
      r16 (Memb.c "blk") (Memb.p 8)], x ∈ ((wasmBaseSegAir nloc ngl).tables[19]'ht).inters := by
    intro x hx
    rw [seg_t19]
    show x ∈ Memb.inters
    unfold Memb.inters
    refine List.mem_append_right _ ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
    rcases hx with rfl | rfl
    · right; left; rfl
    · right; right; left; rfl
  have cP8 : ∀ r, r < tr.height 19 → mbN tr r (1 + 8) = 1 → ((Memb.p 8).eval (tr.row pub 19 r)).toNat = 1 := by
    intro r _ h; rw [memb_p_eval tr pub r (by decide), h]; decide
  have hb0 := seg_r16_ltS H hsend ht hr8 (mem (r16 (Memb.c "blk") (Memb.p 8)) (by simp)) (cP8 _ hr8 hp8)
  have hb1 := seg_r16_ltS H hsend ht hr (mem (r16 (Memb.c "blk") (Memb.p 8)) (by simp)) (cP8 _ hr hp8')
  have hgap := seg_r16_ltS H hsend ht hr8 (mem (r16 (Memb.n "blk" - Memb.c "blk" - 1) (.trans * Memb.p 8 * Memb.n "p0")) (by simp)) (by
    simp only [Expr.eval_mul', memb_p_eval tr pub _ (show 8 < 9 by decide), memb_n_eval tr pub _ hn1,
      trans_eval_one tr pub 19 _ hn1, hp8, mb_ix_p0]
    rw [show (1 : Nat) = 1 + 0 from rfl, hp9, cast_one]
    decide)
  simp only [memb_c_eval, mb_ix.2.1, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at hb0 hb1
  simp only [Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, memb_n_eval tr pub _ hn1, mb_ix.2.1] at hgap
  -- `blk` of row `9b + 9` is the next block's (`memb_blk_constS`)
  have hc := memb_blk_constS H (b := b + 1) hr ha 0 (by decide)
  rw [show 9 * (b + 1) + 0 = 9 * b + 8 + 1 by omega] at hc
  rw [hc] at hgap
  simp only [mbN] at hb0 hb1 hgap ⊢
  generalize rowNat tr 19 (9 * b + 8) 10 = x at hb0 hgap ⊢
  generalize rowNat tr 19 (9 * (b + 1) + 8) 10 = y at hb1 hgap ⊢
  have hP := P_val
  refine ⟨Nat.lt_of_not_le fun hle => ?_, hb1⟩
  -- then `y − x − 1 ≡ P − (x − y) − 1` has `toNat ≥ P − 2^16 > 2^16`
  have e : ((y : Nat) : F) - ((x : Nat) : F) - ((1 : Nat) : F) = ((P - (x - y) - 1 : Nat) : F) := by
    have h1 : ((P - (x - y) - 1 : Nat) : F) + ((x - y : Nat) : F) + 1 = ((P : Nat) : F) := by
      rw [← cast_one, ← Lean.Grind.Semiring.natCast_add, ← Lean.Grind.Semiring.natCast_add]
      congr 1; omega
    have h2 : ((P : Nat) : F) = 0 := by rw [← Fp.cast_toNat 0]; rfl
    have h3 : ((x - y : Nat) : F) + ((y : Nat) : F) = ((x : Nat) : F) := by
      rw [← Lean.Grind.Semiring.natCast_add]; congr 1; omega
    grind
  rw [e, Fp.toNat_cast_of_lt (by omega)] at hgap
  omega

/-- **The padding rows' `blk` values strictly increase**: block `b` before block `b'` (both active)
has a smaller `blk`. -/
theorem memb_blk_strictS
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1) :
    ∀ b d, 9 * (b + d + 1) + 8 < tr.height 19 → mbN tr (9 * (b + d + 1) + 8) 0 = 1 →
      mbN tr (9 * b + 8) 10 < mbN tr (9 * (b + d + 1) + 8) 10 := by
  intro b d
  induction d with
  | zero => intro hr ha; exact (memb_blk_stepS H hsend hr ha).1
  | succ d ih =>
    intro hr ha
    have hpref := (memb_posS H _ hr ha).1
    have ha' := hpref (9 * (b + d + 1) + 8) (by omega)
    have := ih (by omega) ha'
    have := (memb_blk_stepS H hsend (b := b + d + 1) (by omega) (by simpa [Nat.add_assoc] using ha)).1
    rw [show b + (d + 1) + 1 = b + d + 1 + 1 by omega]
    omega

/-- **Touched blocks are distinct.** -/
theorem memb_blk_distinctS
    (hsend : ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {b b' : Nat} (hb : b ≠ b') (hr : 9 * b + 8 < tr.height 19) (hr' : 9 * b' + 8 < tr.height 19)
    (ha : mbN tr (9 * b + 8) 0 = 1) (ha' : mbN tr (9 * b' + 8) 0 = 1) :
    mbN tr (9 * b + 8) 10 ≠ mbN tr (9 * b' + 8) 10 := by
  rcases Nat.lt_or_gt_of_ne hb with h | h
  · have := memb_blk_strictS H hsend b (b' - b - 1) (by rw [show b + (b' - b - 1) + 1 = b' by omega]; exact hr')
      (by rw [show b + (b' - b - 1) + 1 = b' by omega]; exact ha')
    rw [show b + (b' - b - 1) + 1 = b' by omega] at this
    omega
  · have := memb_blk_strictS H hsend b' (b - b' - 1) (by rw [show b' + (b - b' - 1) + 1 = b by omega]; exact hr)
      (by rw [show b' + (b - b' - 1) + 1 = b by omega]; exact ha)
    rw [show b' + (b - b' - 1) + 1 = b by omega] at this
    omega

end

end WasmBase
