import ZkFormal.NearV3.Rcpt.Extract.V.Facts

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.Segs — fields of the `rcpt` table

A *field* (`Fld tr tt r0 L X`): rows `r0 … r0+L−1` in state `X`, `idx` counting
from `0`, `fs` exactly on the first row, `fe` exactly on the last.  From a
field start the field runs to its end (`fld_from`); its length is given by
`lastIdx` (`fld_len`); after it the next field starts in the successor state
(`fld_next`); receipt constants are kept (`fld_consts`).
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- A field of `L` rows in state `X` starting at `r0`. -/
structure Fld (tr : Trace Fp) (tt r0 L X : Nat) : Prop where
  pos : 0 < L
  act : ∀ k, k < L → tr.cell tt (r0 + k) act = 1
  st : ∀ k, k < L → tr.cell tt (r0 + k) X = 1
  idx : ∀ k, k < L → tr.cell tt (r0 + k) idx = ((k : Nat) : Fp)
  fs : ∀ k, k < L → tr.cell tt (r0 + k) fs = if k = 0 then 1 else 0
  fe : ∀ k, k < L → tr.cell tt (r0 + k) fe = if k + 1 = L then 1 else 0

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem hP : tr.height tt < P := by have := height_le hL; unfold P; omega

/-- **From a field start, the field runs to its end.** -/
theorem fld_from {r0 X : Nat} (hr0 : r0 < tr.height tt) (hX : X ∈ states)
    (h1 : tr.cell tt r0 X = 1) (hi : tr.cell tt r0 idx = 0) (hfs : tr.cell tt r0 fs = 1) :
    ∃ L, r0 + L < tr.height tt ∧ Fld tr tt r0 L X := by
  have ha0 := (oneHot hL hr0 hX h1).1
  -- walking forward while `fe = 0`
  have key : ∀ d, r0 + d < tr.height tt → (∀ e, e < d → tr.cell tt (r0 + e) fe = 0) →
      ∀ e, e ≤ d → tr.cell tt (r0 + e) act = 1 ∧ tr.cell tt (r0 + e) X = 1 ∧
        tr.cell tt (r0 + e) idx = ((e : Nat) : Fp) ∧ (0 < e → tr.cell tt (r0 + e) fs = 0) := by
    intro d
    induction d with
    | zero =>
      intro _ _ e he
      have : e = 0 := by omega
      subst this; exact ⟨ha0, h1, by simp only [Nat.add_zero]; rw [hi]; rfl, fun h => by omega⟩
    | succ d ih =>
      intro hd hfe e he
      rcases Nat.lt_or_ge e (d + 1) with h | h
      · exact ih (by omega) (fun e' he' => hfe e' (by omega)) e (by omega)
      · have : e = d + 1 := by omega
        subst this
        obtain ⟨a1, a2, a3, -⟩ := ih (by omega) (fun e' he' => hfe e' (by omega)) d (Nat.le_refl _)
        have hf := inField hL (r := r0 + d) (by omega) a1 (hfe d (by omega))
        rw [show r0 + (d + 1) = r0 + d + 1 by omega]
        refine ⟨hf.2.2.2, by rw [hf.1 X hX, a2], by rw [hf.2.1, a3, natCast_add]; rfl, fun _ => hf.2.2.1⟩
  have hex : ∃ d, r0 + d < tr.height tt ∧ tr.cell tt (r0 + d) fe = 1 := by
    refine Classical.byContradiction fun hne => ?_
    have hall : ∀ e, r0 + e < tr.height tt → tr.cell tt (r0 + e) fe = 0 := fun e he =>
      bool01 hL he (by simp [boolCols]) (fun h => hne ⟨e, he, h⟩)
    have h1' : r0 + (tr.height tt - 1 - r0) = tr.height tt - 1 := by omega
    have ha := (key (tr.height tt - 1 - r0) (by omega) (fun e he => hall e (by omega))
      (tr.height tt - 1 - r0) (Nat.le_refl _)).1
    rw [h1', lastRow hL (by omega)] at ha
    exact fp_zero_ne_one ha
  obtain ⟨d, ⟨hdH, hfd⟩, hmin⟩ := exists_least hex
  have hfe0 : ∀ e, e < d → tr.cell tt (r0 + e) fe = 0 := fun e he =>
    bool01 hL (by omega) (by simp [boolCols]) (fun h => hmin e he ⟨by omega, h⟩)
  have K := key d hdH hfe0
  have hda : r0 + d + 1 < tr.height tt := act_lt hL hdH (K d (Nat.le_refl _)).1
  refine ⟨d + 1, by omega, ⟨by omega, fun k hk => (K k (by omega)).1, fun k hk => (K k (by omega)).2.1,
    fun k hk => (K k (by omega)).2.2.1, fun k hk => ?_, fun k hk => ?_⟩⟩
  · split
    · rename_i h; subst h; simpa using hfs
    · exact (K k (by omega)).2.2.2 (by omega)
  · split
    · rename_i h; rw [show k = d by omega]; exact hfd
    · exact hfe0 k (by omega)

/-- The field's length from `lastIdx`. -/
theorem fld_len {r0 L X : Nat} {e : Expr} (hH : r0 + L ≤ tr.height tt) (hf : Fld tr tt r0 L X)
    (hx : (X, e) ∈ lastIdx) :
    (((L - 1 : Nat) : Nat) : Fp) = e.eval tr tt (r0 + (L - 1)) pub := by
  have hp := hf.pos
  have := fieldEnd hL (r := r0 + (L - 1)) (by omega) (by rw [hf.fe (L - 1) (by omega), if_pos (by omega)]) hx
    (hf.st (L - 1) (by omega))
  rw [← this, hf.idx (L - 1) (by omega)]

/-- A constant field length. -/
theorem fld_len_k {r0 L X m : Nat} (hH : r0 + L ≤ tr.height tt) (hf : Fld tr tt r0 L X)
    (hx : (X, k m) ∈ lastIdx) (hm : m < P) : L = m + 1 := by
  have := fld_len hL hH hf hx
  simp only [eval_k] at this
  have := ofNat_inj (a := L - 1) (b := m) (by have := hP hL; omega) hm this
  have := hf.pos; omega

/-- Receipt constants are kept through a (non-claim) field. -/
theorem fld_consts {r0 L X : Nat} (hH : r0 + L ≤ tr.height tt) (hf : Fld tr tt r0 L X)
    (hX : X ∈ states) (hne : X ≠ sCL) :
    ∀ j, j < L → ∀ x ∈ rconsts, tr.cell tt (r0 + j) x = tr.cell tt r0 x := by
  intro j hj
  induction j with
  | zero => intro x _; rfl
  | succ j ih =>
    intro x hx
    have hq : r0 + j < tr.height tt := by omega
    have hfe : tr.cell tt (r0 + j) fe = 0 := by rw [hf.fe j (by omega), if_neg (by omega)]
    have hrl : tr.cell tt (r0 + j) rl = 0 := by rw [(bounds hL hq).1, hfe]; grind
    have hc : tr.cell tt (r0 + j) sCL = 0 :=
      (oneHot hL hq hX (hf.st j (by omega))).2 sCL (by simp [states]) (Ne.symm hne)
    rw [show r0 + (j + 1) = r0 + j + 1 by omega, rconst hL (by omega) (hf.act j (by omega)) hc hrl x hx,
      ih (by omega) x hx]

/-- After a field (not ending the receipt): the successor field starts. -/
theorem fld_next {r0 L X X' : Nat} {g : Expr} (hH : r0 + L ≤ tr.height tt) (hf : Fld tr tt r0 L X)
    (hrl : tr.cell tt (r0 + (L - 1)) rl = 0) (hs : (X, X', g) ∈ RcptV3.succ)
    (hg : g.eval tr tt (r0 + (L - 1)) pub = 1) :
    r0 + L < tr.height tt ∧ tr.cell tt (r0 + L) X' = 1 ∧ tr.cell tt (r0 + L) idx = 0 ∧
      tr.cell tt (r0 + L) fs = 1 := by
  have hp := hf.pos
  have hq : r0 + (L - 1) < tr.height tt := by omega
  have hq1 := act_lt hL hq (hf.act (L - 1) (by omega))
  have he : tr.cell tt (r0 + (L - 1)) fe = 1 := by rw [hf.fe (L - 1) (by omega), if_pos (by omega)]
  have h1 := fieldSucc hL hq1 he hs (hf.st (L - 1) (by omega)) hg
  have hX' : X' ∈ states := by
    simp only [RcptV3.succ, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at hs
    rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      first | (obtain ⟨-, rfl, -⟩ := h; simp [states]) | exact absurd h id
  have h2 := afterField hL hq1 he (oneHot hL hq1 hX' h1).1
  rw [show r0 + (L - 1) + 1 = r0 + L by omega] at h1 h2 hq1
  exact ⟨hq1, h1, h2⟩

/-- Constants across a field boundary inside a receipt. -/
theorem consts_next {q : Nat} (hq : q + 1 < tr.height tt) (ha : tr.cell tt q act = 1)
    (hc : tr.cell tt q sCL = 0) (hrl : tr.cell tt q rl = 0) :
    ∀ x ∈ rconsts, tr.cell tt (q + 1) x = tr.cell tt q x :=
  rconst hL hq ha hc hrl

end ZkFormal.NearV3.RcptV3Proof
