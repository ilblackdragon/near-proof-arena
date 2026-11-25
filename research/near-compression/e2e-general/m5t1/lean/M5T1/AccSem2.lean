import M5T1.AccSem1

/-!
# M5T1.AccSem2 — the `ACC` constraints, row by row, as natural-number facts (F-4)

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.AccSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.AccDef M5T1.RbSem M5T1.BndLay

/-! ## The constraint list, piece by piece (`++` is left-associative) -/

section
open M5T1.Acc

def L1 : List Expr := ["act", "fst", "lst", "hid"].map fun s => bool (c s)
def L2 : List Expr := [(1 - c "act") * c "fst", (1 - c "act") * c "lst", .isFirst * c "act" * (1 - c "fst")]
def L3 : List Expr := (List.range 16).flatMap (splitCons blkB blkS)
def L4 : List Expr := (List.range 6).flatMap (splitCons dgB dgS)
def L5 : List Expr :=
  (List.range 24).map fun l => c "fst" * (c "h" l - K ((wlimbs (IV384.getD (l / 3) 0)).getD (l % 3) 0))
def L6 : List Expr := (List.range 42).map fun j => c "fst" * (c "blk" j - accPub Rb.SI j)
def L7 : List Expr := (List.range 6).flatMap fun t =>
    let (a0, a1, a2) := wordOf dgB dgS t
    [c "lst" * (a0 - c "o" (3 * t)), c "lst" * (a1 - c "o" (3 * t + 1)), c "lst" * (a2 - c "o" (3 * t + 2))]
def L8 : List Expr := (List.range 42).map fun j => c "lst" * (c "dg" j - accPub Rb.SO j)
def gN : Expr := n "act" * (1 - n "fst")
def L9 : List Expr := [.isTransition * gN * (1 - c "act"), .isTransition * gN * c "lst",
  .isTransition * gN * (n "hid" - c "hid")]
def L10 : List Expr := (List.range 24).map fun l => .isTransition * gN * (n "h" l - c "o" l)

theorem cons_eq : Acc.table.constraints = L1 ++ L2 ++ L3 ++ L4 ++ L5 ++ L6 ++ L7 ++ L8 ++ L9 ++ L10 := rfl
end

theorem m1 {e : Expr} (h : e ∈ L1) : e ∈ Acc.table.constraints := by rw [cons_eq]; simp [h]
theorem m2 {e : Expr} (h : e ∈ L2) : e ∈ Acc.table.constraints := by rw [cons_eq]; simp [h]
theorem m3 {e : Expr} (h : e ∈ L3) : e ∈ Acc.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr h)))))))
theorem m4 {e : Expr} (h : e ∈ L4) : e ∈ Acc.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inr h))))))
theorem m5 {e : Expr} (h : e ∈ L5) : e ∈ Acc.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
theorem m6 {e : Expr} (h : e ∈ L6) : e ∈ Acc.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inr h))))
theorem m7 {e : Expr} (h : e ∈ L7) : e ∈ Acc.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inr h)))
theorem m8 {e : Expr} (h : e ∈ L8) : e ∈ Acc.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inr h))
theorem m9 {e : Expr} (h : e ∈ L9) : e ∈ Acc.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inr h)
theorem m10 {e : Expr} (h : e ∈ L10) : e ∈ Acc.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inr h

/-! ## Row facts -/

section
variable {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (fullAir tape xtape) pub tr)
include H

omit H in
theorem acc_lt : 7 < (fullAir tape xtape).tables.length := by rw [fullAir_len]; decide

theorem ac {r : Nat} (hr : r < tr.height 7) {e : Expr} (he : e ∈ Acc.table.constraints) :
    ev tr 7 r pub e = 0 :=
  ev_of_eval (H.constr 7 acc_lt r hr e he)

theorem bools {r : Nat} (hr : r < tr.height 7) :
    accC tr r "act" ≤ 1 ∧ accC tr r "fst" ≤ 1 ∧ accC tr r "lst" ≤ 1 ∧ accC tr r "hid" ≤ 1 :=
  ⟨bool_le (x := Acc.c "act") (ac H hr (m1 (by simp [L1]))),
    bool_le (x := Acc.c "fst") (ac H hr (m1 (by simp [L1]))),
    bool_le (x := Acc.c "lst") (ac H hr (m1 (by simp [L1]))),
    bool_le (x := Acc.c "hid") (ac H hr (m1 (by simp [L1])))⟩

theorem lst_act {r : Nat} (hr : r < tr.height 7) (hl : accC tr r "lst" = 1) : accC tr r "act" = 1 := by
  have h := ac H hr (m2 (e := (1 - Acc.c "act") * Acc.c "lst") (by simp [L2]))
  have hb := (bools H hr).1
  simp only [evMul, evSub, evOne, evAc, hl] at h
  omega

theorem fst_act {r : Nat} (hr : r < tr.height 7) (hf : accC tr r "fst" = 1) : accC tr r "act" = 1 := by
  have h := ac H hr (m2 (e := (1 - Acc.c "act") * Acc.c "fst") (by simp [L2]))
  have hb := (bools H hr).1
  simp only [evMul, evSub, evOne, evAc, hf] at h
  omega

theorem row0_fst (h0 : 0 < tr.height 7) (ha : accC tr 0 "act" = 1) : accC tr 0 "fst" = 1 := by
  have h := ac H h0 (m2 (e := .isFirst * Acc.c "act" * (1 - Acc.c "fst")) (by simp [L2]))
  have hb := (bools H h0).2.1
  simp only [evMul, evSub, evOne, evAc, ha, evFirst0] at h
  omega

/-- **Inside a hash**: an active non-first row's predecessor is active, not last, has the same
`hid`, and its output chains into the row's input. -/
theorem trans_facts {r : Nat} (hr : r + 1 < tr.height 7) (ha : accC tr (r + 1) "act" = 1)
    (hf : accC tr (r + 1) "fst" = 0) :
    accC tr r "act" = 1 ∧ accC tr r "lst" = 0 ∧ accC tr (r + 1) "hid" = accC tr r "hid" ∧
      ∀ l < 24, accC tr (r + 1) "h" l = accC tr r "o" l := by
  have hr' : r < tr.height 7 := by omega
  have hg : ev tr 7 r pub (.isTransition * gN) = 1 := by
    simp only [gN, evMul, evSub, evOne, evAn hr, ha, hf, evTrans hr]
  have e1 := gate_eq hg (ac H hr' (m9 (e := .isTransition * gN * (1 - Acc.c "act")) (by simp [L9])))
  have e2 := ac H hr' (m9 (e := .isTransition * gN * Acc.c "lst") (by simp [L9]))
  have e3 := gate_eq hg (ac H hr' (m9 (e := .isTransition * gN * (Acc.n "hid" - Acc.c "hid")) (by simp [L9])))
  simp only [evOne, evAc] at e1
  rw [evMul, hg, Nat.one_mul, evAc] at e2
  rw [evAn hr, evAc] at e3
  refine ⟨e1.symm, ?_, e3, fun l hl => ?_⟩
  · have := accC_lt (tr := tr) (r := r) "lst" 0; omega
  · have e4 := gate_eq hg (ac H hr' (m10 (e := .isTransition * gN * (Acc.n "h" l - Acc.c "o" l))
      (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)))
    rw [evAn hr, evAc] at e4
    exact e4

/-- A first row starts from `IV384`. -/
theorem fst_iv {r : Nat} (hr : r < tr.height 7) (hf : accC tr r "fst" = 1) :
    ∀ l < 24, accC tr r "h" l = (Acc.wlimbs (Acc.IV384.getD (l / 3) 0)).getD (l % 3) 0 := by
  intro l hl
  have e := gate_eq (by rw [evAc, hf]) (ac H hr (m5 (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)))
  rw [evAc, evK] at e
  rw [e]
  apply Nat.mod_eq_of_lt
  have : ∀ l < 24, (Acc.wlimbs (Acc.IV384.getD (l / 3) 0)).getD (l % 3) 0 < 2013265921 := by decide
  exact this l hl

theorem ev_accPub (S : BndLay.Side) (j : Nat) {r : Nat} {h : Nat} (hh : accC tr r "hid" = h)
    (h2 : h < 2) : ev tr 7 r pub (Acc.accPub S j) =
      SegRt.pv pub (S.base + S.L.off (accF h) + j) := by
  have hp1 : SegRt.pv pub (S.base + S.L.off "outcomeAcc" + j) < 2013265921 := Fp.toNat_lt _
  have hp2 : SegRt.pv pub (S.base + S.L.off "outRcpt0" + j) < 2013265921 := Fp.toNat_lt _
  unfold Acc.accPub
  simp only [evAdd, evMul, evSub, evOne, evAc, hh, BndLay.Side.b, evPub]
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp [accF] <;> omega

/-- A first row's first 42 block bytes are the input accumulator. -/
theorem fst_prefix {r : Nat} (hr : r < tr.height 7) (hf : accC tr r "fst" = 1) {h : Nat}
    (hh : accC tr r "hid" = h) (h2 : h < 2) :
    ∀ j < 42, accC tr r "blk" j = SegRt.pv pub (BIN + callF.off (accF h) + j) := by
  intro j hj
  have e := gate_eq (by rw [evAc, hf]) (ac H hr (m6 (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))
  rw [evAc, ev_accPub H _ _ hh h2] at e
  simpa [Rb.SI, bin_eq] using e

/-- A last row's digest bytes are the output accumulator. -/
theorem lst_dg {r : Nat} (hr : r < tr.height 7) (hl : accC tr r "lst" = 1) {h : Nat}
    (hh : accC tr r "hid" = h) (h2 : h < 2) :
    ∀ j < 42, accC tr r "dg" j = SegRt.pv pub (BOUT + engF.off (accF h) + j) := by
  intro j hj
  have e := gate_eq (by rw [evAc, hl]) (ac H hr (m8 (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))
  rw [evAc, ev_accPub H _ _ hh h2] at e
  simpa [Rb.SO, bout_eq] using e

/-- A last row's digest limbs are its output words 0..5. -/
theorem lst_limbs {r : Nat} (hr : r < tr.height 7) (hl : accC tr r "lst" = 1) (t : Nat) (ht : t < 6) :
    ev tr 7 r pub (Acc.wordOf Acc.dgB Acc.dgS t).1 = accC tr r "o" (3 * t) ∧
    ev tr 7 r pub (Acc.wordOf Acc.dgB Acc.dgS t).2.1 = accC tr r "o" (3 * t + 1) ∧
    ev tr 7 r pub (Acc.wordOf Acc.dgB Acc.dgS t).2.2 = accC tr r "o" (3 * t + 2) := by
  have hg : ev tr 7 r pub (Acc.c "lst") = 1 := by rw [evAc, hl]
  have mem : ∀ e ∈ [Acc.c "lst" * ((Acc.wordOf Acc.dgB Acc.dgS t).1 - Acc.c "o" (3 * t)),
      Acc.c "lst" * ((Acc.wordOf Acc.dgB Acc.dgS t).2.1 - Acc.c "o" (3 * t + 1)),
      Acc.c "lst" * ((Acc.wordOf Acc.dgB Acc.dgS t).2.2 - Acc.c "o" (3 * t + 2))],
      e ∈ Acc.table.constraints := fun e he => m7 (List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, he⟩)
  refine ⟨?_, ?_, ?_⟩
  · have := gate_eq hg (ac H hr (mem _ (List.mem_cons_self ..))); rwa [evAc] at this
  · have := gate_eq hg (ac H hr (mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))));
    rwa [evAc] at this
  · have := gate_eq hg (ac H hr (mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))); rwa [evAc] at this

/-- The split constraints of a word (ungated). -/
theorem split_facts {r : Nat} (hr : r < tr.height 7) (b s : String) (w : Nat)
    (hm : ∀ e ∈ Acc.splitCons (fun j => Acc.c b j) (fun j => Acc.c s j) w, e ∈ Acc.table.constraints) :
    ev tr 7 r pub (Acc.c b (8 * w + 5) - Acc.c s (4 * w) - K 32 * Acc.c s (4 * w + 1)) = 0 ∧
    ev tr 7 r pub (Acc.c b (8 * w + 2) - Acc.c s (4 * w + 2) - K 4 * Acc.c s (4 * w + 3)) = 0 :=
  ⟨ac H hr (hm _ (by simp [Acc.splitCons])), ac H hr (hm _ (by simp [Acc.splitCons]))⟩

end

end M5T1.AccSem
