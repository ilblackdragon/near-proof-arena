import M5T1.ShSem1

/-!
# M5T1.ShSem2 — the `SH` constraints, row by row, as natural-number facts (F-7)

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.ShSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.ShDef
open M5T1.AccSem (evAdd evMul evSub evK evOne evZero evFirst0 evFirstS evTrans evPub gate_eq
  bool_le)

/-! ## The constraint list, piece by piece (`++` is left-associative) -/

section
open M5T1.Sh

def L1 : List Expr := ["act", "fst", "lst", "fx"].map fun s => bool (c s)
def L2 : List Expr := [(1 - c "act") * c "fst", (1 - c "act") * c "lst", .isFirst * c "act" * (1 - c "fst")]
def L3 : List Expr := (List.range 16).flatMap (Acc.splitCons blkB blkS)
def L4 : List Expr := (List.range 6).flatMap (Acc.splitCons dgB dgS)
def L5 : List Expr :=
  (List.range 24).map fun l => c "fst" * (c "h" l - K ((Acc.wlimbs (Acc.IV384.getD (l / 3) 0)).getD (l % 3) 0))
def L6 : List Expr := [c "fst" * c "bi"]
def L7 : List Expr := (List.range 6).flatMap fun t =>
    let (a0, a1, a2) := Acc.wordOf dgB dgS t
    [c "lst" * (a0 - c "o" (3 * t)), c "lst" * (a1 - c "o" (3 * t + 1)), c "lst" * (a2 - c "o" (3 * t + 2))]
def L8 : List Expr := [.isTransition * gN * (1 - c "act"), .isTransition * gN * c "lst",
  .isTransition * gN * (n "hid" - c "hid"), .isTransition * gN * (n "fx" - c "fx"),
  .isTransition * gN * (n "bi" - c "bi" - 1)]
def L9 : List Expr := (List.range 24).map fun l => .isTransition * gN * (n "h" l - c "o" l)

theorem cons_eq : Sh.table.constraints = L1 ++ L2 ++ L3 ++ L4 ++ L5 ++ L6 ++ L7 ++ L8 ++ L9 := rfl
end

theorem m1 {e : Expr} (h : e ∈ L1) : e ∈ Sh.table.constraints := by rw [cons_eq]; simp [h]
theorem m2 {e : Expr} (h : e ∈ L2) : e ∈ Sh.table.constraints := by rw [cons_eq]; simp [h]
theorem m3 {e : Expr} (h : e ∈ L3) : e ∈ Sh.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inr h))))))
theorem m4 {e : Expr} (h : e ∈ L4) : e ∈ Sh.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
theorem m5 {e : Expr} (h : e ∈ L5) : e ∈ Sh.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inr h))))
theorem m6 {e : Expr} (h : e ∈ L6) : e ∈ Sh.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inr h)))
theorem m7 {e : Expr} (h : e ∈ L7) : e ∈ Sh.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inl (.inr h))
theorem m8 {e : Expr} (h : e ∈ L8) : e ∈ Sh.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inl (.inr h)
theorem m9 {e : Expr} (h : e ∈ L9) : e ∈ Sh.table.constraints := by
  rw [cons_eq]; simp only [List.mem_append]; exact .inr h

/-! ## Row facts -/

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
include H

theorem ac {r : Nat} (hr : r < tr.height 2) {e : Expr} (he : e ∈ Sh.table.constraints) :
    ev tr 2 r pub e = 0 :=
  ev_of_eval (H.constr 2 sh_lt r hr e he)

theorem bools {r : Nat} (hr : r < tr.height 2) :
    shC tr r "act" ≤ 1 ∧ shC tr r "fst" ≤ 1 ∧ shC tr r "lst" ≤ 1 ∧ shC tr r "fx" ≤ 1 :=
  ⟨bool_le (x := Sh.c "act") (ac H hr (m1 (by simp [L1]))),
    bool_le (x := Sh.c "fst") (ac H hr (m1 (by simp [L1]))),
    bool_le (x := Sh.c "lst") (ac H hr (m1 (by simp [L1]))),
    bool_le (x := Sh.c "fx") (ac H hr (m1 (by simp [L1])))⟩

theorem lst_act {r : Nat} (hr : r < tr.height 2) (hl : shC tr r "lst" = 1) : shC tr r "act" = 1 := by
  have h := ac H hr (m2 (e := (1 - Sh.c "act") * Sh.c "lst") (by simp [L2]))
  have hb := (bools H hr).1
  simp only [evMul, evSub, evOne, evSc, hl] at h
  omega

theorem fst_act {r : Nat} (hr : r < tr.height 2) (hf : shC tr r "fst" = 1) : shC tr r "act" = 1 := by
  have h := ac H hr (m2 (e := (1 - Sh.c "act") * Sh.c "fst") (by simp [L2]))
  have hb := (bools H hr).1
  simp only [evMul, evSub, evOne, evSc, hf] at h
  omega

theorem row0_fst (h0 : 0 < tr.height 2) (ha : shC tr 0 "act" = 1) : shC tr 0 "fst" = 1 := by
  have h := ac H h0 (m2 (e := .isFirst * Sh.c "act" * (1 - Sh.c "fst")) (by simp [L2]))
  have hb := (bools H h0).2.1
  simp only [evMul, evSub, evOne, evSc, ha, evFirst0] at h
  omega

theorem fst_bi {r : Nat} (hr : r < tr.height 2) (hf : shC tr r "fst" = 1) : shC tr r "bi" = 0 := by
  have h := ac H hr (m6 (e := Sh.c "fst" * Sh.c "bi") (by simp [L6]))
  simp only [evMul, evSc, hf, Nat.one_mul] at h
  rwa [Nat.mod_eq_of_lt (shC_lt _ _)] at h

/-- **Inside a hash**: an active non-first row's predecessor is active, not last, has the same
`hid` and `fx`, the previous block index, and its output chains into the row's input. -/
theorem trans_facts {r : Nat} (hr : r + 1 < tr.height 2) (ha : shC tr (r + 1) "act" = 1)
    (hf : shC tr (r + 1) "fst" = 0) :
    shC tr r "act" = 1 ∧ shC tr r "lst" = 0 ∧ shC tr (r + 1) "hid" = shC tr r "hid" ∧
      shC tr (r + 1) "fx" = shC tr r "fx" ∧ shC tr (r + 1) "bi" = (shC tr r "bi" + 1) % 2013265921 ∧
      ∀ l < 24, shC tr (r + 1) "h" l = shC tr r "o" l := by
  have hr' : r < tr.height 2 := by omega
  have hg : ev tr 2 r pub (.isTransition * Sh.gN) = 1 := by
    simp only [Sh.gN, evMul, evSub, evOne, evSn hr, ha, hf, evTrans hr]
  have e1 := gate_eq hg (ac H hr' (m8 (e := .isTransition * Sh.gN * (1 - Sh.c "act")) (by simp [L8])))
  have e2 := ac H hr' (m8 (e := .isTransition * Sh.gN * Sh.c "lst") (by simp [L8]))
  have e3 := gate_eq hg (ac H hr' (m8 (e := .isTransition * Sh.gN * (Sh.n "hid" - Sh.c "hid")) (by simp [L8])))
  have e4 := gate_eq hg (ac H hr' (m8 (e := .isTransition * Sh.gN * (Sh.n "fx" - Sh.c "fx")) (by simp [L8])))
  have e5 := gate_eq hg (ac H hr' (m8 (e := .isTransition * Sh.gN * (Sh.n "bi" - Sh.c "bi" - 1)) (by simp [L8])))
  simp only [evOne, evSc] at e1
  rw [evMul, hg, Nat.one_mul, evSc] at e2
  rw [evSn hr, evSc] at e3 e4
  simp only [evSub, evSn hr, evSc, evOne] at e5
  refine ⟨e1.symm, ?_, e3, e4, ?_, fun l hl => ?_⟩
  · have := shC_lt (tr := tr) (r := r) "lst" 0; omega
  · have h1 := shC_lt (tr := tr) (r := r + 1) "bi" 0
    have h2 := shC_lt (tr := tr) (r := r) "bi" 0
    omega
  · have e6 := gate_eq hg (ac H hr' (m9 (e := .isTransition * Sh.gN * (Sh.n "h" l - Sh.c "o" l))
      (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)))
    rw [evSn hr, evSc] at e6
    exact e6

/-- A first row starts from `IV384`. -/
theorem fst_iv {r : Nat} (hr : r < tr.height 2) (hf : shC tr r "fst" = 1) :
    ∀ l < 24, shC tr r "h" l = (Acc.wlimbs (Acc.IV384.getD (l / 3) 0)).getD (l % 3) 0 := by
  intro l hl
  have e := gate_eq (by rw [evSc, hf]) (ac H hr (m5 (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)))
  rw [evSc, evK] at e
  rw [e]
  apply Nat.mod_eq_of_lt
  have : ∀ l < 24, (Acc.wlimbs (Acc.IV384.getD (l / 3) 0)).getD (l % 3) 0 < 2013265921 := by decide
  exact this l hl

/-- A last row's digest limbs are its output words 0..5. -/
theorem lst_limbs {r : Nat} (hr : r < tr.height 2) (hl : shC tr r "lst" = 1) (t : Nat) (ht : t < 6) :
    ev tr 2 r pub (Acc.wordOf Sh.dgB Sh.dgS t).1 = shC tr r "o" (3 * t) ∧
    ev tr 2 r pub (Acc.wordOf Sh.dgB Sh.dgS t).2.1 = shC tr r "o" (3 * t + 1) ∧
    ev tr 2 r pub (Acc.wordOf Sh.dgB Sh.dgS t).2.2 = shC tr r "o" (3 * t + 2) := by
  have hg : ev tr 2 r pub (Sh.c "lst") = 1 := by rw [evSc, hl]
  have mem : ∀ e ∈ [Sh.c "lst" * ((Acc.wordOf Sh.dgB Sh.dgS t).1 - Sh.c "o" (3 * t)),
      Sh.c "lst" * ((Acc.wordOf Sh.dgB Sh.dgS t).2.1 - Sh.c "o" (3 * t + 1)),
      Sh.c "lst" * ((Acc.wordOf Sh.dgB Sh.dgS t).2.2 - Sh.c "o" (3 * t + 2))],
      e ∈ Sh.table.constraints := fun e he => m7 (List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, he⟩)
  refine ⟨?_, ?_, ?_⟩
  · have := gate_eq hg (ac H hr (mem _ (List.mem_cons_self ..))); rwa [evSc] at this
  · have := gate_eq hg (ac H hr (mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))));
    rwa [evSc] at this
  · have := gate_eq hg (ac H hr (mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))); rwa [evSc] at this

/-- The split constraints of a word (ungated). -/
theorem split_facts {r : Nat} (hr : r < tr.height 2) (b s : String) (w : Nat)
    (hm : ∀ e ∈ Acc.splitCons (fun j => Sh.c b j) (fun j => Sh.c s j) w, e ∈ Sh.table.constraints) :
    ev tr 2 r pub (Sh.c b (8 * w + 5) - Sh.c s (4 * w) - K 32 * Sh.c s (4 * w + 1)) = 0 ∧
    ev tr 2 r pub (Sh.c b (8 * w + 2) - Sh.c s (4 * w + 2) - K 4 * Sh.c s (4 * w + 3)) = 0 :=
  ⟨ac H hr (hm _ (by simp [Acc.splitCons])), ac H hr (hm _ (by simp [Acc.splitCons]))⟩

end

end M5T1.ShSem
