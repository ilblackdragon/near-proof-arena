import ZkFormal.Near.Extract.RcptOf

/-!
# ZkFormal.Near.Extract.RcptChunks — toolkit for the `BYTES` chunks of a receipt

Field membership and bounds in a `Layout`, the values of the receipt
constants on a field row (`RowV`), and register-field byte values.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem plan_le (h : Bool) (Lp Lv Ls kt : Nat) :
    ∀ f ∈ plan h Lp Lv Ls kt, f.2.1 + f.2.2 ≤ total h Lp Lv Ls kt := by
  intro f hf
  cases h
  · simp only [plan, hN, Bool.false_eq_true, if_false, List.append_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [total, Vt] <;> omega
  · simp only [plan, hN, if_true, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [total, Vt] <;> omega

theorem hN_cast (h : Bool) : ((hN h : Nat) : Fp) = if h then 1 else 0 := by cases h <;> rfl

/-- Values on a receipt-field row. -/
structure RowV (tr : Trace Fp) (q : Nat) (h : Bool) (Lp Lv Ls kt oN o2N rN k : Nat) : Prop where
  o : tr.cell T_RCPT q o = (oN : Fp)
  o2 : tr.cell T_RCPT q o2 = (o2N : Fp)
  r : tr.cell T_RCPT q Rcpt.r = (rN : Fp)
  Lp : tr.cell T_RCPT q Rcpt.Lp = (Lp : Fp)
  Lv : tr.cell T_RCPT q Rcpt.Lv = (Lv : Fp)
  Ls : tr.cell T_RCPT q Rcpt.Ls = (Ls : Fp)
  kt : tr.cell T_RCPT q Rcpt.kt = (kt : Fp)
  hr : tr.cell T_RCPT q Rcpt.hr = ((hN h : Nat) : Fp)
  idx : tr.cell T_RCPT q idx = (k : Fp)

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem lay_fld {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) {X off L : Nat}
    (hm : (X, off, L) ∈ plan h Lp Lv Ls kt) :
    RFld tr s (s + off) L X ∧ s + off + L ≤ tr.height T_RCPT := by
  have := plan_le h Lp Lv Ls kt _ hm
  have := lay.fin
  exact ⟨lay.flds _ hm, by simp at *; omega⟩

theorem rowV {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt)
    {oN o2N rN : Nat} (ho : tr.cell T_RCPT s o = (oN : Fp)) (ho2 : tr.cell T_RCPT s o2 = (o2N : Fp))
    (hr : tr.cell T_RCPT s Rcpt.r = (rN : Fp)) {r0 L X : Nat} (F : RFld tr s r0 L X) {k : Nat} (hk : k < L) :
    RowV tr (r0 + k) h Lp Lv Ls kt oN o2N rN k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, F.fld.idx k hk⟩
  · rw [F.consts k hk _ (by simp [rconsts]), ho]
  · rw [F.consts k hk _ (by simp [rconsts]), ho2]
  · rw [F.consts k hk _ (by simp [rconsts]), hr]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.cLp]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.cLv]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.cLs]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.ckt]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.hr, hN_cast]

/-- Bytes of a register field from its load. -/
theorem reg_val {s r0 L X : Nat} {l : List Expr} (hH : r0 + L ≤ tr.height T_RCPT) (F : RFld tr s r0 L X)
    (hX : X ∈ regStates) (hne : X ≠ sCL) (hl : (X, l) ∈ loads) (hLl : L ≤ l.length) (hL32 : L ≤ 32)
    (bytes : List Nat)
    (hv : ∀ k (hk : k < L), (l[k]'(by omega)).eval tr T_RCPT r0 pub = ((bytes.getD k 0 : Nat) : Fp)) :
    ∀ k, k < L → (c b).eval tr T_RCPT (r0 + k) pub = ((bytes.getD k 0 : Nat) : Fp) := by
  intro k hk
  rw [eval_c, fld_load hL hH F.fld hX hne hl hLl hL32 k hk, hv k hk]

omit hL in
/-- Bytes of a field read from the column `b`. -/
theorem col_val (r0 L x k : Nat) (hk : k < L) :
    (c x).eval tr T_RCPT (r0 + k) pub = (((colAt tr r0 L x).getD k 0 : Nat) : Fp) := by
  rw [eval_c, colAt_get _ _ _ _ _ hk, cell_eq_cast]

omit hL in
theorem ks_get (bytes : List Nat) (k : Nat) (hk : k < bytes.length) (r0 : Nat) :
    ((ks bytes)[k]'(by simp [ks]; omega)).eval tr T_RCPT r0 pub = ((bytes.getD k 0 : Nat) : Fp) := by
  simp [ks, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

end ZkFormal.Near.RcptProof
