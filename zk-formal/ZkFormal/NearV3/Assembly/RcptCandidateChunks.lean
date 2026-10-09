import ZkFormal.NearV3.Assembly.RcptCandidateOf
-- Source Chunks.lean SHA256: e992e0eb568ca74515f63e52908a02a0a730ef649d173a4a1ced507918b09995.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.Of
import ZkFormal.Near.Extract.RcptChain

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.Chunks (v1 `RcptChunks`) — toolkit for the `BYTES` chunks of a receipt

Field membership and bounds in a `Layout`, the values of the receipt
constants on a field row (`RowV`), and register-field byte values.
-/

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

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
structure RowV (tr : Trace Fp) (tt q : Nat) (h : Bool) (Lp Lv Ls kt oN o2N rN jN k : Nat) : Prop where
  j : tr.cell tt q j = (jN : Fp)
  o : tr.cell tt q o = (oN : Fp)
  o2 : tr.cell tt q o2 = (o2N : Fp)
  r : tr.cell tt q RcptV3.r = (rN : Fp)
  Lp : tr.cell tt q RcptV3.Lp = (Lp : Fp)
  Lv : tr.cell tt q RcptV3.Lv = (Lv : Fp)
  Ls : tr.cell tt q RcptV3.Ls = (Ls : Fp)
  kt : tr.cell tt q RcptV3.kt = (kt : Fp)
  hr : tr.cell tt q RcptV3.hr = ((hN h : Nat) : Fp)
  idx : tr.cell tt q idx = (k : Fp)

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem lay_fld {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt) {X off L : Nat}
    (hm : (X, off, L) ∈ plan h Lp Lv Ls kt) :
    RFld tr tt s (s + off) L X ∧ s + off + L ≤ tr.height tt ∧ off + L ≤ total h Lp Lv Ls kt := by
  have hp := plan_le h Lp Lv Ls kt _ hm
  have := lay.fin
  exact ⟨lay.flds _ hm, by simp at *; omega, by simpa using hp⟩

theorem rowV {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt)
    {oN o2N rN : Nat} (ho : tr.cell tt s o = (oN : Fp)) (ho2 : tr.cell tt s o2 = (o2N : Fp))
    (hr : tr.cell tt s RcptV3.r = (rN : Fp)) {jN : Nat} {r0 L X : Nat} (F : RFld tr tt s r0 L X)
    (hj : ∀ k, k < L → tr.cell tt (r0 + k) j = (jN : Fp)) {k : Nat} (hk : k < L) :
    RowV tr tt (r0 + k) h Lp Lv Ls kt oN o2N rN jN k := by
  refine ⟨hj k hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, F.fld.idx k hk⟩
  · rw [F.consts k hk _ (by simp [rconsts]), ho]
  · rw [F.consts k hk _ (by simp [rconsts]), ho2]
  · rw [F.consts k hk _ (by simp [rconsts]), hr]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.cLp]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.cLv]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.cLs]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.ckt]
  · rw [F.consts k hk _ (by simp [rconsts]), lay.hr, hN_cast]

/-- Bytes of a register field from its load. -/
theorem reg_val {s r0 L X : Nat} {l : List Expr} (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X)
    (hX : X ∈ regStates) (hne : X ≠ sCL) (hl : (X, l) ∈ loads) (hLl : L ≤ l.length) (hL32 : L ≤ 32)
    (bytes : List Nat)
    (hv : ∀ k (hk : k < L), (l[k]'(by omega)).eval tr tt r0 pub = ((bytes.getD k 0 : Nat) : Fp)) :
    ∀ k, k < L → (c b).eval tr tt (r0 + k) pub = ((bytes.getD k 0 : Nat) : Fp) := by
  intro k hk
  rw [eval_c, fld_load hL hH F.fld hX hne hl hLl hL32 k hk, hv k hk]

omit hL in
/-- Bytes of a field read from the column `b`. -/
theorem col_val (r0 L x k : Nat) (hk : k < L) :
    (c x).eval tr tt (r0 + k) pub = (((colAt tr tt r0 L x).getD k 0 : Nat) : Fp) := by
  rw [eval_c, colAt_get _ _ _ _ _ _ hk, cell_eq_cast]

omit hL in
theorem ks_get (bytes : List Nat) (k : Nat) (hk : k < bytes.length) (r0 : Nat) :
    ((ks bytes)[k]'(by simp [ks]; omega)).eval tr tt r0 pub = ((bytes.getD k 0 : Nat) : Fp) := by
  simp [ks, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
