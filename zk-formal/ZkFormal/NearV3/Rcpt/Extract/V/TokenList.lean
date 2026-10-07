import ZkFormal.NearV3.Rcpt.Extract.V.TokenPublic

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The concrete sequence contains the entering value and every receipt's output. -/
def tokenList (tr : Trace Fp) (tt : Nat) (xs : List RS) (a : Nat) : List Nat := a::xs.map (tokenOut tr tt)

theorem tokenList_length (tr : Trace Fp) (tt : Nat) (xs : List RS) (a : Nat) :
    (tokenList tr tt xs a).length=xs.length+1 := by simp [tokenList]

theorem TokenRun.input {tr : Trace Fp} {tt : Nat} {xs : List RS} {a z : Nat}
    (h : TokenRun tr tt xs a z) : ∀ k,(hk:k<xs.length) →
      (tokenList tr tt xs a).getD k 0=tokenIn tr tt xs[k] := by
  induction xs generalizing a with
  | nil => intro k hk; simp at hk
  | cons y ys ih =>
    intro k hk
    cases k with
    | zero => exact h.1
    | succ k => exact ih h.2 k (by simpa using hk)

theorem tokenList_output {tr : Trace Fp} {tt : Nat} {xs : List RS} {a : Nat}
    (k : Nat) (hk : k<xs.length) : (tokenList tr tt xs a).getD (k+1) 0=tokenOut tr tt xs[k] := by
  simp [tokenList,List.getD,List.getElem?_eq_getElem hk]

theorem TokenRun.last {tr : Trace Fp} {tt : Nat} {xs : List RS} {a z : Nat}
    (h : TokenRun tr tt xs a z) : (tokenList tr tt xs a).getD xs.length 0=z := by
  induction xs generalizing a with
  | nil => exact h
  | cons y ys ih => exact ih h.2

/-- Every flattened receipt has a concrete list/within-list index. -/
theorem receipt_flat_index (bs : List ListBlock) (g : Nat) (hg : g<(bs.flatMap ListBlock.receipts).length) :
    ∃ j,∃ hj:j<bs.length,∃ k,∃ hk:k<bs[j].receipts.length,
      g=((bs.take j).map fun B => B.receipts.length).sum+k ∧
      (bs.flatMap ListBlock.receipts)[g]=bs[j].receipts[k] := by
  induction bs generalizing g with
  | nil => simp at hg
  | cons B bs ih =>
    by_cases hi : g<B.receipts.length
    · refine ⟨0,by simp,g,hi,?_,?_⟩
      · simp
      · simp only [List.flatMap_cons,List.getElem_cons_zero]
        exact List.getElem_append_left hi
    · have hb : g-B.receipts.length<(bs.flatMap ListBlock.receipts).length := by
        simp only [List.flatMap_cons,List.length_append] at hg
        omega
      obtain ⟨j,hj,k,hk,hg',he⟩ := ih (g-B.receipts.length) hb
      refine ⟨j+1,by simpa using hj,k,hk,?_,?_⟩
      · simp only [List.take_succ_cons,List.map_cons,List.sum_cons]
        omega
      · simp only [List.flatMap_cons,List.getElem_cons_succ]
        rw [List.getElem_append_right (by omega)]
        exact he

end ZkFormal.NearV3.RcptV3Proof
