import ZkFormal.NearV3.Assembly.RcptCandidateChainBytes
-- Source ViewPositions.lean SHA256: 9b3017e9a7a7ac6589875c53c37503677a6f5fcd9e5908cbb25f645365f09c81.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ChainBytes

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Flattening a prefix of blocks plus a prefix of the selected block preserves order. -/
theorem take_flatten_prefix {α β : Type} (xs : List α) (items : α → List β)
    (j : Nat) (hj : j<xs.length) (k : Nat) (hk : k≤(items xs[j]).length) :
    (xs.flatMap items).take (((xs.take j).map fun x => (items x).length).sum+k)=
      (xs.take j).flatMap items++(items xs[j]).take k := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,List.flatMap_nil,
        List.nil_append,List.getElem_cons_zero,List.flatMap_cons]
      exact List.take_append_of_le_length hk
    | succ j =>
      simp only [List.take_succ_cons,List.map_cons,List.sum_cons,List.getElem_cons_succ,List.flatMap_cons]
      rw [Nat.add_assoc,List.take_length_add_append,ih j (by simpa using hj) hk,List.append_assoc]

/-- Receipt counts in the concrete views are the extracted layout counts. -/
theorem view_baseR (tr : Trace Fp) (tt : Nat) (bs : List ListBlock) (j : Nat) :
    baseR (bs.map (ListBlock.view tr tt)) j=((bs.take j).map fun B => B.receipts.length).sum := by
  simp only [baseR,←List.map_take,List.map_map,Function.comp_def,ListBlock.view_length]

theorem view_lOffs (tr : Trace Fp) (tt : Nat) (B : ListBlock) (k : Nat) :
    lOffs (B.view tr tt).rs k=12+((B.receipts.take k).map fun y => (rcptOf tr tt y).enc.length).sum := by
  simp only [lOffs,ListBlock.view,ListBlock.viewReceipts,←List.map_take,List.map_map,Function.comp_def]

theorem view_refund_sum (tr : Trace Fp) (tt : Nat) (B : ListBlock) :
    ((B.view tr tt).rs.map rfLen).sum=B.refundBytes tr tt := by
  simp only [ListBlock.view,ListBlock.viewReceipts,List.map_map,Function.comp_def,ListBlock.refundBytes]

/-- The final semantic body-position function uses the same natural refund prefixes. -/
theorem view_bOffs (tr : Trace Fp) (tt : Nat) (bs : List ListBlock)
    (j : Nat) (hj : j<bs.length) (k : Nat) (hk : k≤bs[j].receipts.length) :
    bOffs (flatR (bs.map (ListBlock.view tr tt))) (baseR (bs.map (ListBlock.view tr tt)) j+k)=
      8+((bs.take j).map fun B => B.refundBytes tr tt).sum+
        ((bs[j].receipts.take k).map fun y => rfLen (rcptOf tr tt y)).sum := by
  have hh := take_flatten_prefix bs (fun B => (B.view tr tt).rs) j hj k (by simpa only [ListBlock.view_length] using hk)
  simp only [ListBlock.view_length] at hh
  simp only [bOffs,flatR,List.flatMap_map,Function.comp_def,view_baseR]
  rw [hh,List.map_append,List.sum_append]
  have hsum : (((bs.take j).flatMap fun B => (B.view tr tt).rs).map rfLen).sum=
      ((bs.take j).map fun B => B.refundBytes tr tt).sum := by
    induction bs.take j with
    | nil => simp
    | cons B rest ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,view_refund_sum,ih]
  rw [hsum]
  simp only [ListBlock.view,ListBlock.viewReceipts,←List.map_take,List.map_map,Function.comp_def]
  omega

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
