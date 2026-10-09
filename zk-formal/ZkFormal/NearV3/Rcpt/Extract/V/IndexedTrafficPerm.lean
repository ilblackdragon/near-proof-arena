import ZkFormal.NearV3.Rcpt.Extract.V.KeyMessages

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem flatMap_perm_mem {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀ x∈xs,(f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih (by intro y hy; exact h y (by simp [hy])))

/-- Indexed traffic composition permits physical field reordering while keeping
all message values and multiplicities exact. -/
theorem ListChain.indexed_traffic_perm {tr : Trace Fp} {pub : List Fp} {tt e : Nat} {bs : List ListBlock}
    (hL : TableLocal RcptV3.table tr tt pub) (h : ListChain tr tt 0 bs e)
    (f : Nat→List (List Fp)) (g : Nat→RcptE→List Msg)
    (hh : ∀ B∈bs,(List.range' B.start 12).flatMap f=[])
    (hp : ∀ q,q<tr.height tt → tr.cell tt q RcptV3.act=0 → f q=[])
    (hr : ∀ j,(hj:j<bs.length) → ∀ k,(hk:k<bs[j].receipts.length) →
      ((List.range' bs[j].receipts[k].s bs[j].receipts[k].tot).flatMap f).Perm
        ((g (receiptIndex bs j k) (rcptOf tr tt bs[j].receipts[k])).map Msg.toFp)) :
    ((List.range (tr.height tt)).flatMap f).Perm ((indexedReceiptMsgs tr tt bs g).map Msg.toFp) := by
  rw [h.receipt_spans_full hL f hh hp]
  letI : Inhabited ListBlock := ⟨⟨0,[]⟩⟩
  rw [flatMap_eq_range bs]
  unfold indexedReceiptMsgs
  rw [List.map_flatMap]
  apply flatMap_perm_mem
  intro j hj
  have hj := List.mem_range.mp hj
  rw [getD_eq_getElem' bs default hj,getD_eq_getElem' bs ⟨0,[]⟩ hj]
  rw [flatMap_eq_range bs[j].receipts,List.map_flatMap]
  apply flatMap_perm_mem
  intro k hk
  have hk := List.mem_range.mp hk
  rw [getD_eq_getElem' bs[j].receipts default hk]
  exact hr j hj k hk

end ZkFormal.NearV3.RcptV3Proof
