import ZkFormal.NearV3.Assembly.RcptCandidateDigestTraffic
-- Source KeyMessages.lean SHA256: f166e8d91a4a2aab89afd2a57f71c67c288020778a34b9fb030209a6aa0db50c.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.DigestTraffic

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Nonterminal symbols with their ordinary natural positions. -/
def symbolMsgs (w off : Nat) (xs : List Nat) : List Msg :=
  (List.range xs.length).map fun k => [w,off+k,xs.getD k 0,0]

/-- Explicit marker terminates the indexed key-symbol sequence. -/
theorem keyMsgs_marker (w : Nat) (xs : List Nat) :
    RcptE.keyMsgs w (xs++[SYM_END])=symbolMsgs w 0 xs++[[w,xs.length,SYM_END,1]] := by
  unfold RcptE.keyMsgs symbolMsgs
  simp only [List.length_append,List.length_singleton,List.range_succ,List.map_append,List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro k hk
    have hk := List.mem_range.mp hk
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]
    simp only [Nat.zero_add,if_neg (show k+1≠xs.length+1 by omega)]
  · simp

/-- Concatenation advances symbol positions by the preceding payload length. -/
theorem symbolMsgs_append (w off : Nat) (xs ys : List Nat) :
    symbolMsgs w off (xs++ys)=symbolMsgs w off xs++symbolMsgs w (off+xs.length) ys := by
  simp only [symbolMsgs,List.length_append,List.range_add,List.map_append,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro k hk
    have hk := List.mem_range.mp hk
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]
  · apply List.map_congr_left
    intro k hk
    simp only [Function.comp_def,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp only [Nat.add_assoc]

/-- A payload byte contributes its high and low nibbles at consecutive positions. -/
theorem symbolMsgs_nibbles (w off : Nat) (xs : List Nat) :
    symbolMsgs w off (xs.flatMap (fun x => [x/16,x%16]))=
      (List.range xs.length).flatMap (fun k =>
        [[w,off+2*k,xs.getD k 0/16,0],[w,off+2*k+1,xs.getD k 0%16,0]]) := by
  induction xs generalizing off with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,symbolMsgs_append,ih,List.length_cons,List.length_nil,
      List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,List.getD_cons_zero]
    have hhead : symbolMsgs w off [x/16,x%16]=[[w,off,x/16,0],[w,off+1,x%16,0]] := by
      simp [symbolMsgs,List.range_succ]
    rw [hhead]
    simp only [Nat.mul_zero,Nat.add_zero]
    congr 1
    apply flatMap_congr'
    intro k _
    simp only [List.getD_cons_succ,Function.comp_def]
    rw [show off+(0+1+1)+2*k=off+2*k.succ by omega]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
