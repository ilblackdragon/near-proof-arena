import ZkFormal.NearV3.Assembly.RcptRoutingInactive

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def routingNextCoord (p : ReceiptPlan) (i : Nat) : Coord :=
  if i+1<p.input.receipt.receiverId.length then ⟨sV,i+1,p.input.receipt.receiverId.length⟩ else ⟨sRID,0,32⟩

theorem routing_next_active (p : ReceiptPlan) (i : Nat) : routingActive (routingNextCoord p i)=true := by
  unfold routingNextCoord
  split <;> rfl

theorem routing_next_position (p : ReceiptPlan) (i : Nat) (hi : i<p.input.receipt.receiverId.length) :
    routingPosition p (routingNextCoord p i)=i+1 := by
  unfold routingNextCoord
  split
  · rfl
  · simp only [routingPosition,sRID,sV,Nat.reduceEqDiff,ite_false]
    omega

theorem routing_receiver_next_cells (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<p.input.receipt.receiverId.length)
    (col : Nat) (hc : col=eqL ∨ col=eqH) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (routingAux interval fallback))) p (routingNextCoord p i) col=
      frameNext (frameOf p.input.receipt.receiverId (interval p) i) col := by
  have hh := routingAux_transport interval constants pub digests tokens fallback p (routingNextCoord p i) col
    (routing_next_active p i) (by rcases hc with rfl|rfl <;> decide)
  simp only [receiptRoutingFrame,routing_next_position p i hi] at hh
  apply hh.trans
  rcases hc with rfl|rfl
  · exact frame_prefix_lower _ _ _
  · exact frame_prefix_upper _ _ _

theorem routing_receiver_local (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i : Nat) (hi : i<p.input.receipt.receiverId.length)
    (hv : inInterval p.input.receipt.receiverId (interval p)=true)
    (hu : ∀v∈(interval p).2.getD [],0<v.toNat) :
    ∀e∈cRoute,e.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (routingAux interval fallback))) p
      ⟨sV,i,p.input.receipt.receiverId.length⟩ (routingNextCoord p i)) 0 0 pub=0 := by
  apply routing_adjusted_transport _ _ _ _ (frameOf p.input.receipt.receiverId (interval p) i)
    (frameOf_ordered _ _ _ (Nat.le_of_lt hi) hv hu) p.input.receipt.receiverId.length 0
  · exact routing_receiver_current interval constants pub digests tokens fallback p i _ hi
  · exact routing_receiver_next_cells interval constants pub digests tokens fallback p i hi

end ZkFormal.NearV3.Assembly.RcptSkeleton
