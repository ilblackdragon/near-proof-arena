import ZkFormal.NearV3.Assembly.RcptSkeleton

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

def shapeCell (x : Input) (col : Nat) : Fp :=
  if col=Lp then Fp.ofNat x.receipt.predecessorId.length else
  if col=Lv then Fp.ofNat x.receipt.receiverId.length else
  if col=Ls then Fp.ofNat x.receipt.signerId.length else
  if col=kt then Fp.ofNat x.receipt.signerPk.tag else
  if col=hr then (if x.refund then 1 else 0) else 0

def shapeTrace (x : Input) : Trace Fp := ⟨fun _=>1,fun _ _=>shapeCell x⟩

theorem fields_states (refund : Bool) : ∀s∈fields refund,s∈states := by
  cases refund <;> decide

theorem states_limits {s : Nat} (hs : s∈states) : 4≤s ∧ s≤26 := by
  simp only [states,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,sXRI,
    sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ,List.mem_cons,List.not_mem_nil,or_false] at hs
  omega

theorem fields_positive (x : Input) (hw : x.receipt.wf=true) :
    ∀s∈fields x.refund,0<fieldLen x s := by
  have hp : 2≤x.receipt.predecessorId.length ∧ 2≤x.receipt.receiverId.length ∧
      2≤x.receipt.signerId.length := by
    simp only [Receipt.wf,AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hw
    grind only
  intro s hs
  have hlim := states_limits (fields_states x.refund s hs)
  have hd : s=4 ∨ s=5 ∨ s=6 ∨ s=7 ∨ s=8 ∨ s=9 ∨ s=10 ∨ s=11 ∨ s=12 ∨ s=13 ∨ s=14 ∨ s=15 ∨ s=16 ∨ s=17 ∨ s=18 ∨ s=19 ∨ s=20 ∨ s=21 ∨ s=22 ∨ s=23 ∨ s=24 ∨ s=25 ∨ s=26 := by omega
  rcases hd with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst s <;>
    simp [fieldLen,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,sXRI,
      sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ] <;> omega

theorem receiptRows_valid (x : Input) (hw : x.receipt.wf=true) {row : Coord}
    (hrow : row∈receiptRows x) :
    row.state∈states ∧ row.index<row.length ∧ row.length=fieldLen x row.state ∧ 0<row.length := by
  obtain ⟨s,hs,hseg⟩ := List.mem_flatMap.mp hrow
  obtain ⟨hstate,hidx,hlen⟩ := segment_member hseg
  refine ⟨hstate ▸ fields_states x.refund s hs,?_,?_,?_⟩
  · simpa only [hlen] using hidx
  · simpa only [hstate] using hlen
  · rw [hlen]; exact fields_positive x hw s hs

end ZkFormal.NearV3.Assembly.RcptSkeleton
