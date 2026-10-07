import ZkFormal.NearV3.Render.Ups.MemArith

/-! Bounds on complete memory arithmetic operands, including scalar constants and
all combined byte contributions. Prefix bounds refer to existing serialized row caps. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

private theorem byteGet {xs : List Nat} (hb : ∀ b∈xs,b<256) (i : Nat) :
    0≤(xs.getD i 0 : Int) ∧ (xs.getD i 0 : Int)<256 := by
  have h : xs.getD i 0<256 := by
    rw [List.getD_eq_getElem?_getD]
    cases he : xs[i]? with
    | none => simp
    | some b => exact hb b (List.mem_of_getElem? he)
  omega

private theorem bitMul {a x : Int} (ha : 0≤a ∧ a≤1) (hx : 0≤x ∧ x<256) :
    0≤a*x ∧ a*x<256 := by
  rcases (show a=0 ∨ a=1 by omega) with rfl|rfl <;> omega

/-- Boolean selectors and full scalar constants from ordinary constructor metadata. -/
theorem scalar_metadata_bounds (I : UpsInst) (Q : UpsPartI)
    (hk : Q.kind<12) (hc : I.ci<11) (hq : Q.qhk<2^22) (hp : Q.phk<2^22) :
    (0≤useAV I Q ∧ useAV I Q≤1) ∧ (0≤bNV I Q ∧ bNV I Q≤1) ∧
    (0≤bLV Q ∧ bLV Q≤1) ∧ (0≤cOV Q ∧ cOV Q≤1) ∧
    (0≤cSV Q ∧ cSV Q≤1) ∧ (0≤eLV Q ∧ eLV Q≤1) ∧
    (0≤eSV I Q ∧ eSV I Q≤1) ∧
    (0≤KcV I Q ∧ KcV I Q<2^23+100) ∧ (0≤CcV I Q ∧ CcV I Q<2^23+50) := by
  have hk' : Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=2 ∨ Q.kind=3 ∨ Q.kind=4 ∨ Q.kind=5 ∨
      Q.kind=6 ∨ Q.kind=7 ∨ Q.kind=8 ∨ Q.kind=9 ∨ Q.kind=10 ∨ Q.kind=11 := by omega
  have hc' : I.ci=0 ∨ I.ci=1 ∨ I.ci=2 ∨ I.ci=3 ∨ I.ci=4 ∨ I.ci=5 ∨
      I.ci=6 ∨ I.ci=7 ∨ I.ci=8 ∨ I.ci=9 ∨ I.ci=10 := by omega
  rcases hk' with h|h|h|h|h|h|h|h|h|h|h|h <;>
    rcases hc' with c|c|c|c|c|c|c|c|c|c|c <;>
    simp [useAV,bNV,bLV,cOV,cSV,eLV,eSV,KcV,CcV,kin,cin,xcpV,XcpB,spRecv,h,c,ind] <;>
    (repeat' (apply And.intro)) <;> omega

/-- Complete per-limb inputs fit the proposed wide carry range. This includes all
Kc/Cc, old-memory, child-memory and value-length terms, not separate constant bounds. -/
theorem memory_scalar_sums (I : UpsInst) (Q : UpsPartI)
    (hk : Q.kind<12) (hc : I.ci<11) (hq : Q.qhk<2^22) (hp : Q.phk<2^22)
    (hn : Q.neg≤1) (hL : L I<2^24) (hb : ∀ b∈Q.pb,b<256)
    (hchild : ∀ b∈(child I Q).pb,b<256) :
    (∀ i, i<7 → -(2^23+1024)≤sigV Q*X1V I Q i ∧ sigV Q*X1V I Q i≤2^23+1024) ∧
    (∀ i, i<8 → 0≤EinV I Q i ∧ EinV I Q i≤2^23+1024) := by
  obtain ⟨hua,hbn,hbl,hco,hcs,hel,hes,hK,hC⟩ := scalar_metadata_bounds I Q hk hc hq hp
  have hl : ∀ i,0≤Lb I i ∧ Lb I i<256 := by
    intro i; unfold Lb; split <;> (try split) <;> (try split) <;> omega
  have hs : ∀ i,0≤slb Q i ∧ slb Q i<256 := by
    intro i; unfold slb; split
    · exact byteGet hb _
    · omega
  constructor
  · intro i hi
    have ha := bitMul hua (byteGet hb (((Q.pb.length : Int)-8+i).toNat))
    have hbi := bitMul hbn (show 0≤limb Q.mB i ∧ limb Q.mB i<256 by simp only [limb,hi,ite_true]; omega)
    have hbli := bitMul hbl (hl i)
    have hci := bitMul hco (byteGet hchild ((child I Q).pb.length-8+i))
    have hcsi := bitMul hcs (hs i)
    have hz : 0≤ind (i=0)*CcV I Q ∧ ind (i=0)*CcV I Q<2^23+50 := by
      by_cases hi0 : i=0 <;> simp [ind,hi0] <;> omega
    change 0≤useAV I Q*memRb Q i ∧ useAV I Q*memRb Q i<256 at ha
    change 0≤cOV Q*memByte (child I Q) i ∧ cOV Q*memByte (child I Q) i<256 at hci
    rcases (show Q.neg=0 ∨ Q.neg=1 by omega) with hneg|hneg <;>
      simp only [sigV,hneg,Int.natCast_zero,Int.natCast_one,Int.mul_zero,Int.mul_one,
        Int.sub_zero,Int.reduceMul,Int.reduceSub,Int.one_mul,Int.neg_one_mul,X1V,Ai,Bi,Ci] <;> omega
  · intro i hi
    have he1 := bitMul hel (hl i)
    have he2 := bitMul hes (hs i)
    have hz : 0≤ind (i=0)*KcV I Q ∧ ind (i=0)*KcV I Q<2^23+100 := by
      by_cases hi0 : i=0 <;> simp [ind,hi0] <;> omega
    unfold EinV
    omega
end ZkFormal.NearV3.Render.UpsGen
