import ZkFormal.NearV3.Candidates.ProcPriorIdCarryFields
import ZkFormal.NearV3.Candidates.ProcPriorRawBoolean
namespace ZkFormal.NearV3.Candidates.ProcPriorIdGateFields
open ZkFormal.Algebra ProcPriorIdRows ProcPriorCells ProcPriorIdCells

theorem bit_and (a b : Bool) : bit (a && b)=bit a*bit b := by
  cases a <;> cases b <;> simp [bit] <;> grind

theorem gates (a b : Row) :
    bit (gateMid a (some b))=bit (sameTop a (some b))*bit (sameMid a (some b)) ∧
    bit (gateAll a (some b))=bit (gateMid a (some b))*bit (sameLo a (some b)) ∧
    bit (gateAll a (some b) && a.event.isPublic && nextPublic (some b))=
      bit (gateAll a (some b))*bit a.event.isPublic*bit b.event.isPublic := by
  simp only [gateMid,gateAll,nextPublic,Option.any_some,bit_and]
  exact ⟨trivial,trivial,trivial⟩

theorem limb_inverse (f : Nat→Nat) (a b : Row)
    (ha:f a.event.key<P) (hb:f b.event.key<P) :
    let delta:=Fp.ofNat (f b.event.key)-Fp.ofNat (f a.event.key)
    delta*invLimb f a (some b)=1-bit (eqLimb f a (some b)) ∧
    delta*bit (eqLimb f a (some b))=0 := by
  dsimp only
  have hi:=ProcPriorRawBoolean.inv_delta (f b.event.key) (f a.event.key) hb ha
  by_cases h:f a.event.key=f b.event.key
  · simp [invLimb,eqLimb,h,bit]
    grind
  · have hr:f b.event.key≠f a.event.key:=Ne.symm h
    simp [invLimb,eqLimb,h,hr,bit] at hi ⊢
    exact ⟨hi, by grind⟩

end ZkFormal.NearV3.Candidates.ProcPriorIdGateFields
