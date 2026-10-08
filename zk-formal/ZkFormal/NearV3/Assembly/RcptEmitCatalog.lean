import ZkFormal.NearV3.Assembly.RcptEmitPatch

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem emits_lookup {state : Nat} {ems : List Em} (hm : (state,ems)∈emits) :
    emits.find? (fun p=>p.1==state)=some (state,ems) := by
  simp only [emits,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm <;> cases hm <;> rfl

theorem emits_zero_lookup : emits.find? (fun p=>p.1==0)=none := rfl

def emissionNoSelf (em : Em) : Bool :=
  noEmissionExpr em.1 && noEmissionExpr em.2.1 && noEmissionExpr em.2.2.1 && noEmissionExpr em.2.2.2

set_option maxRecDepth 4096 in
theorem emits_noSelf : emits.all (fun p=>p.2.all emissionNoSelf)=true := by decide

theorem emission_noSelf (state : Nat) (ems : List Em) (hm : (state,ems)∈emits)
    (id pos val gate : Expr) (he : (id,pos,val,gate)∈ems) :
    noEmissionExpr id=true ∧ noEmissionExpr pos=true ∧ noEmissionExpr val=true ∧ noEmissionExpr gate=true := by
  have hh := List.all_eq_true.mp (List.all_eq_true.mp emits_noSelf (state,ems) hm) (id,pos,val,gate) he
  simpa only [emissionNoSelf,Bool.and_eq_true,and_assoc] using hh

theorem emissionValues_some (base : Trace Fp) (pub : List Fp) (t r state slot : Nat)
    (ems : List Em) (hm : (state,ems)∈emits) (id pos val gate : Expr)
    (he : ems[slot]?=some (id,pos,val,gate)) :
    emissionValues base pub t r state slot=
      ⟨id.eval base t r pub,pos.eval base t r pub,val.eval base t r pub,gate.eval base t r pub⟩ := by
  simp only [emissionValues,emits_lookup hm,he]

theorem emissionValues_none (base : Trace Fp) (pub : List Fp) (t r state slot : Nat)
    (ems : List Em) (hm : (state,ems)∈emits) (he : ems[slot]?=none) :
    emissionValues base pub t r state slot=⟨0,0,0,0⟩ := by
  simp only [emissionValues,emits_lookup hm,he]

theorem emissionPatch_slot (base : Trace Fp) (pub : List Fp) (stateAt : Nat→Nat→Nat)
    (t pos slot : Nat) (hs : slot<3) :
    (emissionPatch base pub stateAt).cell t pos (eId slot)=(emissionValues base pub t pos (stateAt t pos) slot).id ∧
    (emissionPatch base pub stateAt).cell t pos (ePos slot)=(emissionValues base pub t pos (stateAt t pos) slot).pos ∧
    (emissionPatch base pub stateAt).cell t pos (eV slot)=(emissionValues base pub t pos (stateAt t pos) slot).value ∧
    (emissionPatch base pub stateAt).cell t pos (eG slot)=(emissionValues base pub t pos (stateAt t pos) slot).gate := by
  have hh : slot=0 ∨ slot=1 ∨ slot=2 := by omega
  rcases hh with rfl|rfl|rfl <;> exact ⟨rfl,rfl,rfl,rfl⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
