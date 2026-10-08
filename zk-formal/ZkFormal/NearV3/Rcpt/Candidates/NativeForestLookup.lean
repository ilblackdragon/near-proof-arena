import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupPayload

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen

def forestLookupNid (before : List PTrie) : Nat := (before.flatMap occs).length
def forestLookupVid (before : List PTrie) : Nat := (Assembly.forestBytes before).length

theorem forest_lookup_offsets (before after : List PTrie) (tree : PTrie)
    (hb : Assembly.preBytes (before++tree::after)≤2000000) :
    forestLookupNid before+tsize tree<P ∧ forestLookupVid before+(valsOf tree).length<P := by
  have hc:=forest_allocation_counts (before++tree::after) hb
  simp only [List.flatMap_append,List.flatMap_cons,List.length_append] at hc
  have hv : (Assembly.forestBytes (before++tree::after)).length=
      (Assembly.forestBytes before).length+(valsOf tree).length+(Assembly.forestBytes after).length := by
    simp [Assembly.forestBytes,List.flatMap_append,List.flatMap_cons,List.length_append,Nat.add_assoc]
  rw [hv] at hc
  unfold forestLookupNid forestLookupVid tsize P
  omega

theorem forest_lookup_payload (before after : List PTrie) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (hw : tree.wf=true)
    (hb : Assembly.preBytes (before++tree::after)≤2000000) (hk : ∀a∈key,a<16)
    (h : nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree key=some steps) :
    lookupPayloadSmall steps := by
  have hc:=forest_lookup_offsets before after tree hb
  apply nativeLookupSteps_payload _ _ tree key steps hw hc.1 hc.2 ?_ hk h
  intro o ho
  apply native_forest_key_bound (before++tree::after) hb o
  apply List.mem_flatMap.mpr
  exact ⟨tree,by simp,ho⟩

/-- Actual forest offsets and the unchanged native prestate-byte bound discharge
all edge payload ranges. Remaining input bounds are walk ID, forest size and key rows. -/
theorem native_forest_lookup_wf (before after : List PTrie) (tree : PTrie) (wid : Nat)
    (key : List Nat) (steps : List WStep3) (hw : tree.wf=true)
    (hb : Assembly.preBytes (before++tree::after)≤2000000)
    (hts : (before++tree::after).length≤P) (hwid : wid<P) (hk : ∀a∈key,a<16)
    (hlen : key.length+2≤2^23)
    (h : nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree key=some steps) :
    WalkWf3 [nativeLookupWalk wid before.length (forestLookupNid before) tree steps] := by
  have hc:=forest_lookup_offsets before after tree hb
  apply nativeLookupWalk_wf_of_payload wid before.length _ _ tree key steps hw hk h hwid ?_
    (Nat.le_of_lt hc.1) (forest_lookup_payload before after tree key steps hw hb hk h) hlen
  simp only [List.length_append,List.length_cons] at hts
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
