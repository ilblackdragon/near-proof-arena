import ZkFormal.NearV3.Render.Ups.ForestTerminalSafe
import ZkFormal.NearV3.Assembly.TraceHeads

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows ZkFormal.Near Assembly

/-- Heads with actual root occurrence targets. START-use counters remain seeds,
while native pre/post digests and root record positions match traceHeads. -/
def forestWalkHeads : Nat → Nat → List (PTrie×PTrie) → List HeadE
  | _,_,[] => []
  | tau,n,(pre,post)::rest =>
    {tau:=tau,rid:=n,rlen:=(nodeEnc pre).length,rres:=viewTarget n pre,mE:=0,
      pre:=pre.hashOf.map UInt8.toNat,post:=post.hashOf.map UInt8.toNat} ::
      forestWalkHeads (tau+1) (n+tsize pre) rest

/-- Only the previously unfilled root-resolution field changes. -/
theorem forestWalkHeads_trace : ∀ tau n pairs,
    (forestWalkHeads tau n pairs).map (fun h=>{h with rres:=0})=traceHeads tau n pairs
  | _,_,[] => rfl
  | tau,n,(pre,post)::rest => by simp [forestWalkHeads,traceHeads,forestWalkHeads_trace]

/-- Exact indexed START provider for every concrete forest root. -/
theorem forestWalkHeads_root : ∀ tau n v pairs i root,
    forestRootAt n v (pairs.map Prod.fst) i=some root →
    ∃ h,(forestWalkHeads tau n pairs)[i]?=some h ∧ h.tau=tau+i ∧ h.rid=root.nid ∧
      h.rres=viewTarget root.nid root.tree ∧ h.rlen=(nodeEnc root.tree).length ∧
      h.pre=root.tree.hashOf.map UInt8.toNat
  | _,_,_,[],_,_,h => by simp [forestRootAt] at h
  | tau,n,v,(pre,post)::rest,0,root,h => by
    simp only [List.map_cons,forestRootAt,Option.some.injEq] at h
    subst root
    exact ⟨_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | tau,n,v,(pre,post)::rest,i+1,root,h => by
    have hr : forestRootAt (n+tsize pre) (v+(valsOf pre).length) (rest.map Prod.fst) i=some root := h
    obtain ⟨head,hget,ht,hi,hres,hlen,hpre⟩ := forestWalkHeads_root (tau+1) _ _ rest i root hr
    exact ⟨head,hget,by omega,hi,hres,hlen,hpre⟩

theorem extended_root_resolved (n v d : Nat) (root : PTrie) (key : List Nat)
    (hf : root.find key≠none) :
    resolvedRecordId (pathRecordId (extendedAddresses n v d root key)) root=viewTarget n root := by
  have hmem : (⟨n,v,d,root⟩ : OccurrenceAddress)∈sourceAddresses n v d root key := by
    cases root <;> cases key <;> simp [sourceAddresses]
  have ha := occurrenceResolvedId_source_agrees hmem (resolveNative_isNode_of_known hf)
  rw [←ha]
  unfold occurrenceResolvedId
  rw [extendedAddresses_ids n v d root key (extendedAddresses_root n v d root key)]

/-- The native W0 START row names the head's actual resolved root occurrence.
This uses the concrete head list, rather than assuming a matching START edge. -/
theorem forest_start_provider {pairs : List (PTrie×PTrie)} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 (pairs.map Prod.fst) tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (hf : root.tree.find [0,15]≠none)
    (valueId : Slot→Nat) (resolvedId : PTrie→Nat) (baseI : UpsInst) (Qs : List UpsPartI) :
    ∃ h,(forestWalkHeads 0 0 pairs)[tau]?=some h ∧
      let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
      let I := nativeInstance recordId
        (nativeWalkBase recordId valueId resolvedId {baseI with tau:=tau} root.tree run value)
        root.tree run value Qs
      (step I 0).e++[0]=startEdgeMsg h 0 := by
  obtain ⟨h,hget,ht,_,hres,_,_⟩ := forestWalkHeads_root 0 0 0 pairs tau root hroot
  refine ⟨h,hget,?_⟩
  change [0,tau,SYM_START,
    (sourceLevelIds (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run).getD 0 0,
    0,EK_DOWN]++[0]=startEdgeMsg h 0
  rw [sourceLevelIds_resolvedRoot _ hr,extended_root_resolved _ _ _ _ _ hf]
  simp only [startEdgeMsg,hres,ht,Nat.zero_add,List.cons_append,List.nil_append]
end ZkFormal.NearV3.Render.UpsGen
