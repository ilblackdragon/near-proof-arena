import ZkFormal.NearV3.Assembly.OccurrenceAddress

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def forestRootAt : Nat → Nat → List PTrie → Nat → Option OccurrenceAddress
  | _,_,[],_ => none
  | n,v,t::_,0 => some ⟨n,v,0,t⟩
  | n,v,t::ts,i+1 => forestRootAt (n+tsize t) (v+(valsOf t).length) ts i

theorem forestRootAt_segment {L VL D} : ∀ tau n v ts i a,
    L.drop n=forestRecs tau n v ts → VL.drop v=forestVals tau ts →
    D.drop n=forestDepths ts → forestRootAt n v ts i=some a →
    Seg L VL D (tau+i) a.nid a.vid a.depth a.tree
  | _,_,_,[],_,_,_,_,_,h => by simp [forestRootAt] at h
  | tau,n,v,t::ts,0,a,hn,hv,hd,h => by
    simp only [forestRootAt,Option.some.injEq] at h
    subst a
    exact ⟨⟨_,hn⟩,⟨_,hv⟩,⟨_,hd⟩⟩
  | tau,n,v,t::ts,i+1,a,hn,hv,hd,h => by
    have hn' := drop_of_append hn
    have hv' := drop_of_append hv
    have hd' := drop_of_append hd
    simp only [recsT_length] at hn'
    simp only [valsT,List.length_map] at hv'
    simp only [depsT_length] at hd'
    simpa only [Nat.add_assoc,Nat.add_comm 1 i] using
      forestRootAt_segment (tau+1) (n+tsize t) (v+(valsOf t).length) ts i a hn' hv' hd' h

/-- Concrete forest records authenticate every located occurrence. -/
theorem forest_located_record {ts : List PTrie} {tau : Nat} {root a : OccurrenceAddress}
    (hr : forestRootAt 0 0 ts tau=some root) {steps : List OccurrenceStep}
    (ha : locateOccurrence root steps=some a) (hn : isNode a.tree=true) :
    (forestRecs 0 0 0 ts)[a.nid]?=some ⟨tau,recT a.nid a.vid a.tree⟩ ∧
      fullTree (forestRecs 0 0 0 ts) (forestVals 0 ts) a.nid=a.tree := by
  have hs := forestRootAt_segment (L:=forestRecs 0 0 0 ts) (VL:=forestVals 0 ts)
    (D:=forestDepths ts) 0 0 0 ts tau root (by simp) (by simp) (by simp) hr
  simpa only [Nat.zero_add] using locateOccurrence_record hs ha hn

/-- The concrete seeded NodeS3 list contains the authenticated provider at the
located address. Value IDs are the forest's actual shared address space. -/
theorem forest_located_view {ts : List PTrie} {tau : Nat} {root a : OccurrenceAddress}
    (hw : ∀ t ∈ ts,t.wf=true) (hc : (forestBytes ts).length ≤ ZkFormal.Algebra.P)
    (hr : forestRootAt 0 0 ts tau=some root) {steps : List OccurrenceStep}
    (ha : locateOccurrence root steps=some a) (hn : isNode a.tree=true) :
    ∃ s, (forestStoreViews ts).nodes[a.nid]?=some s ∧
      (⟨s.tau,s.v.toRec3 (forestStoreViews ts).valuePosition⟩ : NodeRec3)=
        ⟨tau,recT a.nid a.vid a.tree⟩ := by
  have hg := (forest_located_record hr ha hn).1
  rw [←(forestStoreViews_records ts hw hc).1] at hg
  simp only [Link3.recsOf,List.getElem?_map,Option.map_eq_some_iff] at hg
  exact hg

end ZkFormal.NearV3.Assembly
