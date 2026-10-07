import ZkFormal.NearV3.Assembly.SourceAddresses
import ZkFormal.NearV3.Render.Ups.TreeEncodingTotal

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

mutual
def PathCovered (P : PTrie → Prop) : PTrie → List Nat → Prop
  | .ext k c m,key => P (.ext k c m) ∧ (isPrefix k key=true → PathCovered P c (key.drop k.length))
  | .branch sv cs m,slot::key => P (.branch sv cs m) ∧ KidsCovered P cs slot key
  | t,_ => P t
def KidsCovered (P : PTrie → Prop) : Kids → Nat → List Nat → Prop
  | .nil,_,_ => True
  | .none _,0,_ => True
  | .some c _,0,key => PathCovered P c key
  | .none rest,i+1,key => KidsCovered P rest i key
  | .some _ rest,i+1,key => KidsCovered P rest i key
end

def SourcesHave (P : PTrie → Prop) (run : TreeRun) : Prop :=
  P run.terminalSource ∧ ∀ p∈run.parts,P p.source

private theorem sourcesHave_push {P run} (h : SourcesHave P run) (part : TreePart)
    (hs : P part.source) : SourcesHave P (pushPart run part) := by
  refine ⟨h.1,?_⟩
  intro p hp
  simp only [pushPart,List.mem_append,List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact h.2 p hp
  · exact hs

private theorem leafSplit_sourcesHave (P : PTrie → Prop) (k : List Nat) (s : Slot) (m : Nat)
    (key : List Nat) (v : Bytes) (hs : P (.leaf k s m)) : SourcesHave P (leafSplitRun k s m key v) := by
  unfold leafSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length <;> cases h2 : key.drop p.length <;>
    simp only [h1,h2] <;> cases p <;> simp [SourcesHave,terminalRun,wrapRun,pushPart,hs]

private theorem extSplit_sourcesHave (P : PTrie → Prop) (k : List Nat) (c : PTrie) (m : Nat)
    (key : List Nat) (v : Bytes) (hs : P (.ext k c m)) : SourcesHave P (extSplitRun k c m key v) := by
  unfold extSplitRun
  generalize commonPrefix k key=p
  cases h1 : k.drop p.length with
  | nil => simp [h1,SourcesHave,terminalRun,hs]
  | cons x xs =>
    cases h2 : key.drop p.length <;> simp only [h1,h2] <;> cases xs <;> cases p <;>
      simp [SourcesHave,terminalRun,wrapRun,pushPart,hs]

mutual
theorem traceUpsert_covered (P : PTrie → Prop) : ∀ t key value run,
    PathCovered P t key → traceUpsert t key value=some run → SourcesHave P run
  | .hash _,_,_,_,_,h => by simp [traceUpsert] at h
  | .leaf k s m,key,value,run,hw,h => by
    by_cases he : k=key
    · simp only [traceUpsert,he,ite_true,Option.some.injEq] at h
      subst run
      simpa [SourcesHave,terminalRun,he,PathCovered] using hw
    · simp only [traceUpsert,he,ite_false,Option.some.injEq] at h
      subst run
      exact leafSplit_sourcesHave P k s m key value hw
  | .ext k c m,key,value,run,hw,h => by
    cases hp : isPrefix k key with
    | false =>
      simp only [traceUpsert,hp,Bool.false_eq_true,ite_false,Option.some.injEq] at h
      subst run
      exact extSplit_sourcesHave P k c m key value hw.1
    | true =>
      cases hm : c.mem? with
      | none => simp [traceUpsert,hp,hm] at h
      | some cm =>
        cases hr : traceUpsert c (key.drop k.length) value with
        | none => simp [traceUpsert,hp,hm,hr] at h
        | some inner =>
          simp only [traceUpsert,hp,ite_true,hm,hr,Option.some.injEq] at h
          subst run
          exact sourcesHave_push (traceUpsert_covered P c _ value inner (hw.2 hp) hr) _ hw.1
  | .branch bv cs m,[],value,run,hw,h => by
    simp only [traceUpsert,Option.some.injEq] at h
    subst run
    simpa [SourcesHave,terminalRun,PathCovered] using hw
  | .branch bv cs m,slot::key,value,run,hw,h => by
    cases hr : traceKids (.branch bv cs m) (slot::key) cs slot key value with
    | none => simp [traceUpsert,hr] at h
    | some inner =>
      simp only [traceUpsert,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact sourcesHave_push (traceKids_covered P _ _ cs slot key value inner hw.1 hw.2 hr) _ hw.1
theorem traceKids_covered (P : PTrie → Prop) : ∀ source wholeKey cs slot key value run,
    P source → KidsCovered P cs slot key →
    traceKids source wholeKey cs slot key value=some run → SourcesHave P run.inner
  | _,_,.nil,_,_,_,_,_,_,h => by simp [traceKids] at h
  | source,wholeKey,.none rest,0,key,value,run,hs,_,h => by
    simp only [traceKids,Option.some.injEq] at h
    subst run
    simpa [SourcesHave,terminalRun] using hs
  | source,wholeKey,.some c rest,0,key,value,run,hs,hw,h => by
    cases hm : c.mem? with
    | none => simp [traceKids,hm] at h
    | some cm =>
      cases hr : traceUpsert c key value with
      | none => simp [traceKids,hm,hr] at h
      | some inner =>
        simp only [traceKids,hm,hr,Option.some.injEq] at h
        subst run
        exact traceUpsert_covered P c key value inner hw hr
  | source,wholeKey,.none rest,i+1,key,value,run,hs,hw,h => by
    cases hr : traceKids source wholeKey rest i key value with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_covered P source wholeKey rest i key value inner hs hw hr
  | source,wholeKey,.some c rest,i+1,key,value,run,hs,hw,h => by
    cases hr : traceKids source wholeKey rest i key value with
    | none => simp [traceKids,hr] at h
    | some inner =>
      simp only [traceKids,hr,Option.map_some,Option.some.injEq] at h
      subst run
      exact traceKids_covered P source wholeKey rest i key value inner hs hw hr
end

mutual
theorem sourceAddresses_cover (P : PTrie → Prop) : ∀ n v d t key,
    (∀ a∈sourceAddresses n v d t key,P a.tree) → PathCovered P t key
  | n,v,d,.hash h,key,hp => hp ⟨n,v,d,.hash h⟩ (by simp [sourceAddresses])
  | n,v,d,.leaf k s m,key,hp => hp ⟨n,v,d,.leaf k s m⟩ (by simp [sourceAddresses])
  | n,v,d,.ext k c m,key,hp => by
    refine ⟨hp ⟨n,v,d,.ext k c m⟩ (by simp [sourceAddresses]),?_⟩
    intro hk
    exact sourceAddresses_cover P (n+1) v (d+1) c _
      (fun a ha => hp a (by simp [sourceAddresses,hk,ha]))
  | n,v,d,.branch sv cs m,[],hp => hp ⟨n,v,d,.branch sv cs m⟩ (by simp [sourceAddresses])
  | n,v,d,.branch sv cs m,slot::key,hp => by
    refine ⟨hp ⟨n,v,d,.branch sv cs m⟩ (by simp [sourceAddresses]),?_⟩
    exact kidSourceAddresses_cover P (n+1) (v+(optSlotVal sv).length) (d+1) cs slot key
      (fun a ha => hp a (by simp [sourceAddresses,ha]))
theorem kidSourceAddresses_cover (P : PTrie → Prop) : ∀ n v d cs slot key,
    (∀ a∈kidSourceAddresses n v d cs slot key,P a.tree) → KidsCovered P cs slot key
  | _,_,_,.nil,_,_,_ => trivial
  | _,_,_,.none _,0,_,_ => trivial
  | n,v,d,.some c _,0,key,hp => sourceAddresses_cover P n v d c key hp
  | n,v,d,.none rest,i+1,key,hp => kidSourceAddresses_cover P n v d rest i key hp
  | n,v,d,.some c rest,i+1,key,hp =>
      kidSourceAddresses_cover P (n+tsize c) (v+(valsOf c).length) d rest i key hp
end

/-- Actual successful native tracing places every emitted source, including PT
and repeated split-terminal sources, in the executable full address list. -/
theorem traceUpsert_source_addresses {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (n v d : Nat) :
    (∃ a∈sourceAddresses n v d t key,a.tree=run.terminalSource) ∧
      ∀ p∈run.parts,∃ a∈sourceAddresses n v d t key,a.tree=p.source := by
  let P := fun tree => ∃ a∈sourceAddresses n v d t key,a.tree=tree
  exact traceUpsert_covered P t key value run
    (sourceAddresses_cover P n v d t key (fun a ha => ⟨a,ha,rfl⟩)) hr

/-- Every emitted source obtains its actual coherent occurrence ID. -/
theorem traceUpsert_source_id {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) (n v d : Nat) {p : TreePart} (hp : p∈run.parts) :
    ∃ a∈sourceAddresses n v d t key,a.tree=p.source ∧
      pathRecordId (sourceAddresses n v d t key) p.source=a.nid := by
  obtain ⟨a,ha,he⟩ := (traceUpsert_source_addresses hr n v d).2 p hp
  exact ⟨a,ha,he,he ▸ sourceAddresses_ids n v d t key ha⟩

/-- Final source-provider lookup for the current renderer's recordId interface.
Every actual part (including PT and split parts) names its exact forest seed. -/
theorem forest_traceUpsert_source_provider {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree key value=some run) {p : TreePart} (hp : p∈run.parts) :
    ∃ a∈sourceAddresses root.nid root.vid root.depth root.tree key,
      a.tree=p.source ∧
      pathRecordId (sourceAddresses root.nid root.vid root.depth root.tree key) p.source=a.nid ∧
      (forestStoreViews ts).nodes[a.nid]?=some (seedNodeView tau a.depth a.nid a.vid p.source) := by
  obtain ⟨a,ha,he,hid⟩ := traceUpsert_source_id hr root.nid root.vid root.depth hp
  have hs := forestRootAt_view (ns:=forestNodes 0 0 0 ts) 0 0 0 ts tau root (by simp) hroot
  have hv := sourceAddresses_view _ _ _ _ _ hs a ha
  have hn : isNode a.tree=true := he ▸ (traceUpsert_nodeParts _ _ _ _ hr p hp).1
  refine ⟨a,ha,he,hid,?_⟩
  simpa only [forestStoreViews,Nat.zero_add,he] using hv.get hn

end ZkFormal.NearV3.Assembly
