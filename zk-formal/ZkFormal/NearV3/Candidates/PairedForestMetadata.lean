import ZkFormal.NearV3.Candidates.PairedForestRelation

namespace ZkFormal.NearV3.Candidates.PairedForestMetadata
open NearSpec ZkFormal.Near Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
open PairedForestRelation

theorem aligned_length {ss ts : List NodeS3} (h : Aligned ss ts) : ss.length=ts.length := by
  induction h with
  | nil => rfl
  | cons hr h ih => simpa using congrArg Nat.succ ih

theorem aligned_get {ss ts : List NodeS3} (h : Aligned ss ts) :
    ∀(i : Nat) (t : NodeS3),ts[i]?=some t → ∃s,ss[i]?=some s ∧ RecordPair s t := by
  induction h with
  | nil => intro i t ht; simp at ht
  | @cons s t ss ts hr h ih =>
    intro i o ho
    cases i with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at ho; subst o; exact ⟨s,rfl,hr⟩
    | succ i => exact ih i o ho

theorem record_fields {s t : NodeS3} (h : RecordPair s t) :
    s.tau=t.tau ∧ s.depth=t.depth ∧ s.res=t.res ∧ s.ubm=t.ubm ∧ s.repE=t.repE := by
  obtain ⟨tau,d,n,v,a,b,_,rfl,rfl⟩:=h
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem record_res {s t : NodeS3} (h : RecordPair s t) (i : Nat) : s.resOk i ↔ t.resOk i := by
  obtain ⟨tau,d,n,v,a,b,h,rfl,rfl⟩:=h
  cases h with
  | hash hh => rfl
  | leaf k m hs => rfl
  | branch m hv hcs => rfl
  | ext k m hc =>
    cases k with
    | cons x xs => rfl
    | nil =>
      cases hc <;> rfl

theorem forest_depth (pairs : List (PTrie×PTrie))
    (hp : ∀p∈pairs,WriteTreePair p.1 p.2)
    (hd : ∀t∈pairs.map Prod.fst,∀k,fdepth t k≤NearSpecV3.trieFuel) :
    ∀s∈pairedForest 0 0 0 pairs,s.depth<400 := by
  intro t ht
  obtain ⟨s,hs,hr⟩:=member (forest 0 0 0 pairs hp) t ht
  rw [←(record_fields hr).2.1]
  exact native_forest_depth _ 0 0 0 hd s hs

theorem forest_res (pairs : List (PTrie×PTrie))
    (hp : ∀p∈pairs,WriteTreePair p.1 p.2) (i : Nat) (s : NodeS3)
    (hs : (pairedForest 0 0 0 pairs)[i]?=some s) : s.resOk i := by
  obtain ⟨o,ho,hr⟩:=aligned_get (forest 0 0 0 pairs hp) i s hs
  apply (record_res hr i).mp
  simpa using forest_index_res (pairs.map Prod.fst) 0 0 0 i o ho

end ZkFormal.NearV3.Candidates.PairedForestMetadata
