import ZkFormal.NearV3.Candidates.PairedNodeCanonical
import ZkFormal.NearV3.Rcpt.Candidates.NodePairedForest

namespace ZkFormal.NearV3.Candidates.PairedForestRelation
open NearSpec ZkFormal.Near Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- Each paired record retains its exact prestate allocation, including ordinal,
depth and node/value IDs. Only the semantic view is updated. -/
def RecordPair (s t : NodeS3) : Prop :=
  ∃tau d n v a b,WriteTreePair a b ∧
    s=seedNodeView tau d n v a ∧ t=pairedRecord tau d n v a b

inductive Aligned : List NodeS3 → List NodeS3 → Prop
  | nil : Aligned [] []
  | cons {s t : NodeS3} {ss ts : List NodeS3} :
      RecordPair s t → Aligned ss ts → Aligned (s::ss) (t::ts)

theorem Aligned.append {as bs cs ds : List NodeS3} (h : Aligned as bs)
    (g : Aligned cs ds) : Aligned (as++cs) (bs++ds) := by
  induction h with
  | nil => exact g
  | cons hr h ih => exact .cons hr ih

mutual
theorem nodes : ∀(tau d n v : Nat){a b : PTrie},WriteTreePair a b →
    Aligned (seedNodesT tau d n v a) (pairedNodes tau d n v a b)
  | _,_,_,_,_,_,.hash _ => .nil
  | tau,d,n,v,_,_,.leaf k m h =>
      .cons ⟨tau,d,n,v,_,_,.leaf k m h,rfl,rfl⟩ .nil
  | tau,d,n,v,_,_,.ext k m h =>
      .cons ⟨tau,d,n,v,_,_,.ext k m h,rfl,rfl⟩ (nodes tau (d+1) (n+1) v h)
  | tau,d,n,v,_,_,.branch m h hs =>
      .cons ⟨tau,d,n,v,_,_,.branch m h hs,rfl,rfl⟩ (children tau (d+1) (n+1) _ hs)
theorem children : ∀(tau d n v : Nat){a b : Kids},WriteKidsPair a b →
    Aligned (seedKidsT tau d n v a) (pairedChildNodes tau d n v a b)
  | _,_,_,_,_,_,.nil => .nil
  | tau,d,n,v,_,_,.none h => by
      simpa only [seedKidsT,pairedChildNodes] using children tau d n v h
  | tau,d,n,v,_,_,.some h hs =>
      (nodes tau d n v h).append (children tau d _ _ hs)
end

theorem forest : ∀(tau n v : Nat)(pairs : List (PTrie×PTrie)),
    (∀p∈pairs,WriteTreePair p.1 p.2) →
    Aligned (Assembly.forestNodes tau n v (pairs.map Prod.fst))
      (pairedForest tau n v pairs)
  | _,_,_,[],_ => .nil
  | tau,n,v,(a,b)::ps,h =>
      (nodes tau 0 n v (h (a,b) (by simp))).append
        (forest _ _ _ ps (fun p hp=>h p (by simp [hp])))

theorem member {ss ts : List NodeS3} (h : Aligned ss ts)
    (t : NodeS3) (ht : t∈ts) : ∃s∈ss,RecordPair s t := by
  induction h with
  | nil => simp at ht
  | @cons s t' ss ts hr h ih =>
    simp only [List.mem_cons] at ht
    rcases ht with rfl|ht
    · exact ⟨s,by simp,hr⟩
    · obtain ⟨s,hs,hr⟩:=ih ht
      exact ⟨s,by simp [hs],hr⟩

theorem forest_view_wf (pairs : List (PTrie×PTrie))
    (hp : ∀p∈pairs,WriteTreePair p.1 p.2)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true)
    (hb : Assembly.preBytes (pairs.map Prod.fst)≤2000000) :
    ∀s∈pairedForest 0 0 0 pairs,s.v.wf := by
  intro t ht
  obtain ⟨s,hs,tau,d,n,v,a,b,h,rfl,rfl⟩:=member (forest 0 0 0 pairs hp) t ht
  apply pairedNode_wf n v h
  have hold : ∀s∈Assembly.forestNodes 0 0 0 (pairs.map Prod.fst),s.v.wf := by
    intro s hs
    obtain ⟨o,ho,tau,d,n,v,rfl,_,_,_⟩:=forest_allocation _ 0 0 0 s hs
    exact native_forest_node_wf _ hw hb n v o ho
  exact hold _ hs

theorem forest_canonical (pairs : List (PTrie×PTrie))
    (hp : ∀p∈pairs,WriteTreePair p.1 p.2)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true)
    (hb : Assembly.preBytes (pairs.map Prod.fst)≤2000000) :
    ∀s∈pairedForest 0 0 0 pairs,∀x∈s.v.raw,x<ZkFormal.Algebra.P := by
  intro t ht
  obtain ⟨s,hs,tau,d,n,v,a,b,h,rfl,rfl⟩:=member (forest 0 0 0 pairs hp) t ht
  exact PairedNodeCanonical.node n v h (native_forest_canonical _ hw hb _ hs)

end ZkFormal.NearV3.Candidates.PairedForestRelation
