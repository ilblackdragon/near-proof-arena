import ZkFormal.NearV3.Assembly.ForestStore

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- Occurrence-sensitive address; equal subtrees at different paths retain
separate node/value positions. -/
structure OccurrenceAddress where
  nid : Nat
  vid : Nat
  depth : Nat
  tree : PTrie

inductive OccurrenceStep where
  | ext
  | branch (slot : Nat)
  deriving DecidableEq

def locateKid (depth : Nat) : Nat → Nat → Kids → Nat → Option OccurrenceAddress
  | _,_,.nil,_ => none
  | _,_,.none _,0 => none
  | n,v,.some c _,0 => some ⟨n,v,depth,c⟩
  | n,v,.none rest,i+1 => locateKid depth n v rest i
  | n,v,.some c rest,i+1 => locateKid depth (n+tsize c) (v+(valsOf c).length) rest i

def locateOccurrence : OccurrenceAddress → List OccurrenceStep → Option OccurrenceAddress
  | a,[] => some a
  | ⟨n,v,d,.ext _ c _⟩,.ext::steps => locateOccurrence ⟨n+1,v,d+1,c⟩ steps
  | ⟨n,v,d,.branch sv cs _⟩,.branch i::steps =>
      (locateKid (d+1) (n+1) (v+(optSlotVal sv).length) cs i).bind
        (fun a => locateOccurrence a steps)
  | _,_ => none

theorem locateKid_segment {L VL D tau} : ∀ depth n v cs i a,
    KSeg L VL D tau n v depth cs → locateKid depth n v cs i=some a →
    Seg L VL D tau a.nid a.vid a.depth a.tree
  | _,_,_,.nil,_,_,_,h => by simp [locateKid] at h
  | _,_,_,.none _,0,_,_,h => by simp [locateKid] at h
  | d,n,v,.some c rest,0,a,hs,h => by
    simp only [locateKid,Option.some.injEq] at h
    subst a
    exact hs.some_c
  | d,n,v,.none rest,i+1,a,hs,h => locateKid_segment d n v rest i a hs.none_r h
  | d,n,v,.some c rest,i+1,a,hs,h =>
    locateKid_segment d (n+tsize c) (v+(valsOf c).length) rest i a hs.some_r h

theorem locateOccurrence_segment {L VL D tau} (steps : List OccurrenceStep) :
    ∀ a b, Seg L VL D tau a.nid a.vid a.depth a.tree →
      locateOccurrence a steps=some b → Seg L VL D tau b.nid b.vid b.depth b.tree := by
  induction steps with
  | nil => intro a b hs h; cases h; exact hs
  | cons step steps ih =>
    intro a b hs h
    obtain ⟨n,v,d,t⟩ := a
    cases step <;> cases t <;> simp only [locateOccurrence] at h
    all_goals try contradiction
    · exact ih _ b hs.ext_kid h
    · rename_i slot sv cs mem
      cases hl : locateKid (d+1) (n+1) (v+(optSlotVal sv).length) cs slot with
      | none => simp [hl] at h
      | some mid =>
        simp only [hl,Option.bind_some] at h
        exact ih mid b (locateKid_segment _ _ _ _ _ _ hs.br_kids hl) h

/-- A successful path lookup names the actual global record and reconstructed
subtree, with no structural-equality-to-ID assumption. -/
theorem locateOccurrence_record {L VL D tau} {a b : OccurrenceAddress}
    (hs : Seg L VL D tau a.nid a.vid a.depth a.tree) {steps : List OccurrenceStep}
    (hl : locateOccurrence a steps=some b) (hn : isNode b.tree=true) :
    L[b.nid]?=some ⟨tau,recT b.nid b.vid b.tree⟩ ∧
      fullTree L VL b.nid=b.tree := by
  have hb := locateOccurrence_segment steps a b hs hl
  exact ⟨(hb.get hn).1,hb.tree hn L.length (by have := hb.len; omega)⟩

end ZkFormal.NearV3.Assembly
