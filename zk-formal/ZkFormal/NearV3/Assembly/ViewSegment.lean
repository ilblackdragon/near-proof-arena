import ZkFormal.NearV3.Assembly.ForestAddress

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

def ViewSegment (ns : List NodeS3) (tau n v d : Nat) (t : PTrie) : Prop :=
  ∃ rest, ns.drop n=seedNodesT tau d n v t ++ rest

def KidViewSegment (ns : List NodeS3) (tau n v d : Nat) (cs : Kids) : Prop :=
  ∃ rest, ns.drop n=seedKidsT tau d n v cs ++ rest

theorem ViewSegment.ext {ns tau n v d key child mem}
    (h : ViewSegment ns tau n v d (.ext key child mem)) :
    ViewSegment ns tau (n+1) v (d+1) child := by
  obtain ⟨r,h⟩ := h
  exact ⟨r,drop_succ_of h⟩

theorem ViewSegment.branch {ns tau n v d value kids mem}
    (h : ViewSegment ns tau n v d (.branch value kids mem)) :
    KidViewSegment ns tau (n+1) (v+(optSlotVal value).length) (d+1) kids := by
  obtain ⟨r,h⟩ := h
  exact ⟨r,drop_succ_of h⟩

theorem KidViewSegment.none {ns tau n v d rest}
    (h : KidViewSegment ns tau n v d (.none rest)) : KidViewSegment ns tau n v d rest := h

theorem KidViewSegment.child {ns tau n v d child rest}
    (h : KidViewSegment ns tau n v d (.some child rest)) : ViewSegment ns tau n v d child := by
  obtain ⟨r,h⟩ := h
  exact ⟨_,by simpa [seedKidsT,List.append_assoc] using h⟩

theorem KidViewSegment.rest {ns tau n v d child rest}
    (h : KidViewSegment ns tau n v d (.some child rest)) :
    KidViewSegment ns tau (n+tsize child) (v+(valsOf child).length) d rest := by
  obtain ⟨r,h⟩ := h
  simp only [seedKidsT,List.append_assoc] at h
  have hh := drop_of_append h
  rw [seedNodesT_length] at hh
  exact ⟨r,hh⟩

theorem ViewSegment.get {ns tau n v d t} (h : ViewSegment ns tau n v d t)
    (hn : isNode t=true) : ns[n]?=some (seedNodeView tau d n v t) := by
  obtain ⟨r,h⟩ := h
  cases t <;> simp only [isNode] at hn
  · contradiction
  all_goals exact get_of_drop h

theorem locateKid_view {ns tau} : ∀ d n v cs i a,
    KidViewSegment ns tau n v d cs → locateKid d n v cs i=some a →
    ViewSegment ns tau a.nid a.vid a.depth a.tree
  | _,_,_,.nil,_,_,_,h => by simp [locateKid] at h
  | _,_,_,.none _,0,_,_,h => by simp [locateKid] at h
  | _,_,_,.some _ _,0,a,hs,h => by cases h; exact hs.child
  | d,n,v,.none rest,i+1,a,hs,h => locateKid_view d n v rest i a hs.none h
  | d,n,v,.some c rest,i+1,a,hs,h =>
    locateKid_view d (n+tsize c) (v+(valsOf c).length) rest i a hs.rest h

theorem locateOccurrence_view {ns tau} (steps : List OccurrenceStep) :
    ∀ a b, ViewSegment ns tau a.nid a.vid a.depth a.tree →
      locateOccurrence a steps=some b → ViewSegment ns tau b.nid b.vid b.depth b.tree := by
  induction steps with
  | nil => intro a b hs h; cases h; exact hs
  | cons step steps ih =>
    intro a b hs h
    obtain ⟨n,v,d,t⟩ := a
    cases step <;> cases t <;> simp only [locateOccurrence] at h
    all_goals try contradiction
    · exact ih _ b hs.ext h
    · rename_i slot sv cs mem
      cases hl : locateKid (d+1) (n+1) (v+(optSlotVal sv).length) cs slot with
      | none => simp [hl] at h
      | some mid =>
        simp only [hl,Option.bind_some] at h
        exact ih mid b (locateKid_view _ _ _ _ _ _ hs.branch hl) h

theorem forestRootAt_view {ns} : ∀ tau n v ts i a,
    ns.drop n=forestNodes tau n v ts → forestRootAt n v ts i=some a →
    ViewSegment ns (tau+i) a.nid a.vid a.depth a.tree
  | _,_,_,[],_,_,_,h => by simp [forestRootAt] at h
  | tau,n,v,t::ts,0,a,hn,h => by
    simp only [forestRootAt,Option.some.injEq] at h
    subst a
    exact ⟨_,hn⟩
  | tau,n,v,t::ts,i+1,a,hn,h => by
    have hn' := drop_of_append hn
    simp only [seedNodesT_length] at hn'
    simpa only [Nat.add_assoc,Nat.add_comm 1 i] using
      forestRootAt_view (tau+1) (n+tsize t) (v+(valsOf t).length) ts i a hn' h

/-- Exact provider view, not just an equal extracted record. This theorem needs
neither wf nor capacity: both are separate accepted-domain facts. -/
theorem forest_located_seed {ts : List PTrie} {tau : Nat} {root a : OccurrenceAddress}
    (hr : forestRootAt 0 0 ts tau=some root) {steps : List OccurrenceStep}
    (ha : locateOccurrence root steps=some a) (hn : isNode a.tree=true) :
    (forestStoreViews ts).nodes[a.nid]?=
      some (seedNodeView tau a.depth a.nid a.vid a.tree) := by
  have hs := forestRootAt_view (ns:=forestNodes 0 0 0 ts) 0 0 0 ts tau root (by simp) hr
  have hl := locateOccurrence_view steps root a hs ha
  simpa only [Nat.zero_add,forestStoreViews] using hl.get hn

end ZkFormal.NearV3.Assembly
