import ZkFormal.NearV3.Rcpt.Candidates.NodePairedViews

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem pairedSlot_wf (vid : Nat) {a b : Slot} (h : WriteSlotPair a b)
    (hw : (viewSlot vid a).wf) : (pairedSlot vid a b).wf := by
  cases h with
  | ref n hh => exact hw
  | val a b =>
    change ((u32 a.length).map UInt8.toNat).length=4 ∧ (digest a).length=32 ∧
      (digest b).length=32 ∧ ((decide (a≠b))=false → digest b=digest a) ∧ _
    refine ⟨hw.1,hw.2.1,digest_length b,?_,hw.2.2.2.2⟩
    intro he
    have hab : a=b := by simpa using he
    rw [hab]

theorem pairedKid_wf (n : Nat) {a b : PTrie} (h : WriteTreePair a b)
    (hw : (viewKid n a).wf) : (pairedKid n a b).wf := by
  have hpost : isNode b=true → b.hashOf.length=32 := by
    intro hb
    rw [hashOf_eq_enc b hb]
    exact ArenaCore.sha256_length _
  cases h <;> simp only [pairedKid,viewKid,isNode,ite_true,ite_false,NKid.wf,List.length_map] at hw ⊢
  · exact hw
  all_goals exact ⟨hw.1,hpost rfl⟩

theorem pairedKids_length : ∀(n : Nat){a b : Kids},WriteKidsPair a b →
    (pairedKids n a b).length=(viewKids n a).length
  | _,_,_,.nil => rfl
  | n,_,_,.none h => by simpa [pairedKids,viewKids] using congrArg Nat.succ (pairedKids_length n h)
  | n,_,_,.some _ hs => by simpa [pairedKids,viewKids] using congrArg Nat.succ (pairedKids_length _ hs)

theorem pairedKids_wf : ∀(n : Nat){a b : Kids},WriteKidsPair a b →
    (∀c∈viewKids n a,c.wf) → ∀c∈pairedKids n a b,c.wf
  | _,_,_,.nil,_ => by simp [pairedKids]
  | n,_,_,.none h,hw => by
    intro c hc
    simp only [pairedKids,List.mem_cons] at hc
    rcases hc with rfl|hc
    · trivial
    · exact pairedKids_wf n h (fun c hc => hw c (by simp [viewKids,hc])) c hc
  | n,_,_,.some h hs,hw => by
    intro c hc
    simp only [pairedKids,List.mem_cons] at hc
    rcases hc with rfl|hc
    · exact pairedKid_wf n h (hw _ (by simp [viewKids]))
    · exact pairedKids_wf _ hs (fun c hc => hw c (by simp [viewKids,hc])) c hc

theorem pairedNode_wf (nid vid : Nat) {a b : PTrie} (h : WriteTreePair a b)
    (hw : (viewNode nid vid a).wf) : (pairedNode nid vid a b).wf := by
  cases h with
  | hash hh => exact hw
  | leaf k m hs => exact ⟨hw.1,pairedSlot_wf vid hs hw.2.1,hw.2.2⟩
  | ext k m hc =>
    refine ⟨hw.1,?_,pairedKid_wf (nid+1) hc hw.2.2.1,hw.2.2.2⟩
    unfold pairedKid
    split <;> simp
  | branch m hv hcs =>
    cases hv with
    | none =>
      refine ⟨?_,?_,pairedKids_wf _ hcs hw.2.2.1,hw.2.2.2⟩
      · rw [pairedKids_length _ hcs];exact hw.1
      · intro s hs;cases hs
    | @some a b hs =>
      refine ⟨?_,?_,pairedKids_wf _ hcs hw.2.2.1,hw.2.2.2⟩
      · rw [pairedKids_length _ hcs];exact hw.1
      · intro s he
        have he' : pairedSlot vid a b=s := Option.some.inj he
        rw [←he']
        exact pairedSlot_wf vid hs (hw.2.1 _ rfl)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
