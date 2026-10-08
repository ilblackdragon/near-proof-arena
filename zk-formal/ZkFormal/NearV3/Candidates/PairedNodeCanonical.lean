import ZkFormal.NearV3.Candidates.PairedNodeWindows
import ZkFormal.NearV3.Rcpt.Candidates.NativeNodeCanonical

namespace ZkFormal.NearV3.Candidates.PairedNodeCanonical
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem slot (v : Nat) {a b : Slot} (h : WriteSlotPair a b)
    (hw : ∀x∈(viewSlot v a).raw,x<P) : ∀x∈(pairedSlot v a b).raw,x<P := by
  cases h with
  | ref n hh => exact hw
  | val a b =>
    intro x hx
    simp only [pairedSlot,NSlot3.raw,List.mem_append] at hx
    rcases hx with hx|hx
    · exact hw x (by simp only [viewSlot,NSlot3.raw,List.mem_append]; exact Or.inl hx)
    · exact native_bytes_small (ArenaCore.sha256 b) x hx

theorem kid (n : Nat) (a b : PTrie)
    (hw : ∀x∈(viewKid n a).raw,x<P) : ∀x∈(pairedKid n a b).raw,x<P := by
  by_cases hn : isNode a=true
  · simp only [pairedKid,viewKid,hn,ite_true] at *
    intro x hx
    simp only [NKid.raw,List.mem_append] at hx
    rcases hx with hx|hx
    · exact hw x (by simp only [NKid.raw,List.mem_append]; exact Or.inl hx)
    · exact native_bytes_small b.hashOf x hx
  · simpa [pairedKid,viewKid,hn] using hw

theorem kids : ∀(n : Nat){a b : Kids},WriteKidsPair a b →
    (∀c∈viewKids n a,∀x∈c.raw,x<P) → ∀c∈pairedKids n a b,∀x∈c.raw,x<P
  | _,_,_,.nil,_,_,hc => by simp [pairedKids] at hc
  | n,_,_,.none h,hw,c,hc => by
    simp only [pairedKids,List.mem_cons] at hc
    rcases hc with rfl|hc
    · simp [NKid.raw]
    · exact kids n h (fun c hc=>hw c (by simp [viewKids,hc])) c hc
  | n,_,_,.some h hs,hw,c,hc => by
    simp only [pairedKids,List.mem_cons] at hc
    rcases hc with rfl|hc
    · exact kid n _ _ (hw _ (by simp [viewKids]))
    · exact kids _ hs (fun c hc=>hw c (by simp [viewKids,hc])) c hc

theorem node (n v : Nat) {a b : PTrie} (h : WriteTreePair a b)
    (hw : ∀x∈(viewNode n v a).raw,x<P) : ∀x∈(pairedNode n v a b).raw,x<P := by
  cases h with
  | hash hh => exact hw
  | leaf k m hs =>
    intro x hx
    simp only [pairedNode,NodeV3.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · exact hw x (by simp [viewNode,NodeV3.raw,hx])
    · exact slot v hs (fun x hx=>hw x (by simp [viewNode,NodeV3.raw,hx])) x hx
    · exact hw x (by simp [viewNode,NodeV3.raw,hx])
  | ext k m hc =>
    intro x hx
    simp only [pairedNode,NodeV3.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · exact hw x (by simp [viewNode,NodeV3.raw,hx])
    · exact kid (n+1) _ _ (fun x hx=>hw x (by simp [viewNode,NodeV3.raw,hx])) x hx
    · exact hw x (by simp [viewNode,NodeV3.raw,hx])
  | branch m hv hcs =>
    have hk := kids (n+1) hcs (fun c hc x hx=>hw x (by
      simp only [viewNode,NodeV3.raw,List.mem_append,List.mem_flatMap]
      exact Or.inl (Or.inr ⟨c,hc,hx⟩)))
    intro x hx
    simp only [pairedNode,NodeV3.raw,List.mem_append] at hx
    rcases hx with (hx|hx)|hx
    · cases hv with
      | none => simp at hx
      | some hs => exact slot v hs (fun x hx=>hw x (by simp [viewNode,NodeV3.raw,hx])) x hx
    · obtain ⟨c,hc,hx⟩:=List.mem_flatMap.mp hx
      exact hk c hc x hx
    · exact hw x (by simp [viewNode,NodeV3.raw,hx])

end ZkFormal.NearV3.Candidates.PairedNodeCanonical
