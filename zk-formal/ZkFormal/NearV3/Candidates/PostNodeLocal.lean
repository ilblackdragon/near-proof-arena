import ZkFormal.NearV3.Candidates.NativeNodeLocal
import ZkFormal.NearV3.Rcpt.Candidates.NodePostWf

namespace ZkFormal.NearV3.Candidates.PostNodeLocal
open ZkFormal.Near ZkFormal.Algebra Render Rcpt.Candidates.NodePostUpdate

theorem kid_ids (u : Inputs) (k : NKid) : kidIds (kid u k)=kidIds k := by
  cases k <;> rfl

theorem window_ids (u : Inputs) (v : NodeV3) : windowIds (node u v)=windowIds v := by
  cases v with
  | leaf k s m =>
    change List.replicate ((node u (.leaf k s m)).ser false).length 0=_
    rw [node_pre];rfl
  | ext k c m => simp only [node,windowIds,kid_ids]
  | branch v cs m => simp only [node,windowIds,Option.isSome_map,List.flatMap_map,kid_ids]

theorem getD (u : Inputs) (vs : List NodeS3) (i : Nat) (hi : i<vs.length) :
    (records u vs).getD i default=record u (vs.getD i default) := by
  simp [records,List.getD,List.getElem?_eq_getElem hi]

theorem cid (u : Inputs) (vs : List NodeS3) (hw : ∀s∈vs,s.v.wf)
    (i p : Nat) (hi : i<vs.length) : NodeGen3.cidAt (records u vs) i p=NodeGen3.cidAt vs i p := by
  have hv : (vs.getD i default).v.wf := by
    simpa [List.getD,List.getElem?_eq_getElem hi] using hw vs[i] (List.getElem_mem hi)
  simp only [NodeGen3.cidAt,NodeGen3.layN,NodeGen3.rec,getD u vs i hi,record]
  have hh:=congrArg (fun ids : List Nat=>ids.getD p 0) (window_ids u (vs.getD i default).v)
  rw [NativeNodeChildIds.window_at _ (node_wf u _ hv),NativeNodeChildIds.window_at _ hv] at hh
  exact hh

theorem slot_origin (u : Inputs) (s : NSlot3) (len : List Nat) (i l : Nat)
    (pre post : List Nat) (w : Bool) (h : slot u s=.val len i l pre post w) :
    ∃po wr,s=.val len i l pre po wr := by
  cases s with
  | ref lb hh => cases h
  | val lb vi vl vp vo vw =>
    cases hu : u.value vi <;> simp only [slot,hu] at h <;> cases h <;> exact ⟨_,_,rfl⟩

theorem len_bytes (u : Inputs) (v : NodeV3)
    (hv : ∀len i l pre post w,
      ((∃k m,v=.leaf k (.val len i l pre post w) m) ∨
       (∃cs m,v=.branch (some (.val len i l pre post w)) cs m)) → ∀x∈len,x<256)
    (len : List Nat) (i l : Nat) (pre post : List Nat) (w : Bool)
    (h : (∃k m,node u v=.leaf k (.val len i l pre post w) m) ∨
      (∃cs m,node u v=.branch (some (.val len i l pre post w)) cs m)) : ∀x∈len,x<256 := by
  cases v with
  | ext k c m => rcases h with ⟨_,_,h⟩|⟨_,_,h⟩ <;> cases h
  | leaf k s m =>
    rcases h with ⟨_,_,h⟩|⟨_,_,h⟩
    · obtain ⟨po,wr,he⟩:=slot_origin u s len i l pre post w (NodeV3.leaf.inj h).2.1
      exact hv len i l pre po wr (Or.inl ⟨k,m,by rw [he]⟩)
    · cases h
  | branch sv cs m =>
    rcases h with ⟨_,_,h⟩|⟨_,_,h⟩
    · cases h
    · cases sv with
      | none => cases h
      | some s =>
        obtain ⟨po,wr,he⟩:=slot_origin u s len i l pre post w (Option.some.inj (NodeV3.branch.inj h).1)
        exact hv len i l pre po wr (Or.inr ⟨cs,m,by rw [he]⟩)

/-- Arbitrary post digest updates preserve honest renderer inputs. Correctness
of the supplied final payloads is a separate native-execution obligation. -/
theorem node_ok (u : Inputs) (vs : List NodeS3) (h : NodeOk vs) : NodeOk (records u vs) := by
  refine ⟨records_wf u vs h.wf,?_,?_,?_,?_,?_⟩
  · simpa [records] using h.pos
  · intro s hs
    simp only [records,List.mem_map] at hs
    obtain ⟨s,hs,rfl⟩:=hs
    exact h.depth s hs
  · intro s hs
    simp only [records,List.mem_map] at hs
    obtain ⟨s,hs,rfl⟩:=hs
    exact len_bytes u s.v (h.lenB s hs)
  · simpa [records_pre_lengths] using h.rows
  · intro n hni p hp
    have hi : n<vs.length := by simpa [records] using hni
    rw [getD u vs n hi] at hp ⊢
    rw [cid u vs h.wf.wf n p hi]
    exact h.ucid n hi p (by simpa only [record,node_pre] using hp)

theorem complete (u : Inputs) (vs : List NodeS3) (h : NodeOk vs)
    (t : Nat) (pub : List Fp) :
    TableLocal Rcpt.Candidates.SizeCount.nodeTable (TrieCountHeight.node (records u vs) pub) t pub :=
  TrieCountHeight.node_local _ (node_ok u vs h) t pub

end ZkFormal.NearV3.Candidates.PostNodeLocal
