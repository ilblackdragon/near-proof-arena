import ZkFormal.NearV3.Assembly.ForestViews
import ZkFormal.NearV3.Assembly.NativeUnfold
import ZkFormal.NearV3.Assembly.QueueSeed
import ZkFormal.NearV3.Assembly.NativeTrace
import ZkFormal.NearV3.Render.Ups.TreeViewBytes

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

mutual
theorem seedNodesT_bytes (tau : Nat) (post : Bool) : ∀ d n v t, t.wf=true →
    (seedNodesT tau d n v t).map (fun s => s.v.ser post)=
      (occs t).map (fun o => (nodeEnc o).map UInt8.toNat)
  | _,_,_,.hash _,_ => rfl
  | d,n,v,.leaf k s m,hw => by
    simp [seedNodesT,occs,seedNodeView,viewNode_ser n v _ hw (by rfl) post]
  | d,n,v,.ext k c m,hw => by
    have hc : c.wf=true := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw
      exact hw.1.1.2
    simp only [seedNodesT,occs,List.map_cons,seedNodeView]
    rw [viewNode_ser n v _ hw (by rfl) post,seedNodesT_bytes tau post _ _ _ c hc]
  | d,n,v,.branch sv cs m,hw => by
    have hc : Kids.wf cs 16=true := by
      simp only [PTrie.wf,Bool.and_eq_true] at hw
      exact hw.1.2
    simp only [seedNodesT,occs,List.map_cons,seedNodeView]
    rw [viewNode_ser n v _ hw (by rfl) post,seedKidsT_bytes tau post _ _ _ cs 16 hc]
theorem seedKidsT_bytes (tau : Nat) (post : Bool) : ∀ d n v cs width, Kids.wf cs width=true →
    (seedKidsT tau d n v cs).map (fun s => s.v.ser post)=
      (kOccs cs).map (fun o => (nodeEnc o).map UInt8.toNat)
  | _,_,_,.nil,_,_ => rfl
  | d,n,v,.none rest,width,hw => by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    exact seedKidsT_bytes tau post d n v rest (width-1) hw.2
  | d,n,v,.some c rest,width,hw => by
    simp only [Kids.wf,Bool.and_eq_true] at hw
    simp only [seedKidsT,kOccs,List.map_append]
    rw [seedNodesT_bytes tau post d n v c hw.1.2,
      seedKidsT_bytes tau post d (n+tsize c) (v+(valsOf c).length) rest (width-1) hw.2]
end

theorem forestNodes_bytes (post : Bool) : ∀ tau nid vid ts,
    (∀ t ∈ ts, t.wf=true) →
    (forestNodes tau nid vid ts).map (fun s => s.v.ser post)=
      (ts.flatMap occs).map (fun o => (nodeEnc o).map UInt8.toNat)
  | _,_,_,[],_ => rfl
  | tau,nid,vid,t::ts,hw => by
    simp only [forestNodes,List.map_append,List.flatMap_cons]
    rw [seedNodesT_bytes tau post _ _ _ t (hw t (by simp)),
      forestNodes_bytes post _ _ _ ts (fun t ht => hw t (by simp [ht]))]

/-- Exact seeded node-byte charge, including every repeated occurrence. -/
theorem forestNodes_byte_charge (ts : List PTrie) (hw : ∀ t ∈ ts, t.wf=true) :
    ((forestNodes 0 0 0 ts).map (fun s => (s.v.ser false).length)).sum ≤ preBytes ts := by
  have he := congrArg (fun xs : List (List Nat) => (xs.map List.length).sum)
    (forestNodes_bytes false 0 0 0 ts hw)
  simp only [List.map_map,List.length_map,Function.comp_def] at he
  rw [he]
  have hsum : ∀ trees : List PTrie,
      ((trees.flatMap occs).map (fun o => (nodeEnc o).length)).sum ≤ preBytes trees := by
    intro trees
    induction trees with
    | nil => simp [preBytes]
    | cons t ts ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,preBytes,List.map_cons,List.sum_cons]
      have ht : ((occs t).map (fun o => (nodeEnc o).length)).sum ≤ NearSpecV3.unfoldedBytesT t := by
        simp only [NearSpecV3.unfoldedBytesT,native_occs_eq]
        exact Nat.le_add_right _ _
      simp only [preBytes] at ih
      omega
  exact hsum ts

/-- The unchanged accepted-domain bound pays for all pre-node occurrence rows,
including shared-subtree copies; no deduplicated-node assumption is needed. -/
theorem checkD0a_forest_node_rows {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w)
    (h : checkD0a B0 cb wb = .ok ()) (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    (((forestStoreViews (m.pre :: steps.map ImplicitStepV3.pre)).nodes).map
      (fun s => (s.v.ser false).length)).sum + 1 ≤ 2^22 := by
  have hwf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf=true := by
    intro t ht
    simp only [List.mem_cons,List.mem_map] at ht
    rcases ht with rfl | ⟨e,he,rfl⟩
    · rw [hm.pre]
      exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
    · exact (hv.input_facts e he).2.2
  have hc := forestNodes_byte_charge _ hwf
  have hb := checkD0a_preBytes hk hw h hm hv
  change ((forestNodes 0 0 0 (m.pre :: steps.map ImplicitStepV3.pre)).map
    (fun s => (s.v.ser false).length)).sum + 1 ≤ 2^22
  unfold B0 at hb
  omega

end ZkFormal.NearV3.Assembly
