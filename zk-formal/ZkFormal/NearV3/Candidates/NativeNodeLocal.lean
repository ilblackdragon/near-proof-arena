import ZkFormal.NearV3.Candidates.NativeNodeChildIds
import ZkFormal.NearV3.Candidates.StoreClassPartition
namespace ZkFormal.NearV3.Candidates.NativeNodeLocal
open NearSpec ZkFormal.Near Render Render.UpsGen Rcpt.Candidates.NodePostUpdate

theorem slot_bytes (vid : Nat) (s : Slot) (len : List Nat) (i l : Nat)
    (pre post : List Nat) (w : Bool) (h : viewSlot vid s=.val len i l pre post w) :
    ∀x∈len,x<256 := by
  cases s with
  | ref n hash => cases h
  | val bytes =>
    cases h
    intro x hx
    exact u32Bytes_lt _ x hx

theorem view_bytes (n v : Nat) (t : PTrie) (len : List Nat) (i l : Nat)
    (pre post : List Nat) (w : Bool)
    (h : (∃k m,viewNode n v t=.leaf k (.val len i l pre post w) m) ∨
      (∃kids m,viewNode n v t=.branch (some (.val len i l pre post w)) kids m)) :
    ∀x∈len,x<256 := by
  cases t with
  | hash hash => rcases h with ⟨_,_,h⟩|⟨_,_,h⟩ <;> cases h
  | ext k c m => rcases h with ⟨_,_,h⟩|⟨_,_,h⟩ <;> cases h
  | leaf k s m =>
    rcases h with ⟨_,_,h⟩|⟨_,_,h⟩
    · exact slot_bytes v s len i l pre post w (NodeV3.leaf.inj h).2.1
    · cases h
  | branch s cs m =>
    rcases h with ⟨_,_,h⟩|⟨_,_,h⟩
    · cases h
    · cases hs : s with
      | none => simp [viewNode,hs] at h
      | some sl =>
        have hh : viewSlot v sl=.val len i l pre post w := by
          simpa only [viewNode,hs,Option.map_some,NodeV3.branch.injEq,Option.some.injEq] using (NodeV3.branch.inj h).1
        exact slot_bytes v sl len i l pre post w hh

/-- Full honest node-generator input from native forest metadata. Nonempty
revealed inventory is explicit; all metadata and byte-layout obligations are derived. -/
theorem native_ok (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (hb : Assembly.preBytes ts≤2000000)
    (hd : ∀t∈ts,∀k,fdepth t k≤NearSpecV3.trieFuel)
    (ht : ts.length≤ZkFormal.Algebra.P) (hp : 0<(ts.flatMap occs).length) :
    NodeOk (initializeList 0 (Assembly.forestNodes 0 0 0 ts)) := by
  let vs:=Assembly.forestNodes 0 0 0 ts
  have hn:=native_forest_wf ts hw hb hd ht
  refine ⟨hn,?_,?_,?_,hn.rows,?_⟩
  · simpa [initializeList_length,forest_length] using hp
  · intro s hs
    obtain ⟨i,_,o,ho,rfl⟩:=initializeList_member vs 0 s hs
    exact native_forest_depth ts 0 0 0 hd o (List.mem_of_getElem? ho)
  · intro s hs len i l pre post w hv
    obtain ⟨j,_,o,ho,rfl⟩:=initializeList_member vs 0 s hs
    obtain ⟨t,_,tau,d,n,v,he,_,_,_⟩:=forest_allocation ts 0 0 0 o (List.mem_of_getElem? ho)
    subst o
    exact view_bytes n v t len i l pre post w hv
  · intro n hni p _
    have hi : n<vs.length := by simpa [initializeList_length] using hni
    apply NativeNodeChildIds.initialized_cid vs _ n p hi
    intro s hs
    obtain ⟨t,ht',tau,d,n,v,rfl,_,_,_⟩:=forest_allocation ts 0 0 0 s hs
    exact native_forest_node_wf ts hw hb n v t ht'
/-- Actual count-extended node/value tables are locally valid after both native
metadata initialization and duplicate-chain assignment. -/
theorem complete (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (hb : Assembly.preBytes ts≤2000000)
    (hd : ∀t∈ts,∀k,fdepth t k≤NearSpecV3.trieFuel)
    (ht : ts.length≤ZkFormal.Algebra.P) (hp : 0<(ts.flatMap occs).length)
    (t : Nat) (pub : List ZkFormal.Algebra.Fp) :
    let vs:=initializeList 0 (Assembly.forestNodes 0 0 0 ts)
    let es:=UpsGen.seedValuesFrom 0 (Assembly.forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    TableLocal Rcpt.Candidates.SizeCount.nodeTable
      (TrieCountHeight.node (ChainMetadata.assign cs 0 vs) pub) t pub ∧
    TableLocal Rcpt.Candidates.SizeCount.valTable
      (TrieCountHeight.value (ChainMetadata.assignValues cs es) pub) t pub := by
  exact StoreClassPartition.combined_local _ _ _ (native_ok ts hw hb hd ht hp)
    (NativeValueWf.forest_wf ts hw hb) t pub

end ZkFormal.NearV3.Candidates.NativeNodeLocal
