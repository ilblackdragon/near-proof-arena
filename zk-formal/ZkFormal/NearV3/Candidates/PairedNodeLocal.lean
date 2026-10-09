import ZkFormal.NearV3.Candidates.PairedForestWf
import ZkFormal.NearV3.Candidates.NativeNodeLocal

namespace ZkFormal.NearV3.Candidates.PairedNodeLocal
open NearSpec ZkFormal.Near Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem slot_bytes (v : Nat) {a b : Slot} (hp : WriteSlotPair a b)
    (len : List Nat) (i l : Nat) (pre post : List Nat) (w : Bool)
    (h : pairedSlot v a b=.val len i l pre post w) : ∀x∈len,x<256 := by
  cases hp with
  | ref n hh => cases h
  | val a b =>
    cases h
    exact fun x hx=>u32Bytes_lt _ x hx

theorem view_bytes (n v : Nat) {a b : PTrie} (hp : WriteTreePair a b)
    (len : List Nat) (i l : Nat) (pre post : List Nat) (w : Bool)
    (h : (∃k m,pairedNode n v a b=.leaf k (.val len i l pre post w) m) ∨
      (∃kids m,pairedNode n v a b=.branch (some (.val len i l pre post w)) kids m)) :
    ∀x∈len,x<256 := by
  cases hp with
  | hash hh => exact NativeNodeLocal.view_bytes n v (.hash hh) len i l pre post w h
  | ext k m hc => rcases h with ⟨_,_,h⟩|⟨_,_,h⟩ <;> cases h
  | leaf k m hs =>
    rcases h with ⟨_,_,h⟩|⟨_,_,h⟩
    · exact slot_bytes v hs len i l pre post w (NodeV3.leaf.inj h).2.1
    · cases h
  | branch m hv hcs =>
    rcases h with ⟨_,_,h⟩|⟨_,_,h⟩
    · cases h
    · cases hv with
      | none => cases h
      | some hs => exact slot_bytes v hs len i l pre post w (Option.some.inj (NodeV3.branch.inj h).1)

/-- Full node-renderer input with paired post payloads, under the explicit
native write relation. Actual transition-to-pair extraction remains separate. -/
theorem native_ok (pairs : List (PTrie×PTrie))
    (hp : ∀p∈pairs,WriteTreePair p.1 p.2)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true)
    (hb : Assembly.preBytes (pairs.map Prod.fst)≤2000000)
    (hd : ∀t∈pairs.map Prod.fst,∀k,fdepth t k≤NearSpecV3.trieFuel)
    (ht : pairs.length≤ZkFormal.Algebra.P)
    (hn : 0<((pairs.map Prod.fst).flatMap occs).length) :
    NodeOk (initializeList 0 (pairedForest 0 0 0 pairs)) := by
  have hwf:=PairedForestWf.complete pairs hp hw hb hd ht
  have hl:=PairedForestMetadata.aligned_length (PairedForestRelation.forest 0 0 0 pairs hp)
  refine ⟨hwf,?_,?_,?_,hwf.rows,?_⟩
  · rw [initializeList_length,←hl,forest_length];exact hn
  · intro s hs
    obtain ⟨i,_,o,ho,rfl⟩:=initializeList_member _ 0 s hs
    exact PairedForestMetadata.forest_depth pairs hp hd o (List.mem_of_getElem? ho)
  · intro s hs len i l pre post w hv
    obtain ⟨j,_,o,ho,rfl⟩:=initializeList_member _ 0 s hs
    obtain ⟨s,_,tau,d,n,v,a,b,hp,rfl,rfl⟩:=PairedForestRelation.member
      (PairedForestRelation.forest 0 0 0 pairs hp) o (List.mem_of_getElem? ho)
    exact view_bytes n v hp len i l pre post w hv
  · intro n hni p _
    apply NativeNodeChildIds.initialized_cid _ (PairedForestRelation.forest_view_wf pairs hp hw hb) n p
    simpa [initializeList_length] using hni

theorem complete (pairs : List (PTrie×PTrie))
    (hp : ∀p∈pairs,WriteTreePair p.1 p.2)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true)
    (hb : Assembly.preBytes (pairs.map Prod.fst)≤2000000)
    (hd : ∀t∈pairs.map Prod.fst,∀k,fdepth t k≤NearSpecV3.trieFuel)
    (ht : pairs.length≤ZkFormal.Algebra.P)
    (hn : 0<((pairs.map Prod.fst).flatMap occs).length)
    (t : Nat) (pub : List ZkFormal.Algebra.Fp) :
    let vs:=initializeList 0 (pairedForest 0 0 0 pairs)
    let es:=UpsGen.seedValuesFrom 0 (Assembly.forestBytes (pairs.map Prod.fst))
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs
      (NativeStoreProvenance.valueTau (pairs.map Prod.fst)) es)
    TableLocal SizeCount.nodeTable (TrieCountHeight.node (ChainMetadata.assign cs 0 vs) pub) t pub ∧
    TableLocal SizeCount.valTable (TrieCountHeight.value (ChainMetadata.assignValues cs es) pub) t pub := by
  exact StoreClassPartition.combined_local _ _ _ (native_ok pairs hp hw hb hd ht hn)
    (NativeValueWf.forest_wf _ hw hb) t pub

end ZkFormal.NearV3.Candidates.PairedNodeLocal
