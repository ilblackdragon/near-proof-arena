import ZkFormal.NearV3.Candidates.PairedForestMetadata

namespace ZkFormal.NearV3.Candidates.PairedForestWf
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
open PairedForestRelation PairedForestMetadata

/-- Paired records carry actual post payloads while inheriting the complete
native prestate allocation and initialized metadata validity. -/
theorem complete (pairs : List (PTrie×PTrie))
    (hp : ∀p∈pairs,WriteTreePair p.1 p.2)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true)
    (hb : Assembly.preBytes (pairs.map Prod.fst)≤2000000)
    (hd : ∀t∈pairs.map Prod.fst,∀k,fdepth t k≤NearSpecV3.trieFuel)
    (ht : pairs.length≤P) : NodeWf3 (initializeList 0 (pairedForest 0 0 0 pairs)) := by
  have hold := native_forest_wf (pairs.map Prod.fst) hw hb hd (by simpa using ht)
  have hal := forest 0 0 0 pairs hp
  have hlen := aligned_length hal
  have hbytes := congrArg (fun xs : List (List Nat)=>(xs.map List.length).sum)
    (pairedForest_pre 0 0 0 pairs hp)
  simp only [List.map_map,Function.comp_def] at hbytes
  apply initializeList_wf
  · exact forest_view_wf pairs hp hw hb
  · exact forest_depth pairs hp hd
  · exact forest_res pairs hp
  · intro t hmem
    obtain ⟨s,hs,hr⟩:=member hal t hmem
    obtain ⟨i,hib,hi⟩:=List.getElem_of_mem hs
    have hinit : initializeMetadata i s∈initializeList 0 (Assembly.forestNodes 0 0 0 (pairs.map Prod.fst)) := by
      apply List.mem_of_getElem? (i:=i)
      rw [initializeList_get]
      simp [List.getElem?_eq_getElem hib,hi]
    have hh:=hold.small _ hinit
    have hf:=record_fields hr
    exact ⟨hf.1 ▸ hh.1,hf.2.2.1 ▸ hh.2.2.1,hf.2.2.2.1 ▸ hh.2.2.2.1,
      hf.2.2.2.2 ▸ hh.2.2.2.2.1⟩
  · exact PairedForestRelation.forest_canonical pairs hp hw hb
  · simpa only [initializeList_length,hlen] using hold.count
  · rw [hbytes]
    simpa only [initializeList_bytes] using hold.rows

end ZkFormal.NearV3.Candidates.PairedForestWf
