import ZkFormal.NearV3.Candidates.WindowKeyCanonical

namespace ZkFormal.NearV3.Candidates.WindowProviderMetadata
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates.NodePostUpdate

/-- Duplicate-chain metadata and use-counter assignment preserve every original
provider window key at its original global occurrence and byte position. -/
theorem member (cs : List StoreDuplicateChain.Entry) (q : UseRequests)
    (u : Inputs) (ss : List NodeS3) (key : Msg)
    (hk : key∈nodeWindowKeys (records u ss)) :
    key∈nodeWindowKeys (assignList q 0 (records u (ChainMetadata.assign cs 0 ss))) := by
  obtain ⟨⟨s,n⟩,hs,hk'⟩ := List.mem_flatMap.mp hk
  obtain ⟨p,hp,hkey⟩:=List.mem_map.mp hk'
  have hs' : (records u ss)[n]?=some s := by
    have hz : (s,n)∈(records u ss).zipIdx := by
      simpa only [List.zipIdx_eq_zip_range',←List.range_eq_range'] using hs
    exact List.mem_zipIdx_iff_getElem?.mp hz
  obtain ⟨o,ho,hso⟩ : ∃o,ss[n]?=some o ∧ record u o=s := by
    simpa only [records,List.getElem?_map,Option.map_eq_some_iff] using hs'
  have hf : (assignList q 0 (records u (ChainMetadata.assign cs 0 ss)))[n]?=
      some (assignUses q n (record u (ChainMetadata.patch cs n o))) := by
    rw [assignList_get]
    simp [records,List.getElem?_map,ChainMetadata.assign_get,ho]
  have he : windowKey n p (assignUses q n (record u (ChainMetadata.patch cs n o)))=windowKey n p s := by
    rw [←hso];rfl
  rw [←hkey,←he]
  apply nodeWindowKeys_mem hf
  simpa only [assignUses,record,ChainMetadata.patch,←hso] using List.mem_range.mp hp

theorem canonical {vs : List NodeS3} (hw : NodeWf3 vs)
    (hb : ∀s∈vs,∀x∈s.v.ser true,x<256) {key : Msg}
    (hk : key∈nodeWindowKeys vs) : ∀x∈key,x<P := by
  obtain ⟨⟨s,n⟩,hs,hk'⟩:=List.mem_flatMap.mp hk
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hk'
  have hz : (s,n)∈vs.zipIdx := by
    simpa only [List.zipIdx_eq_zip_range',←List.range_eq_range'] using hs
  have hn : vs[n]?=some s:=List.mem_zipIdx_iff_getElem?.mp hz
  exact WindowKeyCanonical.small hw hn (List.mem_range.mp hp) (hb s (List.mem_of_getElem? hn))

/-- Mapped native coverage transfers through actual duplicate metadata and use
assignment, then canonicality closes the exact natural ownership premise. Only
the final provider list needs well-formedness; no separate base-list witness. -/
theorem physical_member (cs : List StoreDuplicateChain.Entry) (q : UseRequests)
    (u : Inputs) (ss : List NodeS3)
    (hw : NodeWf3 (assignList q 0 (records u (ChainMetadata.assign cs 0 ss))))
    (hb : ∀s∈assignList q 0 (records u (ChainMetadata.assign cs 0 ss)),∀x∈s.v.ser true,x<256)
    (tr : Trace Fp) (t r : Nat)
    (hc : ∃key,key∈nodeWindowKeys (records u ss) ∧ windowFieldKey tr t r=key.map Fp.ofNat) :
    physicalWindowKey tr t r∈nodeWindowKeys (assignList q 0 (records u (ChainMetadata.assign cs 0 ss))) := by
  obtain ⟨key,hk,he⟩:=hc
  have hm:=member cs q u ss key hk
  have heq : physicalWindowKey tr t r=key := by
    rw [physicalWindowKey,he,List.map_map]
    conv => rhs;rw [←List.map_id key]
    apply List.map_congr_left
    intro x hx
    simpa only [Function.comp_def,id_eq,Fp.toNat_ofNat] using Nat.mod_eq_of_lt (canonical hw hb hm x hx)
  rw [heq]
  exact hm

end ZkFormal.NearV3.Candidates.WindowProviderMetadata
