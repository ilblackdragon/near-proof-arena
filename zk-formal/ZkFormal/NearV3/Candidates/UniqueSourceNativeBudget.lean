import ZkFormal.NearV3.Candidates.UniqueSourceBudget
import ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
import ZkFormal.NearV3.Assembly.DecodedWitnessShape
namespace ZkFormal.NearV3.Candidates.UniqueSourceNativeBudget
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Render.SrcpGen

theorem compiled_charges (sources : List SrcList) (entries : List ProofEntry) :
    (((DedupCompile.blocks sources entries).filter fun B=>!B.dup).map
      fun B=>B.L+33*B.path.length)=
      (firstSourceEntries sources (DedupCompile.entryAt sources entries)).map entrySizeCharge := by
  simp only [DedupCompile.blocks,List.filter_map,List.map_map,Function.comp_def,
    DedupCompile.block,blockOfProof,proofItems_length,firstSourceEntries,firstSourceIndices,
    entrySizeCharge,encodeReceipts,encList]

/-- First-occurrence order may differ from dictionary order; exact permutation
preserves multiplicity before the selected dictionary sublist bound is used. -/
theorem dictionary (sources : List SrcList) (entries : List ProofEntry)
    (hl : ∀j,j<sources.length→∃e,lookupLast (sources.getD j ⟨[],0,[]⟩).key entries=some e)
    (hk : ∀e∈entries,e.key.length=32)
    (hp : ∀e∈entries,∀s∈e.proof.path,s.1.length=32) :
    UniqueSourceCharge.size (DedupCompile.blocks sources entries)+4≤
      (encList ZkFormal.V3.encodeEntry entries).length := by
  let computed:=firstSourceEntries sources (DedupCompile.entryAt sources entries)
  have hlookup : ∀e∈computed,lookupLast e.key entries=some e := by
    intro e he
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp he
    have hh:=DedupCompile.entryAt_lookup sources entries (hl j (firstSourceIndices_lt sources hj))
    rw [lookupLast_key hh]
    exact hh
  have hn:=firstSourceEntries_keys_nodup sources entries (DedupCompile.entryAt sources entries)
    (fun j hj=>DedupCompile.entryAt_lookup sources entries (hl j hj))
  have hperm:=computed_perm_selected computed entries hn hlookup
  have hsum:=(hperm.map entrySizeCharge).sum_nat
  have hlen:=hperm.length_eq
  have hs:=selectedSources_sublist (computed.map ProofEntry.key) entries
  have hb:=SourceDictionaryBudget.selected_dictionary_le _ entries hs
    (fun e he=>hk e (hs.subset he)) (fun e he=>hp e (hs.subset he))
  have hc:=compiled_charges sources entries
  have hnlen:=congrArg List.length hc
  simp only [List.length_map] at hnlen
  rw [UniqueSourceCharge.computed_sum,hc,hnlen]
  change (computed.map entrySizeCharge).sum+44*computed.length+4≤_
  rw [hsum,hlen]
  exact hb

/-- Actual successful decoding supplies dictionary key/path byte widths. -/
theorem decoded_dictionary {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw=.ok w) (hb : raw.length≤8388608)
    (sources : List SrcList)
    (hl : ∀j,j<sources.length→∃e,lookupLast (sources.getD j ⟨[],0,[]⟩).key w.entries=some e) :
    UniqueSourceCharge.size (DedupCompile.blocks sources w.entries)+4≤
      (encList ZkFormal.V3.encodeEntry w.entries).length := by
  have hs:=decodeStateWitness_shape hw hb
  have he : w.entries.all ZkFormal.V3.entryWf=true := by
    simp only [ZkFormal.V3.D0Shape,ZkFormal.V3.D0Shape.wf,Bool.and_eq_true] at hs
    exact hs.1.1.1.1.1.1.2
  apply dictionary sources w.entries hl
  · intro e hem
    have hh:=List.all_eq_true.mp he e hem
    simp only [ZkFormal.V3.entryWf,Bool.and_eq_true] at hh
    exact ZkFormal.V3.h32_len hh.1.1.1.1.1.1
  · intro e hem s hsm
    exact (decodeStateWitness_path_shape hw e hem s hsm).1
/-- The actual accepted D0a/preparation path pays the corrected source charge
without a supplied dictionary-selection or accounting hypothesis. -/
theorem accepted_dictionary {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w) :
    UniqueSourceCharge.size (DedupCompile.blocks p.lists w.entries)+4≤
      (encList ZkFormal.V3.encodeEntry w.entries).length := by
  obtain ⟨hb,_,hl⟩:=DedupCompile.relD0a_inputs h hp hf hw
  apply decoded_dictionary hw _ p.lists hl
  simpa only [ReexecV3D0.lenT_eq,witnessBytes] using hb

end ZkFormal.NearV3.Candidates.UniqueSourceNativeBudget
