import ZkFormal.NearV3.Candidates.OriginalSourceReserve
import ZkFormal.NearV3.Rcpt.Candidates.DedupTableFacts
namespace ZkFormal.NearV3.Candidates.OriginalSourceNativeBudget
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates
theorem dictionary (sources : List SrcList) (entries : List ProofEntry)
    (hl : ∀j,j<sources.length→∃e,lookupLast (sources.getD j ⟨[],0,[]⟩).key entries=some e)
    (hk : ∀e∈entries,e.key.length=32)
    (hp : ∀e∈entries,∀s∈e.proof.path,s.1.length=32)
    (hN : sources.length≤entries.length)
    (hskip : ∀B∈DedupCompile.blocks sources entries,B.dup=true→B.L=12) :
    DedupRender.size (DedupCompile.blocks sources entries)+44*sources.length+4≤
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
  have hcomp := SourceDictionaryBudget.computed_encoding computed
    (fun e he=>hk e (lookupLast_mem (hlookup e he)))
    (fun e he=>hp e (lookupLast_mem (hlookup e he)))
  have hc:=UniqueSourceNativeBudget.compiled_charges sources entries
  have hnlen:=congrArg List.length hc
  simp only [List.length_map] at hnlen
  have hsumenc := (hperm.map (fun e=>(ZkFormal.V3.encodeEntry e).length)).sum_nat
  have hcharge : UniqueSourceCharge.size (DedupCompile.blocks sources entries)=
      ((selectedSources (computed.map ProofEntry.key) entries).map fun e=>(ZkFormal.V3.encodeEntry e).length).sum := by
    rw [UniqueSourceCharge.computed_sum,hc,hnlen]
    change (computed.map entrySizeCharge).sum+44*computed.length=_
    rw [←hcomp,hsumenc]
  simpa only [DedupCompile.blocks_length] using OriginalSourceReserve.dictionary_bound
    (DedupCompile.blocks sources entries) _ entries hs (by simpa [DedupCompile.blocks_length] using hN)
    hk hcharge (by rw [←hlen];exact hnlen.symm) hskip

/-- Native cardinality reserves unused entries to pay the original duplicate
charge. No distinct-source restriction or replacement dictionary is assumed. -/
theorem accepted_dictionary {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep} {k : WalkD0}
    (h : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (hwalk : walkD0 cb=.ok k) :
    DedupRender.size (DedupCompile.blocks p.lists w.entries)+44*p.lists.length+4≤
      (encList ZkFormal.V3.encodeEntry w.entries).length := by
  obtain ⟨hb,_,hl⟩:=DedupCompile.relD0a_inputs h hp hf hw
  have hc : checkD0 cb wb=.ok () := by
    have hh:=h.1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  have hd : decodeW wb=.ok w := by
    unfold decodeW
    rw [hf]
    change decodeStateWitness raw=.ok w
    exact hw
  have hb' : raw.length≤8388608 := by simpa only [ReexecV3D0.lenT_eq,witnessBytes] using hb
  have hs:=decodeStateWitness_shape hw hb'
  have he : w.entries.all ZkFormal.V3.entryWf=true := by
    simp only [ZkFormal.V3.D0Shape,ZkFormal.V3.D0Shape.wf,Bool.and_eq_true] at hs
    exact hs.1.1.1.1.1.1.2
  apply dictionary p.lists w.entries hl
  · intro e hem
    have hh:=List.all_eq_true.mp he e hem
    simp only [ZkFormal.V3.entryWf,Bool.and_eq_true] at hh
    exact ZkFormal.V3.h32_len hh.1.1.1.1.1.1
  · intro e hem s hsm
    exact (decodeStateWitness_path_shape hw e hem s hsm).1
  · exact prepD0_sources_le_entries hwalk hd hc hp
  · intro B hB hdup
    obtain ⟨i,hi,heq⟩:=List.getElem_of_mem hB
    have hg : (DedupCompile.blocks p.lists w.entries).getD i default=B := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,heq]
    have ht:=DedupCompile.relD0a_table_facts h hp hf hw
    have hr:=ht.dup_rep i hi (by rw [hg];exact hdup)
    simpa only [hg] using ht.rep_length i hi hr

end ZkFormal.NearV3.Candidates.OriginalSourceNativeBudget
