import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionaryVerified
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRouting
import ZkFormal.NearV3.Assembly.PreparedSources

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Air ZkFormal.Near NearSpec NearSpecV3

theorem prepD0_source_key_shape {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k) :
    ∀ s∈p.lists,s.key.length=32 := by
  apply preparedSourceLists_property (fun s => s.key.length=32) k.sourceBlks ?_ (Assembly.prepD0_source_lists hp hw)
  intro B hB s hs
  obtain ⟨x,hx,hs⟩ := List.mem_flatMap.mp hs
  split at hs
  · simp only [List.mem_singleton] at hs
    subst s
    exact ArenaCore.sha256_length _
  · simp at hs

namespace DedupProof
open ZkFormal.Algebra

theorem BlockChain.indexed_metadata {src : Trace Fp} {ts : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint=.ok p)
    (hpub : ∀ m,cnt (sourceMsgs src ts bs B_SRC false) m=cnt (SourcePublic.records p.lists) m) :
    bs.length=p.lists.length ∧ ∀ i (hi : i<bs.length),
      (bs.getD i default).j=i ∧ (bs.getD i default).dup=Public.sourceDup p.lists i := by
  have hb := hs.bind_prepared hsrc hp hpub
  refine ⟨hb.1,?_⟩
  intro i hi
  have hm : bs[i]∈bs := List.getElem_mem hi
  obtain ⟨rep,hrep⟩ := sourceViews_mem (tr := src) (tt := ts) (s := 0) hm
  have hf := hb.2 (bs[i],rep) hrep
  have hj : bs[i].j=i := by
    have hh := hs.j_indices hsrc i hi
    rw [(row0 hsrc).2.1] at hh
    simpa only [show Fp.toNat 0=0 from rfl,Nat.zero_add] using hh
  rw [getD_eq_getElem' bs default hi]
  exact ⟨hj,by simpa only [hj] using hf.2.1⟩

theorem BlockChain.first_entry_shape {src : Trace Fp} {ts : Nat} {pub : List Fp}
    (hsrc : TableLocal (DedupTable.table 24) src ts pub)
    {bs : List SrcpB} {se : Nat} (hs : BlockChain src ts 0 bs se)
    {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k)
    (hpub : ∀ m,cnt (sourceMsgs src ts bs B_SRC false) m=cnt (SourcePublic.records p.lists) m)
    (rs : RcptV3Vs) :
    ∀ e∈firstNativeEntries p.lists p.hdr.own rs bs,
      e.key.length=32 ∧ ∀ item∈e.proof.path,item.1.length=32 := by
  intro e he
  obtain ⟨entry,hentry,rfl⟩ := List.mem_map.mp he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hentry
  have hil := firstSourceIndices_lt p.lists hi
  have hmeta := hs.indexed_metadata hsrc hp hpub
  have hbi : i<bs.length := by omega
  have hdup : Public.sourceDup p.lists i=false := by
    have hh := (List.mem_filter.mp hi).2
    simpa using hh
  have hbdup : bs[i].dup=false := by
    have hh := (hmeta.2 i hbi).2
    rw [getD_eq_getElem' bs default hbi,hdup] at hh
    exact hh
  have hb := (hs.payload_wf hsrc).computed (List.getElem_mem hbi) hbdup
  constructor
  · exact prepD0_source_key_shape hp hw _ (by
      rw [getD_eq_getElem' p.lists ⟨[],0,[]⟩ hil]
      exact List.getElem_mem hil)
  · intro item hm
    change item∈((bs.getD i default).path.map (fun it => (Link3.toB it.sib,if it.dir then 1 else 0))) at hm
    rw [getD_eq_getElem' bs default hbi] at hm
    obtain ⟨it,hit,rfl⟩ := List.mem_map.mp hm
    simpa only [Link3.toB,List.length_map] using (hb.len.2.2 it hit).1

end DedupProof
end ZkFormal.NearV3.Rcpt.Candidates
