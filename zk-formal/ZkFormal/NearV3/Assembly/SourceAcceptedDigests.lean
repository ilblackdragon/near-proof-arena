import ZkFormal.NearV3.Assembly.SourceBlockDigests
import ZkFormal.NearV3.Rcpt.Candidates.DedupCompile
import ZkFormal.NearV3.Rcpt.Link.WitnessSources

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Near Render.SrcpGen Rcpt.Candidates

/-- Native acceptance selects exactly the proof compiled at each prepared index;
raw decoding supplies its sibling widths. -/
theorem accepted_source_block_digests {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (j : Nat) (hj : j<p.lists.length) (repeated : Bool) :
    let B:=DedupCompile.block p.lists w.entries j
    (if B.dup then [] else sourceBlockOutputs B++[digMsg (msgId K_RC B.j) B.L B.leaf]).Perm
      (DedupRender.blockMsgs B repeated B_DIGEST false) := by
  obtain ⟨k,w',hk,hd,hv,_⟩ := relD0a_sources_verified ha
  have hd' : decodeW wb=.ok w := by simp [decodeW,hf,hw,bind,Except.bind]
  have hew := Except.ok.inj (hd.symm.trans hd')
  subst w'
  have hm : p.lists.getD j ⟨[],0,[]⟩∈p.lists := by
    rw [←List.getElem_eq_getD (h:=hj) ⟨[],0,[]⟩]
    exact List.getElem_mem hj
  obtain ⟨e,he,_,_,hevalid⟩ := preparedSourceLists_authenticated w.entries k.H.shardId k.sourceBlks hv
    (prepD0_source_lists hp hk) _ hm
  have heq : DedupCompile.entryAt p.lists w.entries j=e := by
    unfold DedupCompile.entryAt
    rw [he]
    rfl
  have hpath := lookupLast_path_shape hw he
  dsimp only [DedupCompile.block]
  rw [heq]
  exact blockOfProof_digest_partition _ _ repeated _ _ e hevalid (fun s hs=>(hpath s hs).1)

end ZkFormal.NearV3.Assembly
