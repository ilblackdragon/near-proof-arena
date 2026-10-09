import ZkFormal.NearV3.Rcpt.Candidates.NativeOldTreeReconstruct

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly

/-- Executable old-record reconstruction, preserving the order and multiplicity
of actual receipt writes. Unknown or absent write targets fail explicitly. -/
def replayOldWrites : PTrie→List (List Nat×Bytes)→Option PTrie
  | pre,[]=>some pre
  | pre,(key,value)::rest=>do
    let mid←pre.set key value
    replayOldWrites mid rest

theorem replayOldWrites_of_run {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes post) : replayOldWrites pre writes=some post := by
  induction h with
  | nil=>rfl
  | cons hs ht ih=>simp [replayOldWrites,hs,ih]

theorem replayOldWrites_to_run : ∀(pre : PTrie)(writes : List (List Nat×Bytes))(post : PTrie),
    replayOldWrites pre writes=some post→AccountWriteRun pre writes post
  | pre,[],post,h=>by cases h;exact .nil pre
  | pre,(key,value)::rest,post,h=>by
    simp only [replayOldWrites] at h
    cases hs:pre.set key value with
    | none=>simp [hs] at h
    | some mid=>
      simp only [hs] at h
      exact .cons hs (replayOldWrites_to_run mid rest post h)

/-- Actual accepted execution supplies a successful executable old-tree replay,
whose scheduler reassembly is precisely the native final trie. -/
theorem newchunk_executable_old_tree {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : TrieShape pre) (hwell : pre.wf=true)
    (h : applyNewChunk prims ctx pre rs=.ok out) :
    ∃writes,∃oldPost mid : PTrie,∃so : SchedOut,
      schedStep prims ctx pre=.ok (mid,so) ∧
      writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId) ∧
      replayOldWrites pre writes=some oldPost ∧ WriteTreePair pre oldPost ∧ oldPost.wf=true ∧
      (valsOf oldPost).map List.length=(valsOf pre).map List.length ∧
      oldPost.upsert keyBwState so.state=some out.trie := by
  obtain ⟨writes,oldPost,mid,so,hs,hkeys,hr,hp,hwf,hl,hfinal⟩:=newchunk_old_tree_reconstruct hw hwell h
  exact ⟨writes,oldPost,mid,so,hs,hkeys,replayOldWrites_of_run hr.forget,hp,hwf,hl,hfinal⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
