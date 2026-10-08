import ZkFormal.NearV3.Assembly.SourceAcceptedDigests
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaTraffic

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Near Render.SrcpGen Rcpt.Candidates

private theorem flatMap_perm {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,(f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact (h x (by simp)).append (ih (fun y hy=>h y (by simp [hy])))

private theorem block_repeated (B : SrcpB) (repeated : Bool) :
    DedupRender.blockMsgs B repeated B_DIGEST false=DedupRender.blockMsgs B false B_DIGEST false := by
  simp [DedupRender.blockMsgs,DedupRender.rootMsgs,B_DIGEST,B_RCL,B_SRC]

private theorem batch_partition (bs : List SrcpB) (repeated : Nat→Bool)
    (h : ∀B∈bs,(if B.dup then [] else sourceBlockOutputs B++[digMsg (msgId K_RC B.j) B.L B.leaf]).Perm
      (DedupRender.blockMsgs B false B_DIGEST false)) :
    ((bs.filter (fun B=>!B.dup)).flatMap sourceBlockOutputs++
      (bs.filter (fun B=>!B.dup)).map (fun B=>digMsg (msgId K_RC B.j) B.L B.leaf)).Perm
      (DedupRender.sourceMsgs bs repeated B_DIGEST false) := by
  have he : DedupRender.sourceMsgs bs repeated B_DIGEST false=
      bs.flatMap (fun B=>DedupRender.blockMsgs B false B_DIGEST false) := by
    unfold DedupRender.sourceMsgs
    simp only [block_repeated]
    exact (flatMap_eq_range bs (fun B=>DedupRender.blockMsgs B false B_DIGEST false)).symm
  rw [he]
  have hp := flatMap_perm bs _ _ h
  have hf : bs.flatMap (fun B=>if B.dup then [] else sourceBlockOutputs B++[digMsg (msgId K_RC B.j) B.L B.leaf])=
      (bs.filter (fun B=>!B.dup)).flatMap (fun B=>sourceBlockOutputs B++[digMsg (msgId K_RC B.j) B.L B.leaf]) := by
    clear h he hp
    induction bs with
    | nil => rfl
    | cons B bs ih => cases hd : B.dup <;> simp [hd,ih]
  rw [hf] at hp
  exact ((by simpa only [←List.map_eq_flatMap] using
    (flatMap_split_perm (bs.filter (fun B=>!B.dup)) sourceBlockOutputs
      (fun B=>[digMsg (msgId K_RC B.j) B.L B.leaf])).symm) :
      ((bs.filter (fun B=>!B.dup)).flatMap sourceBlockOutputs++
        (bs.filter (fun B=>!B.dup)).map (fun B=>digMsg (msgId K_RC B.j) B.L B.leaf)).Perm _).trans hp

private theorem jobs_digests (jobs : List Render.Msg) :
    Sha.Gen.expectedDigests (jobsToSha jobs)=jobs.map Render.digestMsg := by
  induction jobs with
  | nil=>rfl
  | cons j js ih=>simpa [jobsToSha,Sha.Gen.expectedDigests,Render.digestMsg,Render.shaN,Render.ofNats,Render.toNats] using congrArg (List.cons (Render.digestMsg j)) ih

theorem source_sha_digest_outputs (sources : List SrcList) (entries : List ProofEntry) :
    Sha.Gen.expectedDigests (sourceShaMessages sources entries)=
      ((DedupCompile.blocks sources entries).filter (fun B=>!B.dup)).flatMap sourceBlockOutputs := by
  rw [←sourceViewJobs_compiled,jobs_digests]
  unfold sourceBlockOutputs
  simp only [sourceViewJobs,List.map_flatMap,List.map_map,Function.comp_def]


theorem accepted_source_digest_partition {budget : Nat} {cb wb raw : Bytes} {codes : List Bytes}
    {w : StateWitness} {hint : Hint} {p : Prep}
    (ha : RelD0a budget cb wb) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hw : decodeStateWitness raw=.ok w)
    (repeated : Nat→Bool) :
    (Sha.Gen.expectedDigests (sourceShaMessages p.lists w.entries)++
      ((DedupCompile.blocks p.lists w.entries).filter (fun B=>!B.dup)).map
        (fun B=>digMsg (msgId K_RC B.j) B.L B.leaf)).Perm
      (DedupRender.sourceMsgs (DedupCompile.blocks p.lists w.entries) repeated B_DIGEST false) := by
  rw [source_sha_digest_outputs]
  apply batch_partition
  intro B hB
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hB
  exact accepted_source_block_digests ha hp hf hw j (List.mem_range.mp hj) false

end ZkFormal.NearV3.Assembly
