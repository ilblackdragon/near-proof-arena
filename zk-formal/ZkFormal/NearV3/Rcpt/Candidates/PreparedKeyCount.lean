import ZkFormal.NearV3.Rcpt.Candidates.PreparedCoverage
import ZkFormal.NearV3.Assembly.Good

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

private theorem slotDescriptors_keys (B : Blk) (slots : List (ChunkSlot × ChunkInner)) :
    (slotDescriptors B slots).map SrcList.key=
      slots.filterMap (fun (s,ci) => if s.heightIncluded == B.hdr.height then
        some (chunkHash s.inner ci.encodedMerkleRoot) else none) := by
  induction slots with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨s,ci⟩
    simp only [slotDescriptors,List.flatMap_cons,List.filterMap_cons]
    split <;> simp_all [slotDescriptors]

theorem prepD0_source_keys_perm {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k) :
    (Assembly.sourceKeysV3 k).Perm (p.lists.map SrcList.key) := by
  have hh := (preparedSourceLists_perm (Assembly.prepD0_source_lists hp hw)).map SrcList.key
  have he : (k.sourceBlks.flatMap (fun B => slotDescriptors B B.slots)).map SrcList.key=
      Assembly.sourceKeysV3 k := by
    rw [List.map_flatMap]
    unfold Assembly.sourceKeysV3
    induction k.sourceBlks with
    | nil => rfl
    | cons B rest ih => simp only [List.flatMap_cons,slotDescriptors_keys,ih]
  rw [he] at hh
  exact hh

theorem prepD0_source_keys_count {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k) :
    p.lists.length=(Assembly.sourceKeysV3 k).length := by
  have hh := (prepD0_source_keys_perm hp hw).length_eq
  simpa only [List.length_map] using hh.symm

end ZkFormal.NearV3.Rcpt.Candidates
