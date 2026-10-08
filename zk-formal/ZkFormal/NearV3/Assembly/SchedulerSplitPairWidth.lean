import ZkFormal.NearV3.Assembly.SchedulerSplitSingleSlice

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near ZkFormal.Near.Render

/-- Exact honest field lengths pay for both split child hashes, including a
copied child which deliberately has no new SHA request. -/
theorem split_pair_hash_lengths {p : TreePart} {ts x : Nat} {old new : PTrie} {mem : Nat}
    (ho : p.output=.branch none (kids2 x old (if ts=1 then 0 else 15) new) mem)
    {base Q : UpsPartI} (he : encodeTreePart base p=some Q) (hf : FieldsOk Q)
    (hq : Q.q=(nodeEnc p.output).map UInt8.toNat) (hx : x<16)
    (hd : x≠if ts=1 then 0 else 15) : old.hashOf.length+new.hashOf.length=64 := by
  have ht:Q.ty=2:=by simpa [ho,nativeNodeType] using encodeTreePart_type he
  have hn:nWin Q.shape=2:=by
    unfold encodeTreePart at he
    rw [ho,treeNode] at he
    cases hs:treeNode p.source <;> simp [hs] at he
    subst Q
    rw [encodePart_windows]
    change (NodeGen3.branchWins (treeKids (kids2 x old (if ts=1 then 0 else 15) new))).length=2
    rw [treeKids_two ts x old new hx hd,twoEdgeKids_windows ts x (treeKid old) (treeKid new) (by simp [treeKid]) (by simp [treeKid])]
  have hlen:Q.q.length=75:=by rw [hf.bytes,hf.shape,ht,hn];simp [nodeFields,fieldsLen]
  rw [hq,List.length_map,ho] at hlen
  simp only [nodeEnc,List.length_append,List.length_cons,List.length_nil,u16_len,u64_len,
    kids2_hashes ts x old new hx hd] at hlen
  by_cases ht:ts=1 <;> simp [ht] at hlen <;> omega

end ZkFormal.NearV3.Assembly
