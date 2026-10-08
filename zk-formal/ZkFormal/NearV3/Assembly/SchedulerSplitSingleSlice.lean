import ZkFormal.NearV3.Assembly.SchedulerSplitHashOrder
import ZkFormal.NearV3.Render.Ups.SplitKidCounts
import ZkFormal.NearV3.Render.Ups.EncodedKindTypes

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Near ZkFormal.Near.Render

/-- Honest field lengths and exact native bytes fix the singleton branch
header to39 bytes, including copied source values. No value-width premise. -/
theorem split_single_physical_slice {p : TreePart} {sv : Slot} {x : Nat} {child : PTrie} {mem : Nat}
    (ho : p.output=.branch (some sv) (kids1 x child) mem) {base Q : UpsPartI}
    (he : encodeTreePart base p=some Q) (hf : FieldsOk Q)
    (hq : Q.q=(nodeEnc p.output).map UInt8.toNat) (hx : x<16) (hh : child.hashOf.length=32) :
    ((nodeEnc p.output).drop 39).take 32=child.hashOf := by
  have ht:Q.ty=3:=by simpa [ho,nativeNodeType] using encodeTreePart_type he
  have hn:nWin Q.shape=1:=by
    unfold encodeTreePart at he
    rw [ho,treeNode] at he
    cases hs:treeNode p.source <;> simp [hs] at he
    subst Q
    rw [encodePart_windows]
    change (NodeGen3.branchWins (treeKids (kids1 x child))).length=1
    rw [treeKids_one x child hx,oneKid_windows x (treeKid child) (by simp [treeKid])]
  have hlen:Q.q.length=79:=by
    rw [hf.bytes,hf.shape,ht,hn]
    simp [nodeFields,fieldsLen]
  rw [hq,List.length_map,ho] at hlen
  have hv:sv.valueRef.length=36:=by
    simp only [nodeEnc,List.length_append,List.length_cons,List.length_nil,u16_len,u64_len,
      kids1_hashes x child hx,hh] at hlen
    omega
  have hpre:(branchHashPrefix (some sv) (kids1 x child)).length=39:=by
    simp [branchHashPrefix,hv]
  rw [ho,←hpre]
  exact split_single_child_slice _ x child mem hx hh

end ZkFormal.NearV3.Assembly
