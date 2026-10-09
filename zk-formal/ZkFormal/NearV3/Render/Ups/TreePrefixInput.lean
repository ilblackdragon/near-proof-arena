import ZkFormal.NearV3.Render.Ups.TreeValueInput
import ZkFormal.NearV3.Render.Ups.MvlInput
import ZkFormal.NearV3.Render.Ups.MveInput
import ZkFormal.NearV3.Render.Ups.FreshInput

/-! Runtime prefix-node constructors. The path allocator supplies ordinary suffix
indices; all serialization conditions follow from source well-formedness. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near ZkFormal.Near.Render

def treeNlf_byteInput (I : UpsInst) (base : UpsPartI) (source : PTrie) (v : Bytes) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.NLF,source,newLeaf ([0,15].drop I.ts) v,0⟩=some Q)
    (hs : source.wf=true)
    (hv : I.v=v.map UInt8.toNat) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  cases hn : treeNode source with
  | none => simp [encodeTreePart,hn] at he
  | some src =>
    unfold encodeTreePart at he
    rw [hn] at he
    simp [treeNode,newLeaf] at he
    subst Q
    have hd : (NodeV3.leaf ([0,15].drop I.ts) (treeSlot (.val v))
        ((u64 (leafMem ([0,15].drop I.ts) v.length)).map UInt8.toNat)).wf := by
      refine ⟨?_,treeSlot_fresh_wf v,by simp⟩
      intro n h
      have hm := List.mem_of_mem_drop h
      simp at hm
      rcases hm with rfl|rfl <;> decide
    exact nlf_byteInput I _ rfl src _ _ hd (treeSlot_fresh_length I v hv)
      (treeNode_byte_bound hs hn true) hts hx

def treeMvl_byteInput (I : UpsInst) (base : UpsPartI) (key : List Nat) (value : Slot)
    (mem : Nat) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.MVL,.leaf key value mem,
      .leaf (key.drop (I.ti+1)) value (leafMem (key.drop (I.ti+1)) value.len),0⟩=some Q)
    (hs : (PTrie.leaf key value mem).wf=true)
    (hcut : I.ti+1≤key.length) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  have hd : (NodeV3.leaf (key.drop (I.ti+1)) (snapshotValue (treeSlot value))
      ((u64 (leafMem (key.drop (I.ti+1)) value.len)).map UInt8.toNat)).wf := by
    rw [treeSlot_snapshot]
    exact ⟨fun n h => hsrc.1 n (List.mem_of_mem_drop h),hsrc.2.1,by simp⟩
  simpa only [treeSlot_snapshot,UKind.ix] using mvl_byteInput I {base with kind:=6} rfl
    key (treeSlot value) _ _ hsrc hd hcut (treeNode_byte_bound hs rfl true) hts hx

def treeMve_byteInput (I : UpsInst) (base : UpsPartI) (key : List Nat) (child : PTrie)
    (mem : Nat) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.MVE,.ext key child mem,
      .ext (key.drop (I.ti+1)) child (extOwnMem (key.drop (I.ti+1))+(mem-extOwnMem key)),0⟩=some Q)
    (hs : (PTrie.ext key child mem).wf=true)
    (hcut : I.ti+1≤key.length) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  have hd : (NodeV3.ext (key.drop (I.ti+1)) (snapshotKid (treeKid child))
      ((u64 (extOwnMem (key.drop (I.ti+1))+(mem-extOwnMem key))).map UInt8.toNat)).wf := by
    rw [treeKid_snapshot]
    exact ⟨fun n h => hsrc.1 n (List.mem_of_mem_drop h),hsrc.2.1,hsrc.2.2.1,by simp⟩
  simpa only [treeKid_snapshot,UKind.ix] using mve_byteInput I {base with kind:=7} rfl
    key (treeKid child) _ _ hsrc hd hcut (treeNode_byte_bound hs rfl true) hts hx

/-- The split branch is a concrete node, so its child hash has the required width
without any assumption about its runtime memory-usage bound. -/
def treeWex_byteInput (I : UpsInst) (base : UpsPartI) (source child : PTrie) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.WEX,source,
      .ext (([0,15].drop (I.ts-1-I.ti)).take I.ti) child
        (extOwnMem (([0,15].drop (I.ts-1-I.ti)).take I.ti)+child.memD),0⟩=some Q)
    (hs : source.wf=true)  (hc : isNode child=true)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16)
    (wrap : I.ts=2 ∧ I.ti=1 ∨ I.ts=3 ∧ I.ti=1 ∨ I.ts=3 ∧ I.ti=2) : ByteInput I Q := by
  cases hn : treeNode source with
  | none => simp [encodeTreePart,hn] at he
  | some src =>
    unfold encodeTreePart at he
    rw [hn] at he
    simp [treeNode] at he
    subst Q
    have hd : (NodeV3.ext (([0,15].drop (I.ts-1-I.ti)).take I.ti) (treeKid child)
        ((u64 (extOwnMem (([0,15].drop (I.ts-1-I.ti)).take I.ti)+child.memD)).map UInt8.toNat)).wf := by
      refine ⟨?_,by simp [treeKid],?_,by simp⟩
      · intro n h
        have hm := List.mem_of_mem_drop (List.mem_of_mem_take h)
        simp at hm
        rcases hm with rfl|rfl <;> decide
      · simp [treeKid,NKid.wf,hashOf_eq_enc child hc]
    exact wex_byteInput I _ rfl src _ _ hd (treeNode_byte_bound hs hn true) hts hx wrap

end ZkFormal.NearV3.Render.UpsGen
