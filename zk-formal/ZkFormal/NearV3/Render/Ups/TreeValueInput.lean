import ZkFormal.NearV3.Render.Ups.TreePartEncoding
import ZkFormal.NearV3.Render.Ups.RlpInput
import ZkFormal.NearV3.Render.Ups.RbrInput
import ZkFormal.NearV3.Render.Ups.RbvInput

/-! Byte completeness inputs for the runtime's value-replacement terminal cases.
Raw-node well-formedness, source byte bounds and fresh value lengths are derived
from the actual source trie and value, rather than supplied independently. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near ZkFormal.Near.Render

@[simp] theorem treeSlot_snapshot (s : Slot) : snapshotValue (treeSlot s)=treeSlot s := by
  cases s <;> rfl
@[simp] theorem treeKid_snapshot (t : PTrie) : snapshotKid (treeKid t)=treeKid t := rfl
@[simp] theorem treeKids_snapshot : ∀ cs : Kids, (treeKids cs).map snapshotKid=treeKids cs
  | .nil => rfl
  | .none cs => by simp [treeKids,snapshotKid,treeKids_snapshot cs]
  | .some c cs => by simp [treeKids,treeKids_snapshot cs]

theorem treeSlot_fresh_wf (v : Bytes) : (treeSlot (.val v)).wf := by
  simp [treeSlot,NSlot3.wf]

theorem treeSlot_fresh_length (I : UpsInst) (v : Bytes) (hv : I.v=v.map UInt8.toNat) :
    (treeSlot (.val v)).lenB=(u32 (L I)).map UInt8.toNat := by
  simp [treeSlot,NSlot3.lenB,L,hv]

/-- Runtime leaf replacement, with all semantic byte conditions derived. -/
def treeRlp_byteInput (I : UpsInst) (base : UpsPartI) (key : List Nat) (old : Slot)
    (mem : Nat) (v : Bytes) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.RLP,.leaf key old mem,newLeaf key v,0⟩=some Q)
    (hs : (PTrie.leaf key old mem).wf=true)

    (hv : I.v=v.map UInt8.toNat) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode,newLeaf] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  have hdst : (NodeV3.leaf key (treeSlot (.val v)) ((u64 (leafMem key v.length)).map UInt8.toNat)).wf :=
    ⟨hsrc.1,treeSlot_fresh_wf v,by simp⟩
  exact rlp_byteInput I _ rfl key _ _ _ _ hsrc hdst (treeSlot_fresh_length I v hv)
    (treeNode_byte_bound hs rfl true) hts hx

/-- Runtime replacement of an existing branch value. -/
def treeRbr_byteInput (I : UpsInst) (base : UpsPartI) (old : Slot) (kids : Kids)
    (mem : Nat) (v : Bytes) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.RBR,.branch (some old) kids mem,
      .branch (some (.val v)) kids (mem+valueMem v.length-valueMem old.len),0⟩=some Q)
    (hs : (PTrie.branch (some old) kids mem).wf=true)
    (hv : I.v=v.map UInt8.toNat) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  have hdst : (NodeV3.branch (some (treeSlot (.val v))) ((treeKids kids).map snapshotKid)
      ((u64 (mem+valueMem v.length-valueMem old.len)).map UInt8.toNat)).wf := by
    rw [treeKids_snapshot]
    exact ⟨hsrc.1,by intro s h; cases h; exact treeSlot_fresh_wf v,hsrc.2.2.1,by simp⟩
  simpa only [treeKids_snapshot,UKind.ix] using rbr_byteInput I {base with kind:=3} rfl
    (treeSlot old) (treeSlot (.val v)) (treeKids kids) _ _ hsrc hdst (treeSlot_fresh_length I v hv)
    (treeNode_byte_bound hs rfl true) hts hx

/-- Runtime insertion of a value into an existing valueless branch. -/
def treeRbv_byteInput (I : UpsInst) (base : UpsPartI) (kids : Kids)
    (mem : Nat) (v : Bytes) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.RBV,.branch none kids mem,
      .branch (some (.val v)) kids (mem+valueMem v.length),0⟩=some Q)
    (hs : (PTrie.branch none kids mem).wf=true)
    (hv : I.v=v.map UInt8.toNat) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  have hdst : (NodeV3.branch (some (treeSlot (.val v))) ((treeKids kids).map snapshotKid)
      ((u64 (mem+valueMem v.length)).map UInt8.toNat)).wf := by
    rw [treeKids_snapshot]
    exact ⟨hsrc.1,by intro s h; cases h; exact treeSlot_fresh_wf v,hsrc.2.2.1,by simp⟩
  simpa only [treeKids_snapshot,UKind.ix] using rbv_byteInput I {base with kind:=4} rfl
    (treeSlot (.val v)) (treeKids kids) _ _ hsrc hdst (treeSlot_fresh_length I v hv)
    (treeNode_byte_bound hs rfl true) hts hx

end ZkFormal.NearV3.Render.UpsGen
