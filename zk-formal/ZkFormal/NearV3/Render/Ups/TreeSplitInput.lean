import ZkFormal.NearV3.Render.Ups.TreeSplitKids
import ZkFormal.NearV3.Render.Ups.SpbFreshInput
import ZkFormal.NearV3.Render.Ups.SpbValueInput
import ZkFormal.NearV3.Render.Ups.SpbChildInput

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near ZkFormal.Near.Render

theorem treeKid_node_wf {t : PTrie} (h : isNode t=true) : (treeKid t).wf := by
  simp [treeKid,NKid.wf,hashOf_eq_enc t h]

def treeSpbFreshSome_input (I : UpsInst) (base : UpsPartI) (source child : PTrie)
    (v : Bytes) (mem : Nat) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.SPB,source,.branch (some (.val v)) (kids1 I.x child) mem,0⟩=some Q)
    (hi : I.ci=5 ∨ I.ci=7) (hs : source.wf=true)
    (hc : isNode child=true) (hv : I.v=v.map UInt8.toNat)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  cases hn : treeNode source with
  | none => simp [encodeTreePart,hn] at he
  | some src =>
    unfold encodeTreePart at he
    rw [hn] at he
    simp [treeNode] at he
    subst Q
    have hk : splitKids I (treeKid child) .none=treeKids (kids1 I.x child) := by
      rw [treeKids_one _ _ hx]
      rcases hi with h|h <;> simp [splitKids,splitHasNew,h]
    have hd : (NodeV3.branch (some (treeSlot (.val v))) (splitKids I (treeKid child) .none)
        ((u64 mem).map UInt8.toNat)).wf := by
      rw [hk,treeKids_one _ _ hx]
      exact ⟨oneKid_length _ _ hx,by intro s h; cases h; exact treeSlot_fresh_wf v,
        oneKid_wf _ _ (treeKid_node_wf hc),by simp⟩
    simpa only [hk,UKind.ix] using spb_fresh_some_input I {base with kind:=10} rfl hi
      src (treeSlot (.val v)) (treeKid child) _ hd (by simp [treeKid]) (treeSlot_fresh_length I v hv)
      (treeNode_byte_bound hs hn true) hts hx

def treeSpbFreshNone_input (I : UpsInst) (base : UpsPartI) (source old new : PTrie)
    (mem : Nat) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.SPB,source,.branch none (kids2 I.x old (splitNewSlot I) new) mem,0⟩=some Q)
    (hi : I.ci=6 ∨ I.ci=9) (hs : source.wf=true)
    (ho : isNode old=true) (hn : isNode new=true) (hxy : I.x≠splitNewSlot I)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  cases hsrc : treeNode source with
  | none => simp [encodeTreePart,hsrc] at he
  | some src =>
    unfold encodeTreePart at he
    rw [hsrc] at he
    simp [treeNode] at he
    subst Q
    have hk : splitKids I (treeKid old) (treeKid new)=treeKids (kids2 I.x old (splitNewSlot I) new) := by
      simp only [splitNewSlot]
      rw [treeKids_two I.ts I.x old new hx hxy]
      rcases hi with h|h <;> simp [splitKids,splitHasNew,h]
    have hd : (NodeV3.branch none (splitKids I (treeKid old) (treeKid new))
        ((u64 mem).map UInt8.toNat)).wf := by
      rw [hk]
      simp only [splitNewSlot]
      rw [treeKids_two I.ts I.x old new hx hxy]
      exact ⟨twoEdgeKids_length _ _ _ _ hx hxy,by simp,
        twoEdgeKids_wf _ _ _ _ (treeKid_node_wf ho) (treeKid_node_wf hn),by simp⟩
    simpa only [hk,UKind.ix] using spb_fresh_none_input I {base with kind:=10} rfl hi src
      (treeKid old) (treeKid new) _ hd (by simp [treeKid]) (by simp [treeKid]) hxy
      (treeNode_byte_bound hs hsrc true) hts hx

def treeSpbValue_input (I : UpsInst) (base : UpsPartI) (key : List Nat) (value : Slot)
    (oldMem : Nat) (child : PTrie) (mem : Nat) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.SPB,.leaf key value oldMem,
      .branch (some value) (kids1 (splitNewSlot I) child) mem,0⟩=some Q)
    (hi : I.ci=4) (hs : (PTrie.leaf key value oldMem).wf=true)
     (hc : isNode child=true)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  have hy : splitNewSlot I<16 := by unfold splitNewSlot; split <;> decide
  have hk : splitKids I .none (treeKid child)=treeKids (kids1 (splitNewSlot I) child) := by
    rw [treeKids_one _ _ hy]
    simp [splitKids,hi]
  have hd : (NodeV3.branch (some (snapshotValue (treeSlot value))) (splitKids I .none (treeKid child))
      ((u64 mem).map UInt8.toNat)).wf := by
    rw [treeSlot_snapshot,hk,treeKids_one _ _ hy]
    exact ⟨oneKid_length _ _ hy,by intro s h; cases h; exact hsrc.2.1,
      oneKid_wf _ _ (treeKid_node_wf hc),by simp⟩
  simpa only [treeSlot_snapshot,hk,UKind.ix] using spb_value_input I {base with kind:=10} rfl hi
    key (treeSlot value) (treeKid child) _ _ hsrc hd (by simp [treeKid])
    (treeNode_byte_bound hs rfl true) hts hx

def treeSpbChildValue_input (I : UpsInst) (base : UpsPartI) (key : List Nat) (child : PTrie)
    (oldMem : Nat) (v : Bytes) (mem : Nat) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.SPB,.ext key child oldMem,
      .branch (some (.val v)) (kids1 I.x child) mem,0⟩=some Q)
    (hi : I.ci=8) (hs : (PTrie.ext key child oldMem).wf=true)
     (hv : I.v=v.map UInt8.toNat)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  let dummy := treeKid (newLeaf [] v)
  have hk : splitKids I (snapshotKid (treeKid child)) dummy=treeKids (kids1 I.x child) := by
    rw [treeKid_snapshot,treeKids_one _ _ hx]
    simp [splitKids,splitHasNew,hi]
  have hd : (NodeV3.branch (some (treeSlot (.val v))) (splitKids I (snapshotKid (treeKid child)) dummy)
      ((u64 mem).map UInt8.toNat)).wf := by
    rw [hk,treeKids_one _ _ hx]
    exact ⟨oneKid_length _ _ hx,by intro s h; cases h; exact treeSlot_fresh_wf v,
      oneKid_wf _ _ hsrc.2.2.1,by simp⟩
  have hlen : ∀ s,some (treeSlot (.val v))=some s → s.lenB=(u32 (L I)).map UInt8.toNat := by
    intro s h; cases h; exact treeSlot_fresh_length I v hv
  simpa only [hk,UKind.ix] using spb_child_input I {base with kind:=10} rfl (Or.inl hi)
    key (treeKid child) dummy (some (treeSlot (.val v))) _ _
    (by simp [dummy,treeKid]) (treeKid_node_wf (t:=newLeaf [] v) rfl) hsrc hd hlen
    (by intro h; omega) (treeNode_byte_bound hs rfl true) hts hx

def treeSpbChildNone_input (I : UpsInst) (base : UpsPartI) (key : List Nat) (child new : PTrie)
    (oldMem mem : Nat) (Q : UpsPartI)
    (he : encodeTreePart base ⟨.SPB,.ext key child oldMem,
      .branch none (kids2 I.x child (splitNewSlot I) new) mem,0⟩=some Q)
    (hi : I.ci=10) (hs : (PTrie.ext key child oldMem).wf=true)
     (hn : isNode new=true)
    (hxy : I.x≠splitNewSlot I) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  have hk : splitKids I (snapshotKid (treeKid child)) (treeKid new)=
      treeKids (kids2 I.x child (splitNewSlot I) new) := by
    rw [treeKid_snapshot]
    simp only [splitNewSlot]
    rw [treeKids_two I.ts I.x child new hx hxy]
    simp [splitKids,splitHasNew,hi]
  have hd : (NodeV3.branch none (splitKids I (snapshotKid (treeKid child)) (treeKid new))
      ((u64 mem).map UInt8.toNat)).wf := by
    rw [hk]
    simp only [splitNewSlot]
    rw [treeKids_two I.ts I.x child new hx hxy]
    exact ⟨twoEdgeKids_length _ _ _ _ hx hxy,by simp,
      twoEdgeKids_wf _ _ _ _ hsrc.2.2.1 (treeKid_node_wf hn),by simp⟩
  simpa only [hk,UKind.ix] using spb_child_input I {base with kind:=10} rfl (Or.inr hi)
    key (treeKid child) (treeKid new) none _ _
    (by simp [treeKid]) (treeKid_node_wf hn) hsrc hd (by simp) (fun _ => hxy)
    (treeNode_byte_bound hs rfl true) hts hx

end ZkFormal.NearV3.Render.UpsGen
