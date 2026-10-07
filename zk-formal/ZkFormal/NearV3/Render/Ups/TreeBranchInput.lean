import ZkFormal.NearV3.Render.Ups.TreeEdge

/-! Byte completeness for actual branch-child recursion. The runtime trace proves
which slot changes, whether it was absent, and the output child hash width. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near ZkFormal.Near.Render

def treeRdb_byteInput (I : UpsInst) (base : UpsPartI) (value : Option Slot) (cs : Kids)
    (mem : Nat) (key : List Nat) (v : Bytes) (run : KidsRun) (Q : UpsPartI)
    (hr : traceKids (.branch value cs mem) (edgeSlot base.sd::key) cs (edgeSlot base.sd) key v=some run)
    (hi : run.inserted=false)
    (he : encodeTreePart base ⟨.RDB,.branch value cs mem,
      .branch value run.output (mem+run.newMem-run.oldMem),edgeSlot base.sd⟩=some Q)
    (hs : (PTrie.branch value cs mem).wf=true)
    (sd : base.sd=0 ∨ base.sd=1) (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  have hcs : Kids.wf cs 16=true := by
    simp only [PTrie.wf,Bool.and_eq_true] at hs
    exact hs.1.2
  have hf := traceKids_effect _ _ _ _ _ _ _ hr
  have hd := traceKids_output_wf hr hcs
  have hec := edge_decompose base.sd (treeKids cs) hsrc.1
  have heo : treeKids run.output=edgeKids base.sd (treeKid run.inner.output) (edgeRest base.sd (treeKids cs)) :=
    hf.2.1.trans (edge_set base.sd (treeKids cs) hsrc.1 _)
  have ho : (treeKids cs).getD (edgeSlot base.sd) .none ≠ .none := by
    intro h
    have := hf.2.2.1.mpr h
    simp [hi] at this
  have how : ((treeKids cs).getD (edgeSlot base.sd) .none).wf := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hf.1,Option.getD_some]
    exact hsrc.2.2.1 _ (List.getElem_mem hf.1)
  have hnw : (treeKid run.inner.output).wf := by
    simp [treeKid,NKid.wf,hashOf_eq_enc run.inner.output hf.2.2.2]
  have hs' : (NodeV3.branch (value.map treeSlot)
      (edgeKids base.sd ((treeKids cs).getD (edgeSlot base.sd) .none) (edgeRest base.sd (treeKids cs)))
      ((u64 mem).map UInt8.toNat)).wf := by rw [hec]; exact hsrc
  have hd' : (NodeV3.branch ((value.map treeSlot).map snapshotValue)
      (edgeKids base.sd (treeKid run.inner.output) ((edgeRest base.sd (treeKids cs)).map snapshotKid))
      ((u64 (mem+run.newMem-run.oldMem)).map UInt8.toNat)).wf := by
    rw [treeOption_snapshot,edgeRest_snapshot,←heo]
    exact ⟨hd.1,hsrc.2.1,hd.2,by simp⟩
  have hb : ∀b∈(NodeV3.branch (value.map treeSlot)
      (edgeKids base.sd ((treeKids cs).getD (edgeSlot base.sd) .none) (edgeRest base.sd (treeKids cs)))
      ((u64 mem).map UInt8.toNat)).ser true,b<256 := by
    rw [hec]
    exact treeNode_byte_bound hs trivial rfl true
  simpa only [treeOption_snapshot,edgeRest_snapshot,hec,←heo,UKind.ix] using
    rdb_byteInput I {base with kind:=0} rfl sd (value.map treeSlot) (edgeRest base.sd (treeKids cs))
      ((treeKids cs).getD (edgeSlot base.sd) .none) (treeKid run.inner.output) _ _
      ho (by simp [treeKid]) how hnw hs' hd' hb hts hx

def treeRbi_byteInput (I : UpsInst) (base : UpsPartI) (value : Option Slot) (cs : Kids)
    (mem : Nat) (key : List Nat) (v : Bytes) (run : KidsRun) (Q : UpsPartI)
    (hr : traceKids (.branch value cs mem) (edgeSlot (insertSide I)::key) cs (edgeSlot (insertSide I)) key v=some run)
    (hi : run.inserted=true)
    (he : encodeTreePart base ⟨.RBI,.branch value cs mem,
      .branch value run.output (mem+run.newMem-run.oldMem),edgeSlot (insertSide I)⟩=some Q)
    (hs : (PTrie.branch value cs mem).wf=true)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) : ByteInput I Q := by
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hs rfl
  have hcs : Kids.wf cs 16=true := by
    simp only [PTrie.wf,Bool.and_eq_true] at hs
    exact hs.1.2
  have hf := traceKids_effect _ _ _ _ _ _ _ hr
  have hd := traceKids_output_wf hr hcs
  have habs := hf.2.2.1.mp hi
  have hec : edgeKids (insertSide I) .none (edgeRest (insertSide I) (treeKids cs))=treeKids cs := by
    simpa only [habs] using edge_decompose (insertSide I) (treeKids cs) hsrc.1
  have heo : treeKids run.output=edgeKids (insertSide I) (treeKid run.inner.output) (edgeRest (insertSide I) (treeKids cs)) :=
    hf.2.1.trans (edge_set (insertSide I) (treeKids cs) hsrc.1 _)
  have hnw : (treeKid run.inner.output).wf := by
    simp [treeKid,NKid.wf,hashOf_eq_enc run.inner.output hf.2.2.2]
  have hs' : (NodeV3.branch (value.map treeSlot)
      (edgeKids (insertSide I) .none (edgeRest (insertSide I) (treeKids cs)))
      ((u64 mem).map UInt8.toNat)).wf := by rw [hec]; exact hsrc
  have hd' : (NodeV3.branch ((value.map treeSlot).map snapshotValue)
      (edgeKids (insertSide I) (treeKid run.inner.output) ((edgeRest (insertSide I) (treeKids cs)).map snapshotKid))
      ((u64 (mem+run.newMem-run.oldMem)).map UInt8.toNat)).wf := by
    rw [treeOption_snapshot,edgeRest_snapshot,←heo]
    exact ⟨hd.1,hsrc.2.1,hd.2,by simp⟩
  have hb : ∀b∈(NodeV3.branch (value.map treeSlot)
      (edgeKids (insertSide I) .none (edgeRest (insertSide I) (treeKids cs)))
      ((u64 mem).map UInt8.toNat)).ser true,b<256 := by
    rw [hec]
    exact treeNode_byte_bound hs trivial rfl true
  simpa only [treeOption_snapshot,edgeRest_snapshot,hec,←heo,UKind.ix] using
    rbi_byteInput I {base with kind:=5} rfl (value.map treeSlot) (edgeRest (insertSide I) (treeKids cs))
      (treeKid run.inner.output) _ _ (by simp [treeKid]) hnw hs' hd' hb hts hx

end ZkFormal.NearV3.Render.UpsGen
