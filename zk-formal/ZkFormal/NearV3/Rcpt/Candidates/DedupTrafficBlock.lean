import ZkFormal.NearV3.Rcpt.Candidates.DedupTraffic
import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficBlock

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near Render.SrcpGen

/-- Non-root rows retain the original bus records exactly. -/
theorem nonroot_messages (B : SrcpB) (before : Nat) (kind : Kind) (hk : kind ≠ .root)
    (terminal repeated : Bool) (bb : Nat) (sd : Bool) :
    rowN (localCells B before kind terminal repeated) bb sd =
      Render.SrcpGen.rowN ({frame B before kind with gz := terminal}).cell bb sd := by
  have hreg := regN_local B before kind terminal repeated
  simp only [rowN, Render.SrcpGen.rowN, hreg, regN_gz]
  cases kind with
  | root => exact False.elim (hk rfl)
  | leaf p =>
    simp [localCells, frame, leafFrame, Frame.cell, SrcpV3.rt, SrcpV3.sg,
      SrcpV3.gD, SrcpV3.gz, SrcpV3.q, SrcpV3.wn, SrcpV3.pw, SrcpV3.b,
      SrcpV3.cId, SrcpV3.cLen, SrcpV3.sz]
  | path i o =>
    simp [localCells, frame, pathFrame, Frame.cell, SrcpV3.rt, SrcpV3.sg,
      SrcpV3.gD, SrcpV3.gz, SrcpV3.q, SrcpV3.wn, SrcpV3.pw, SrcpV3.b,
      SrcpV3.cId, SrcpV3.cLen, SrcpV3.sz]

def rootMsgs (B : SrcpB) (repeated : Bool) (bb : Nat) (sd : Bool) : List Msg :=
  (if bb = B_DIGEST ∧ sd = false ∧ B.dup = false then
    [digMsg (msgId K_SRC B.qe) B.le B.root] else []) ++
  (if bb = B_RCL ∧ sd = false then [[B.j, B.L]] else []) ++
  (if bb = B_SRC ∧ sd = false then [[B.j, B.dup.toNat, repeated.toNat] ++ B.root] else [])

def blockMsgs (B : SrcpB) (repeated : Bool) (bb : Nat) (sd : Bool) : List Msg :=
  rootMsgs B repeated bb sd ++ if B.dup then [] else
    srcpLeafMsgs B.j B.L B.ql B.leaf bb sd ++ B.path.flatMap (fun it => srcpItemMsgs it bb sd)

theorem root_messages_nonterminal (B : SrcpB) (before : Nat) (repeated : Bool)
    (hl : B.root.length = 32) (bb : Nat) (sd : Bool) :
    rowN (localCells B before .root false repeated) bb sd = rootMsgs B repeated bb sd := by
  simpa [rootMsgs] using root_messages B before false repeated hl bb sd

theorem leaf_messages (B : SrcpB) (before : Nat) (repeated : Bool) (bb : Nat) (sd : Bool)
    (hl : B.leaf.length = 32) :
    (List.range 32).flatMap (fun p => rowN (localCells B before (.leaf p) false repeated) bb sd) =
      srcpLeafMsgs B.j B.L B.ql B.leaf bb sd := by
  have he : ∀ p, rowN (localCells B before (.leaf p) false repeated) bb sd =
      Render.SrcpGen.rowN (leafFrame B before p).cell bb sd := by
    intro p
    rw [nonroot_messages B before (.leaf p) (by simp)]
    rfl
  simp only [he]
  exact Render.SrcpGen.leaf_messages B before bb sd hl

theorem path_messages (B : SrcpB) (before i : Nat) (repeated : Bool) (bb : Nat) (sd : Bool)
    (ha : (B.path.getD i default).acc.length = 32)
    (hs : (B.path.getD i default).sib.length = 32) :
    (List.range 64).flatMap (fun o => rowN (localCells B before (.path i o) false repeated) bb sd) =
      srcpItemMsgs (B.path.getD i default) bb sd := by
  have he : ∀ o, rowN (localCells B before (.path i o) false repeated) bb sd =
      Render.SrcpGen.rowN (pathFrame B before i o).cell bb sd := by
    intro o
    rw [nonroot_messages B before (.path i o) (by simp)]
    rfl
  simp only [he]
  exact Render.SrcpGen.path_messages B before i bb sd ha hs

/-- Exact candidate source messages, including complete omission of duplicate SHA work. -/
theorem block_messages (B : SrcpB) (before : Nat) (repeated : Bool) (bb : Nat) (sd : Bool)
    (hr : B.root.length = 32) (hl : B.leaf.length = 32)
    (hp : ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32) :
    (kinds B).flatMap (fun k => rowN (localCells B before k false repeated) bb sd) =
      blockMsgs B repeated bb sd := by
  cases hd : B.dup
  · simp only [kinds, hd, Bool.false_eq_true, ↓reduceIte, Render.SrcpGen.kinds,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.flatMap_map, Function.comp_def, root_messages_nonterminal B before repeated hr bb sd,
      leaf_messages B before repeated bb sd hl, blockMsgs, ← List.append_assoc]
    congr 1
    rw [List.flatMap_assoc]
    have hh : (List.range B.path.length).flatMap (fun i =>
        (List.range 64).flatMap (fun o => rowN (localCells B before (.path i o) false repeated) bb sd)) =
        (List.range B.path.length).flatMap (fun i => srcpItemMsgs (B.path.getD i default) bb sd) := by
      apply flatMap_congr'
      intro i hi
      have hii := List.mem_range.mp hi
      have hm : B.path.getD i default ∈ B.path := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hii]
        exact List.getElem_mem hii
      exact path_messages B before i repeated bb sd (hp _ hm).2 (hp _ hm).1
    simp only [List.flatMap_map, Function.comp_def]
    rw [hh]
    exact flatMap_getD_all default (fun it => srcpItemMsgs it bb sd) B.path
  · simp [kinds, hd, blockMsgs, root_messages_nonterminal B before repeated hr bb sd]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
