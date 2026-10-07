import ZkFormal.NearV3.Rcpt.Candidates.DedupDuplicateLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- A final leaf window can occupy the physical endpoint. -/
theorem leaf_physical_last (B : SrcpB) (before : Nat)
    (hqe : B.qe = B.ql) (hle : B.le = 32) (next pub : Nat → Int) (hsg : next SrcpV3.sg = 0) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before (.leaf 31) true false x : Int))
        next 0 1 0 pub ex = 0 := by
  simp only [SrcpV3.sg] at hsg
  simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, pathFrame, Frame.cell, hqe, hle, hsg,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- A final path window can occupy the physical endpoint. -/
theorem path_physical_last (B : SrcpB) (before i : Nat)
    (hqe : B.qe = (B.path.getD i default).q) (hle : B.le = 64)
    (next pub : Nat → Int) (hsg : next SrcpV3.sg = 0) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before (.path i 63) true false x : Int))
        next 0 1 0 pub ex = 0 := by
  simp only [SrcpV3.sg] at hsg
  cases hdir : (B.path.getD i default).dir
  all_goals simp only [List.getD_eq_getElem?_getD] at hdir hqe
  all_goals
    simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, pathFrame, Frame.cell, hdir, hqe, hle, hsg,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
