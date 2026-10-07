import ZkFormal.NearV3.Rcpt.Candidates.DedupDuplicateLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- A final leaf window starts the next source header, including a skipped duplicate. -/
theorem leaf_to_root (B C : SrcpB) (before : Nat) (repC : Bool)
    (hqe : B.qe = B.ql) (hle : B.le = 32)
    (hq : C.ql = B.ql + 1) (hj : C.j = B.j + 1) (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before (.leaf 31) false false x : Int))
        (fun x => (localCells C (before + B.L) .root false repC x : Int))
        0 0 1 pub ex = 0 := by
  cases hc : C.dup
  all_goals simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, pathFrame, Frame.cell, hqe, hle, hc, hq, hj,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- A final path window starts the next source header, including a skipped duplicate. -/
theorem path_to_root (B C : SrcpB) (before i : Nat) (repC : Bool)
    (hqe : B.qe = (B.path.getD i default).q) (hle : B.le = 64)
    (hq : C.ql = (B.path.getD i default).q + 1) (hj : C.j = B.j + 1) (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before (.path i 63) false false x : Int))
        (fun x => (localCells C (before + B.L + 33 * (i + 1)) .root false repC x : Int))
        0 0 1 pub ex = 0 := by
  cases hc : C.dup
  all_goals cases hdir : (B.path.getD i default).dir
  all_goals simp only [List.getD_eq_getElem?_getD] at hdir hqe hq
  all_goals
    simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, pathFrame, Frame.cell, hdir, hqe, hle, hc, hq, hj,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
