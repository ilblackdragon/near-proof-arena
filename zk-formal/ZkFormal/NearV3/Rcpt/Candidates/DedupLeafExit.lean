import ZkFormal.NearV3.Rcpt.Candidates.DedupDuplicateLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- A leaf segment enters the first path segment with a fresh message and33-byte SIZE charge. -/
theorem leaf_to_path (B : SrcpB) (before : Nat)
    (hq : (B.path.getD 0 default).q = B.ql + 1)
    (hpl : (B.path.getD 0 default).pl = 32) (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before (.leaf 31) false false x : Int))
        (fun x => (localCells B before (.path 0 0) false false x : Int))
        0 0 1 pub ex = 0 := by
  cases hdir : (B.path.getD 0 default).dir
  all_goals simp only [List.getD_eq_getElem?_getD] at hdir hq hpl
  all_goals
    simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, pathFrame, Frame.cell, hdir, hq, hpl,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
