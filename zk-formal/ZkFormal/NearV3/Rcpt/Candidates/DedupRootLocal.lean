import ZkFormal.NearV3.Rcpt.Candidates.DedupDuplicateLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- Every computed root enters its leaf segment, with public repetition metadata
checked independently of any path-depth or table-cap restriction. -/
theorem computed_root_to_leaf (B : SrcpB) (before : Nat) (rep : Bool)
    (hd : B.dup = false) (hq : 1 ≤ B.ql) (hL : rep = true → B.L = 12)
    (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before .root false rep x : Int))
        (fun x => (localCells B before (.leaf 0) false false x : Int))
        0 0 1 pub ex = 0 := by
  have hqi : ((B.ql - 1 : Nat) : Int) = (B.ql : Int) - 1 := by omega
  cases hrp : rep
  · simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, Frame.cell, hd, hL, hrp, hqi,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]
  · have hL := hL hrp
    simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, Frame.cell, hd, hL, hrp, hqi,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- The first computed root initializes source/message counters and SIZE. -/
theorem first_root_to_leaf (B : SrcpB) (rep : Bool)
    (hd : B.dup = false) (hq : B.ql = 1) (hj : B.j = 0) (hL : rep = true → B.L = 12)
    (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B 0 .root false rep x : Int))
        (fun x => (localCells B 0 (.leaf 0) false false x : Int))
        1 0 1 pub ex = 0 := by
  have hqi : ((B.ql - 1 : Nat) : Int) = (B.ql : Int) - 1 := by omega
  cases hrp : rep
  · simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, Frame.cell, hd, hL, hrp, hqi, hq, hj,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]
  · have hL := hL hrp
    simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, Frame.cell, hd, hL, hrp, hqi, hq, hj,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
