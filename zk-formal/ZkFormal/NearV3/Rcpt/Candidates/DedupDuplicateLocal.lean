import ZkFormal.NearV3.Rcpt.Candidates.DedupTable
import ZkFormal.Near.Render.Proof.NodeEv

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

/-- One candidate row's natural cells, including terminal and repetition metadata. -/
def localCells (B : SrcpB) (before : Nat) (kind : Kind) (terminal repeated : Bool) : Nat → Nat :=
  fun x => if x = 56 then if kind = .root then repeated.toNat else 0
    else ({frame B before kind with gz := terminal}).cell x

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- Every candidate AIR constraint holds on a skipped duplicate header followed by
the next source header. No SHA or path premise is used for this row. -/
theorem duplicate_to_root (B C : SrcpB) (before : Nat) (repC : Bool)
    (hd : B.dup = true) (hL : B.L = 12) (hj : C.j = B.j + 1) (hq : C.ql = B.ql)
    (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before .root false true x : Int))
        (fun x => (localCells C (before + B.L) .root false repC x : Int))
        0 0 1 pub ex = 0 := by
  cases hc : C.dup <;> cases repC
  all_goals
    simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
      DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
      SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
      ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
      localCells, frame, rootFrame, Frame.cell, hd, hc, hL, hj, hq,
      SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
      SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
      SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
      SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
      Int.add_right_neg, Int.add_assoc]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- A duplicate header can be the physical last row; it emits terminal SIZE and
requires no cyclic successor values. -/
theorem duplicate_physical_last (B : SrcpB) (before : Nat)
    (hd : B.dup = true) (hL : B.L = 12) (next pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before .root true true x : Int)) next 0 1 0 pub ex = 0 := by
  simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, Frame.cell, hd, hL,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- A terminal duplicate header can be followed by padding that carries SIZE. -/
theorem duplicate_to_padding (B : SrcpB) (before : Nat)
    (hd : B.dup = true) (hL : B.L = 12) (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before .root true true x : Int))
        (fun x => if x = SrcpV3.sz then ((before + B.L : Nat) : Int) else 0) 0 0 1 pub ex = 0 := by
  simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, Frame.cell, hd, hL,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
