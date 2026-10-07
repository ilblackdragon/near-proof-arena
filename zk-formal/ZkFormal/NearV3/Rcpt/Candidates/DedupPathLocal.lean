import ZkFormal.NearV3.Rcpt.Candidates.DedupLeafLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- Internal bytes of a path's first window preserve every candidate constraint. -/
theorem path_lower_step (B : SrcpB) (before i p : Nat) (hp : p < 31)
    (hq : (B.path.getD i default).q = (B.path.getD i default).pq + 1)
    (pub : Nat → Int) :
    ∀ ex ∈ DedupTable.constraints,
      ev (fun x => (localCells B before (.path i p) false false x : Int))
        (fun x => (localCells B before (.path i (p + 1)) false false x : Int))
        0 0 1 pub ex = 0 := by
  have h31 : p ≠ 31 := by omega
  have hnext0 : p + 1 ≠ 0 := by omega
  have hm : p % 32 = p := by omega
  have hmnext : (p + 1) % 32 = p + 1 := by omega
  have hw : ¬ 32 ≤ p := by omega
  have hwnext : ¬ 32 ≤ p + 1 := by omega
  have h63 : p ≠ 63 := by omega
  have hnext63 : p + 1 ≠ 63 := by omega
  by_cases h0 : p = 0
  all_goals cases hdir : (B.path.getD i default).dir
  all_goals simp only [List.getD_eq_getElem?_getD] at hdir hq
  all_goals
    simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append, DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow, DedupTable.repeated,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul, Dsl.sum, Dsl.mid,
    localCells, frame, rootFrame, leafFrame, pathFrame, Frame.cell, h0, h31, hnext0, hp, hm, hmnext, hw, hwnext, h63, hnext63, hdir, hq,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
    SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.q, SrcpV3.j, SrcpV3.L, SrcpV3.qe,
    SrcpV3.le, SrcpV3.dup, SrcpV3.dir, SrcpV3.aw, SrcpV3.pl, SrcpV3.b,
    SrcpV3.cId, SrcpV3.cLen, SrcpV3.gD, SrcpV3.reg, SrcpV3.sz, SrcpV3.gz,
    Int.add_right_neg, Int.add_assoc, msgId, K_SRC, K_RC]

  all_goals
    intro a ha
    have ha32 : a < 32 := by omega
    have hb32 : a + 1 < 32 := by omega
    have ha56 : 22 + a ≠ 56 := by omega
    have hb56 : 22 + (a + 1) ≠ 56 := by omega
    simp [ha56, hb56, Nat.add_comm 22, ha32, hb32, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm, show a ≠ 34 by omega, show a ≠ 33 by omega, Int.add_right_neg]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
