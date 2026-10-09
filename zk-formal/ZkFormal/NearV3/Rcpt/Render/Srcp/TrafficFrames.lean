import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficUtil

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near

/-- SIZE is the only interaction affected by the terminal gate. -/
theorem rowN_gz (C : Frame) (g : Bool) (bb : Nat) (sd : Bool) (hb : bb ≠ B_SIZE) :
    rowN ({ C with gz := g }).cell bb sd = rowN C.cell bb sd := by
  simp [rowN, hb, SrcpV3.rt, SrcpV3.sg, SrcpV3.gD, SrcpV3.q, SrcpV3.wn, SrcpV3.pw,
    SrcpV3.b, SrcpV3.cId, SrcpV3.cLen, SrcpV3.j, SrcpV3.L, SrcpV3.dup, Frame.cell, regN_gz]

theorem root_messages (B : SrcpB) (z bb : Nat) (sd : Bool) (hl : B.root.length = 32) :
    rowN (rootFrame B z).cell bb sd = srcpRootMsgs B bb sd := by
  have hreg : regN (rootFrame B z).cell = B.root := regN_full _ hl
  by_cases hd : bb = B_DIGEST <;> by_cases hr : bb = B_RCL <;> by_cases hs : bb = B_SRC
  all_goals cases sd
  all_goals simp_all [rowN, srcpRootMsgs, digMsg, rootFrame, Frame.cell,
    SrcpV3.rt, SrcpV3.sg, SrcpV3.gD, SrcpV3.gz, SrcpV3.q, SrcpV3.wn, SrcpV3.pw,
    SrcpV3.b, SrcpV3.cId, SrcpV3.cLen, SrcpV3.j, SrcpV3.L, SrcpV3.dup, hreg,
    B_DIGEST, B_RCL, B_SRC]
  all_goals cases B.dup <;> rfl

theorem leaf_row_messages (B : SrcpB) (z p bb : Nat) (sd : Bool) (hl : B.leaf.length = 32) :
    rowN (leafFrame B z p).cell bb sd =
      (if bb = B_BYTES ∧ sd = true then [[msgId K_SRC B.ql, p, B.leaf.getD p 0]] else []) ++
      (if bb = B_DIGEST ∧ sd = false ∧ p = 0 then [digMsg (msgId K_RC B.j) B.L B.leaf] else []) := by
  by_cases hp : p = 0
  · subst p
    have hreg : regN (leafFrame B z 0).cell = B.leaf := by
      have hh := regN_full (leafFrame B z 0) (by simpa [leafFrame] using hl)
      simpa [leafFrame] using hh
    simp only [rowN, hreg]
    simp [leafFrame, Frame.cell, SrcpV3.rt, SrcpV3.sg, SrcpV3.gD, SrcpV3.gz,
      SrcpV3.q, SrcpV3.wn, SrcpV3.pw, SrcpV3.b, SrcpV3.cId, SrcpV3.cLen, hreg, digMsg]
  · simp [rowN, leafFrame, Frame.cell, SrcpV3.rt, SrcpV3.sg, SrcpV3.gD, SrcpV3.gz,
      SrcpV3.q, SrcpV3.wn, SrcpV3.pw, SrcpV3.b, SrcpV3.cId, SrcpV3.cLen, hp]

end ZkFormal.NearV3.Render.SrcpGen
