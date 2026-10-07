import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficPathBytes

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near

/-- Exactly the accumulator window's first row looks up its predecessor digest. -/
theorem path_digest_flag (B : SrcpB) (z i o : Nat) (ho : o < 64) :
    (pathFrame B z i o).gD.toNat = 1 ↔
      o = SrcpProof.accStart (B.path.getD i default).dir := by
  cases hd : (B.path.getD i default).dir <;>
    by_cases hz : o % 32 = 0 <;> by_cases hw : 32 ≤ o
  all_goals
    simp only [List.getD_eq_getElem?_getD] at hd
    simp [pathFrame, SrcpProof.accStart, hd, hz, hw] <;> omega

/-- The predecessor digest is loaded unshifted at its single lookup row. -/
theorem path_lookup_registers (B : SrcpB) (z i o : Nat)
    (ho : o = SrcpProof.accStart (B.path.getD i default).dir)
    (hl : (B.path.getD i default).acc.length = 32) :
    regN (pathFrame B z i o).cell = (B.path.getD i default).acc := by
  have hm : o % 32 = 0 := by
    rw [ho]; cases (B.path.getD i default).dir <;> decide
  have hh := regN_full (pathFrame B z i o) (by simpa [pathFrame, hm] using hl)
  simpa [pathFrame, hm] using hh

end ZkFormal.NearV3.Render.SrcpGen
