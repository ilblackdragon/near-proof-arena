import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficPathGate

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near

/-- One path row contributes its byte and, once per segment, its predecessor digest. -/
theorem path_row_messages (B : SrcpB) (z i o bb : Nat) (sd : Bool) (ho : o < 64)
    (ha : (B.path.getD i default).acc.length = 32)
    (hs : (B.path.getD i default).sib.length = 32) :
    let it := B.path.getD i default
    rowN (pathFrame B z i o).cell bb sd =
      (if bb = B_BYTES ∧ sd = true then [[msgId K_SRC it.q, o, it.bytes.getD o 0]] else []) ++
      (if bb = B_DIGEST ∧ sd = false ∧ o = SrcpProof.accStart it.dir
        then [digMsg (msgId K_SRC it.pq) it.pl it.acc] else []) := by
  dsimp only
  have hp := path_byte_position o ho
  have hv := path_byte_value (B.path.getD i default) o ho ha hs
  have hg := path_digest_flag B z i o ho
  by_cases hk : o = SrcpProof.accStart (B.path.getD i default).dir
  · have hr := path_lookup_registers B z i o hk ha
    have hgate := hg.mpr hk
    simp only [rowN, show (pathFrame B z i o).cell SrcpV3.gD = 1 from hgate, hr]
    simp only [pathFrame, Frame.cell, SrcpV3.rt, SrcpV3.sg, SrcpV3.gz, SrcpV3.q,
      SrcpV3.wn, SrcpV3.pw, SrcpV3.b, SrcpV3.cId, SrcpV3.cLen]
    rw [hp, hv]
    simp only [hk, and_true, ite_true, digMsg]
    simp
  · have hgate : (pathFrame B z i o).cell SrcpV3.gD ≠ 1 := fun h => hk (hg.mp h)
    simp only [rowN, hgate, and_false, ite_false, List.append_nil]
    simp only [pathFrame, Frame.cell, SrcpV3.rt, SrcpV3.sg, SrcpV3.gz, SrcpV3.q,
      SrcpV3.wn, SrcpV3.pw, SrcpV3.b, SrcpV3.cId, SrcpV3.cLen]
    rw [hp, hv]
    simp only [List.getD_eq_getElem?_getD] at hk
    simp [hk]

end ZkFormal.NearV3.Render.SrcpGen
