import ZkFormal.NearV3.Rcpt.Candidates.ReplayHeadOk

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render

/-- Common log22 HEAD trace, with existing head cells and zero padding. -/
def replayHeadTrace (hs : List HeadE) : Trace Fp :=
  ⟨fun _=>22,fun _ r c=>Fp.ofNat (HeadGen.cell hs (2^22) r c)⟩

theorem replayHeadTrace_complete (hs : List HeadE) (hw : HeadOk hs)
    (t : Nat) (pub : List Fp) :
    TableLocal {HeadV3.table with maxLog:=22} (replayHeadTrace hs) t pub ∧
    TableTraffic HeadV3.interactions (replayHeadTrace hs) t pub (headTraffic hs) := by
  have hcap : 32*hs.length≤(replayHeadTrace hs).height t := by
    change 32*hs.length≤2^22
    have hh:=hw.cap
    omega
  exact ⟨head_render_local_at hs hw _ t pub 22 (by change 1≤22 ∧ 22≤22;decide) hcap (by intros;rfl),
    head_render_traffic_at hs hw _ t pub hcap (by intros;rfl)⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
