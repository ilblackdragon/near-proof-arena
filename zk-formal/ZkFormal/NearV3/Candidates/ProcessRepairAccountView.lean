import ZkFormal.NearV3.Candidates.ProcessRepairKeyView
import ZkFormal.NearV3.Rcpt.Candidates.AccountEmptyTraffic
import ZkFormal.NearV3.Rcpt.Extract.AkeyProof
namespace ZkFormal.NearV3.Candidates.ProcessRepairAccountView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem accounts {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) :
    ∃as:List AcctV,(as=[] ∨ AcctV3Wf as) ∧ TableTraffic AcctV3.interactions tr 6 pub (acctV3Traffic as) := by
  have h:=view.rest 6 (by rw [view.length];decide +kernel) (by decide)
  have hl:TableLocal Rcpt.Candidates.AccountEmpty.table tr 6 pub:=
    (InteractionTriples.local_iff _ _ _ _).mp h
  rcases Rcpt.Candidates.AccountEmpty.sound_cases hl with ho|hz
  · obtain ⟨as,hw,ht⟩:=acctV3_view tr pub 6 ho
    exact ⟨as,Or.inr hw,ht⟩
  · refine ⟨[],Or.inl rfl,?_⟩
    intro b msg
    have he (dir:Bool):tableBusCount AcctV3.interactions tr 6 pub b dir msg=0:=by
      rw [tableBusCount_eq]
      have hn:(List.range (tr.height 6)).flatMap (fun r=>rowTraffic AcctV3.interactions tr 6 r pub b dir)=[]:=by
        apply List.flatMap_eq_nil_iff.mpr
        intro r hr
        exact hz r (List.mem_range.mp hr) b dir
      rw [hn,List.count_nil]
    rw [he true,he false]
    simp [acctV3Traffic,acctV3Sends,acctRecvs,acctSends]

end ZkFormal.NearV3.Candidates.ProcessRepairAccountView
