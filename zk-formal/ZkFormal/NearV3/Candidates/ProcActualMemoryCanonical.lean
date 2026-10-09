import ZkFormal.NearV3.Candidates.ProcActualMemoryChainBounds
import ZkFormal.NearV3.Candidates.ProcActualRunComparisonInventory
import ZkFormal.NearV3.Candidates.ProcActualComparisonValid
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryCanonical
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcActualMemoryComparisonInventory

theorem request_bounds (g : Gen.Seg) (v w tp : Nat) (os : List Gen.MOp)
    (h:OpsOk g v w os) (hc:∀q∈requests tp os,CmpOk q) :
    ∀o∈os,o.t<2^29 ∧ o.inc<2^29 := by
  induction os generalizing v w tp with
  | nil=>simp
  | cons o os ih=>
    have ht:CmpOk (o.t,tp+1,1):=hc _ (by simp [requests,opRequests])
    have hi:o.inc<2^29 := by
      rcases h.1.kind with hr|hg
      · rw [(h.1.rd hr).2.2.1];decide
      · exact (hc (o.vin,o.inc,b2n o.sf) (by simp [requests,opRequests,hg])).2.1
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact ⟨ht.1,hi⟩
    · exact ih _ _ _ h.2 (fun q hq=>hc q (List.mem_append_right _ hq)) q hq

theorem small (g : Gen.Seg) (h:ProcActualMemoryChainSegments.SegChain g)
    (hc:∀q∈requests 0 g.ops,CmpOk q)
    (ha:g.addr<P) (hi:g.vin0<P) (hv:g.v0<P) (hw:g.wfin<P) : SegSmall g := by
  have hh:=ProcActualMemoryChainBounds.segment_bounds g h
  refine ⟨ha,hi,hv,Nat.lt_of_le_of_lt hh.1 hw,?_⟩
  intro o ho
  have hb:=hh.2 o ho
  have hq:=request_bounds g g.v0 g.w0 0 g.ops h hc o ho
  have hP:2^29<P:=by decide
  exact ⟨Nat.lt_trans hq.1 hP,Nat.lt_of_le_of_lt hb.1 hv,Nat.lt_of_le_of_lt hb.2.1 hv,
    Nat.lt_of_le_of_lt hb.2.2.1 hw,Nat.lt_of_le_of_lt hb.2.2.2 hw,Nat.lt_trans hq.2 hP⟩

theorem run (I : Input) (tau : Nat) (R : Run) (hr:ActualRun.run I tau=.ok R)
    (g : Gen.Seg) (hg:g∈R.segs)
    (ha:g.addr<P) (hi:g.vin0<P) (hv:g.v0<P) (hw:g.wfin<P) : SegSmall g := by
  apply small g (ProcActualMemoryChainSegments.run I tau R hr g hg) ?_ ha hi hv hw
  intro q hq
  apply ProcActualComparisonValid.run I tau R hr q
  rw [ProcActualRunComparisonInventory.run I tau R hr]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g,hg,hq⟩)
end ZkFormal.NearV3.Candidates.ProcActualMemoryCanonical
