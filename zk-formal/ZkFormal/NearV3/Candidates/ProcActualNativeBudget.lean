import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualSpendBudget
import ZkFormal.NearV3.Candidates.ProcActualNativeComplete
namespace ZkFormal.NearV3.Candidates.ProcActualNativeBudget
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

theorem round_rows_le (rs : List Gen.RoundD)
    (h : ∀rd∈rs,0<rd.entries.length) :
    (rs.map (fun rd=>1+rd.entries.length)).sum≤2*(rs.map (fun rd=>rd.entries.length)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := h r (by simp)
    have ht := ih (fun rd hd=>h rd (by simp [hd]))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem run_rows_le (I : Input) (tau : Nat) (R : Run)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (h : ActualRun.run I tau=.ok R) :
    (procVs R).length≤16+2*(R.conv.length+43*I.ids.length) := by
  have hb := ProcActualSpendBudget.run_steps_le I tau R hp h
  have hs := round_rows_le R.rounds (by
    intro rd hd
    have hh := ProcActualReplayShape.run_shapes I tau R h rd hd
    have he := hh.2.1
    have hz := hh.1
    simp only [List.size_toArray] at he
    omega)
  rw [procVs_length]
  omega

theorem rows_bound (rs : List Run) (B : Nat) (h : ∀R∈rs,(procVs R).length≤B) :
    (ProcConcatGeometry.rows rs).length≤B*rs.length := by
  induction rs with
  | nil => simp [ProcConcatGeometry.rows]
  | cons R rs ih =>
    have hh := h R (by simp)
    have ht := ih (fun S hs=>h S (by simp [hs]))
    simp only [ProcConcatGeometry.rows,List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one] at *
    omega

/-- The native replay budget implies a concrete common-height bound. The
request-count and instance-count inputs remain separate allocation obligations. -/
theorem native_capacity (rs : List Run) (hc : rs.length≤33)
    (hr : ∀R∈rs,∃I : Input,
      NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p ∧
      ActualRun.run I R.tau=.ok R ∧ I.ids.length≤64 ∧ R.conv.length≤4096) :
    (ProcConcatGeometry.rows rs).length+1≤2^22 := by
  have hb := rows_bound rs 13712 (by
    intro R hR
    rcases hr R hR with ⟨I,hp,h,hn,hC⟩
    have := run_rows_le I R.tau R hp h
    omega)
  omega

theorem native_local (rs : List Run) (hc : rs.length≤33)
    (hr : ∀R∈rs,∃I : Input,
      NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p ∧
      ActualRun.run I R.tau=.ok R ∧ I.ids.length≤64 ∧ R.conv.length≤4096)
    (hfirst : ∀R rest,rs=R::rest → R.tau=0)
    (ht : ∀pre R S post,rs=pre++R::S::post → S.tau=R.tau+1)
    (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (ProcConcatGeometry.trace rs) t pub := by
  apply ProcActualNativeComplete.list_local rs ?_ hfirst ht (native_capacity rs hc hr) t pub
  intro R hR
  rcases hr R hR with ⟨I,hp,h,_,_⟩
  exact ⟨I,hp,h⟩
end ZkFormal.NearV3.Candidates.ProcActualNativeBudget
