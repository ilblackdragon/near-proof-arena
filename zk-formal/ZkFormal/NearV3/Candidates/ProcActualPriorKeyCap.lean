import ZkFormal.NearV3.Candidates.ProcActualModelKeyCap

namespace ZkFormal.NearV3.Candidates.ProcActualPriorKeyCap
open Sched Sched.Gen ProcActualReplayChain

/-- Stamping copies only the initial sentinel or an earlier emitted key.
The conclusion includes the final cursor, including the empty replay. -/
theorem stamped_cap {T kp Kq zq : Nat} {rs : List Gen.RoundD}
    (hs : Stamped T kp Kq zq rs)
    (hb : ∀ rd ∈ rs, rd.K < Proc.KSENT) :
    Kq ≤ Proc.KSENT ∧ ∀ rd ∈ rs, rd.Kq ≤ Proc.KSENT := by
  induction hs with
  | nil => exact ⟨Nat.le_refl _, by simp⟩
  | @snoc T kp Kq zq rs hs K z L kend es ih =>
    have hi := ih (fun rd hr => hb rd (List.mem_append_left _ hr))
    have hk := hb ⟨K,z,T,L,kp,kend,Kq,zq,es⟩ (by simp)
    refine ⟨Nat.le_of_lt hk, ?_⟩
    intro rd hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hi.2 rd hr
    · have he := List.mem_singleton.mp hr
      subst rd
      exact hi.1

theorem stamped_operand {T kp Kq zq : Nat} {rs : List Gen.RoundD}
    (hs : Stamped T kp Kq zq rs)
    (hb : ∀ rd ∈ rs, rd.K < Proc.KSENT) :
    Kq < 2^29 ∧ ∀ rd ∈ rs, rd.Kq < 2^29 := by
  have h := stamped_cap hs hb
  have hc : Proc.KSENT < 2^29 := by decide
  exact ⟨Nat.lt_of_le_of_lt h.1 hc, fun rd hr => Nat.lt_of_le_of_lt (h.2 rd hr) hc⟩

/-- Actual PV86 process and replay derive the bound; no complete run success
or separate emitted-key range premise is required. -/
theorem replay_prior_cap (I : Input) (cv : Array CReq) (st : PState) (rs : List Round)
    (out : ProcActualReplayRound.Acc)
    (hpp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length = some I.p)
    (hp : ProcActualInput.process I = .ok (st, rs))
    (hr : ProcActualReplayFactor.replay I cv rs = .ok out) :
    ∀ rd ∈ (ProcActualReplayKeyTrace.rounds out).toList, rd.Kq ≤ Proc.KSENT := by
  exact (stamped_cap (ProcActualReplayKeyTrace.replay_metadata I cv rs out hr).1
    (ProcActualModelKeyCap.replay_sentinel I cv st rs out hpp hp hr)).2

theorem replay_prior_operand (I : Input) (cv : Array CReq) (st : PState) (rs : List Round)
    (out : ProcActualReplayRound.Acc)
    (hpp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length = some I.p)
    (hp : ProcActualInput.process I = .ok (st, rs))
    (hr : ProcActualReplayFactor.replay I cv rs = .ok out) :
    ∀ rd ∈ (ProcActualReplayKeyTrace.rounds out).toList, rd.Kq < 2^29 := by
  intro rd hd
  exact Nat.lt_of_le_of_lt (replay_prior_cap I cv st rs out hpp hp hr rd hd) (by decide)

end ZkFormal.NearV3.Candidates.ProcActualPriorKeyCap
