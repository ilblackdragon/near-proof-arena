import ZkFormal.NearV3.Candidates.ProcActualReplayKeyTrace

namespace ZkFormal.NearV3.Candidates.ProcActualModelKeyCap
open Sched Sched.Gen

def Pending (cap : Nat) (ps : List Push) : Prop := ∀ p ∈ ps, p.key < cap

theorem fold_cap (cap seed : Nat) (ps : List Push) (hz : seed < cap)
    (hp : Pending cap ps) : ps.foldl (fun m p => Nat.max m p.key) seed < cap := by
  induction ps generalizing seed with
  | nil => exact hz
  | cons p ps ih =>
    apply ih
    · exact Nat.max_lt.mpr ⟨hz, hp p (by simp)⟩
    · intro q hq; exact hp q (by simp [hq])

private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α) = .error e := rfl

set_option maxHeartbeats 800000 in
theorem entry_cap (cap n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (K z v : Nat) (hk : K < cap) (s : ProcActualModelStep.EntryAcc)
    (hs : Pending cap s.1) (out : ForInStep ProcActualModelStep.EntryAcc)
    (h : ProcActualModelStep.entryStep n allowed reqs K z v s = .ok out) :
    ExceptLoop.StepInv (fun s => Pending cap s.1) out := by
  unfold ProcActualModelStep.entryStep at h
  simp only [bind, Except.bind, pure, Except.pure, throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | simp only [ExceptLoop.StepInv, Pending, List.mem_append, List.mem_singleton]
      intro p hp
      rcases hp with hp | rfl
      · exact hs p hp
      · dsimp only
        simp_all only [Bool.not_eq_true, Bool.not_eq_false', Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        omega

theorem entries_cap (cap n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (K z : Nat) (hk : K < cap) (vs : List Nat) (s out : ProcActualModelStep.EntryAcc)
    (hs : Pending cap s.1)
    (h : forIn vs s (ProcActualModelStep.entryStep n allowed reqs K z) = .ok out) :
    Pending cap out.1 :=
  ExceptLoop.invariant vs (ProcActualModelStep.entryStep n allowed reqs K z)
    (fun s => Pending cap s.1)
    (fun v _ s hs out h => entry_cap cap n allowed reqs K z v hk s hs out h) s out hs h

def Inv (cap : Nat) (s : ProcActualModelStep.Acc) : Prop :=
  Pending cap s.1 ∧ ∀ rd ∈ s.2.2.2.1, rd.key < cap

set_option maxHeartbeats 1000000 in
theorem step_cap (cap n : Nat) (hc : 0 < cap) (allowed : Array Bool)
    (reqs : List NearSpecV3.Scheduler.Req) (i : Nat) (s : ProcActualModelStep.Acc)
    (hs : Inv cap s) (out : ForInStep ProcActualModelStep.Acc)
    (h : ProcActualModelStep.step n allowed reqs i s = .ok out) :
    ExceptLoop.StepInv (Inv cap) out := by
  let K := s.1.foldl (fun m p => Nat.max m p.key) 0
  let z := ((sortTs (s.1.filter (fun p => p.key == K))).headD default).z
  have hk : K < cap := fold_cap cap 0 s.1 hc hs.1
  have hf : Pending cap (s.1.filter (fun p => p.key != K)) := by
    intro p hp; exact hs.1 p (List.mem_filter.mp hp).1
  unfold ProcActualModelStep.step at h
  simp only [bind, Except.bind, pure, Except.pure, throw_eq] at h
  split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | refine ⟨?_, ?_⟩
      · exact entries_cap cap n allowed reqs K z hk _ _ _ hf (by assumption)
      · intro rd hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hs.2 rd hr
        · have he := List.mem_singleton.mp hr
          subst rd
          exact hk

theorem initial_cap (cap : Nat) (reqs : List NearSpecV3.Scheduler.Req) (st : PState)
    (ha : ∀ i : Nat, st.al[i]! < cap) : Inv cap (ProcActualModelStep.initial reqs st) := by
  constructor
  · intro p hp
    simp only [ProcActualModelStep.initial, List.mem_filterMap] at hp
    rcases hp with ⟨i, hi, he⟩
    split at he
    · cases he
    · have hh := Option.some.inj he
      subst p
      exact ha _
  · simp [ProcActualModelStep.initial]

set_option maxHeartbeats 400000 in
theorem process_cap (cap n : Nat) (hc : 0 < cap) (allowed : Array Bool)
    (reqs : List NearSpecV3.Scheduler.Req) (st0 st : PState) (fuel : Nat) (rs : List Round)
    (ha : ∀ i : Nat, st0.al[i]! < cap)
    (h : processEv n allowed reqs st0 fuel = .ok (st, rs)) : ∀ rd ∈ rs, rd.key < cap := by
  rw [ProcActualModelStep.process_eq] at h
  simp only [bind, Except.bind, pure, Except.pure, throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    have hh : Inv cap ?out := by
      refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f (Inv cap) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => exact initial_cap cap _ _ ha
      case step => exact fun i _ s hs out h => step_cap cap n hc allowed reqs i s hs out h
    exact hh.2

/-- Even out-of-range allowance reads return zero, so this bound needs no index premise. -/
theorem initial_allowance (I : Input) (i : Nat) :
    (ProcActualInput.initial I).al[i]! ≤ I.p.maxAllowance := by
  unfold ProcActualInput.initial linkPass
  dsimp only
  by_cases hi : i < I.ids.length * I.ids.length
  · rw [getElem!_pos _ i (by simpa using hi)]
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
    split
    · exact Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_right _ _)
    · exact Nat.min_le_right _ _
  · rw [getElem!_neg _ i (by simpa using hi)]
    exact Nat.zero_le _

/-- Actual PV86 processing cannot emit a key reaching the AIR sentinel. -/
theorem process_sentinel (I : Input) (st : PState) (rs : List Round)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length = some I.p)
    (h : ProcActualInput.process I = .ok (st, rs)) :
    ∀ rd ∈ rs, rd.key < Proc.KSENT := by
  have ha : I.p.maxAllowance = 4500000 := by rw [lp_calc hp]
  apply process_cap Proc.KSENT I.ids.length (by decide) I.allowed _ _ st _ rs ?_ h
  intro i
  have hb := initial_allowance I i
  rw [ha] at hb
  change _ < 16777216
  omega

/-- Transport the model cap through the exact replay key sequence. -/
theorem replay_sentinel (I : Input) (cv : Array CReq) (st : PState) (rs : List Round)
    (out : ProcActualReplayRound.Acc)
    (hpp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length = some I.p)
    (hp : ProcActualInput.process I = .ok (st, rs))
    (hr : ProcActualReplayFactor.replay I cv rs = .ok out) :
    ∀ rd ∈ (ProcActualReplayKeyTrace.rounds out).toList, rd.K < Proc.KSENT := by
  intro rd hd
  have hm : (rd.K, rd.z) ∈ ProcActualReplayKeyTrace.keys out := List.mem_map.mpr ⟨rd, hd, rfl⟩
  rw [(ProcActualReplayKeyTrace.replay_metadata I cv rs out hr).2] at hm
  obtain ⟨r, hmem, he⟩ := List.mem_map.mp hm
  have hb := process_sentinel I st rs hpp hp r hmem
  have he' := congrArg Prod.fst he
  change r.key = rd.K at he'
  rw [← he']
  exact hb

/-- The previous explicit emitted-key cap is now derived from actual PV86 input. -/
theorem replay_decreasing (I : Input) (cv : Array CReq) (st : PState) (rs : List Round)
    (out : ProcActualReplayRound.Acc)
    (hpp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length = some I.p)
    (hp : ProcActualInput.process I = .ok (st, rs))
    (hr : ProcActualReplayFactor.replay I cv rs = .ok out) :
    ∀ rd ∈ (ProcActualReplayKeyTrace.rounds out).toList, rd.K ≠ 0 → rd.K < rd.Kq :=
  ProcActualReplayKeyTrace.replay_decreasing I cv st rs out hp hr
    (replay_sentinel I cv st rs out hpp hp hr)

end ZkFormal.NearV3.Candidates.ProcActualModelKeyCap
