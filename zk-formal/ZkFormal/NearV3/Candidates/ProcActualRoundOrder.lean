import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualZeroTrace
namespace ZkFormal.NearV3.Candidates.ProcActualRoundOrder
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualZeroTrace ProcActualZeroPending ProcActualZeroTransition ProcActualModelValid ProcActualReplayChain

theorem trace_empty {last : Option (Nat×Nat)} {xs : List (Nat×Nat)} (h : Trace last xs)
    (he : xs=[]) : last=none := by
  cases h with
  | nil => rfl
  | snoc h K z hv ho hz => simp at he

theorem trace_snoc {last : Option (Nat×Nat)} (rs : List (Nat×Nat)) (K z : Nat)
    (h : Trace last (rs++[(K,z)])) :
    ∃prev,Trace prev rs ∧ last=some (K,z) ∧ Valid K z ∧ Ordered prev K z ∧
      (K=0 → z=nextZero prev) := by
  generalize he : rs++[(K,z)]=xs at h
  cases h with
  | nil => simp at he
  | @snoc prev ps h K' z' hv ho hz =>
    have hl := congrArg List.getLast? he
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some.injEq,Prod.mk.injEq] at hl
    rcases hl with ⟨rfl,rfl⟩
    have hr : rs=ps := List.append_cancel_right he
    subst ps
    exact ⟨prev,h,rfl,hv,ho,hz⟩

def Cursor (Kq zq : Nat) (last : Option (Nat×Nat)) : Prop :=
  match last with
  | none=>Kq=Proc.KSENT ∧ zq=0
  | some (K,z)=>K=Kq ∧ z=zq ∧ Valid K z

def ZeroRule (rd : Gen.RoundD) : Prop :=
  if rd.K=0 then rd.z=rd.zq+1 else rd.z=0 ∧ rd.zq=0

theorem cursor_rule (K z Kq zq : Nat) (last : Option (Nat×Nat))
    (hc : Cursor Kq zq last) (hv : Valid K z) (ho : Ordered last K z)
    (hz : K=0 → z=nextZero last) : if K=0 then z=zq+1 else z=0 ∧ zq=0 := by
  cases last with
  | none =>
    have hq : zq=0 := hc.2
    by_cases hk : K=0
    · have hh := hz hk
      simpa [hk,nextZero,hq] using hh
    · have hh : z=0 := by simpa [Valid,hk] using hv
      simp [hk,hh,hq]
  | some p =>
    rcases p with ⟨K',z'⟩
    rcases hc with ⟨rfl,rfl,hv'⟩
    by_cases hk : K=0
    · have hh := hz hk
      by_cases hk' : K'=0
      · simpa [hk,nextZero,hk'] using hh
      · have hz' : z'=0 := by simpa [Valid,hk'] using hv'
        simpa [hk,nextZero,hk',hz'] using hh
    · have hk' : K'≠0 := by unfold Ordered at ho; omega
      have hh : z=0 := by simpa [Valid,hk] using hv
      have hh' : z'=0 := by simpa [Valid,hk'] using hv'
      simp [hk,hh,hh']

theorem stamped_rules {T kp Kq zq : Nat} {rs : List Gen.RoundD}
    (hs : Stamped T kp Kq zq rs) {last : Option (Nat×Nat)}
    (ht : Trace last (rs.map (fun rd=>(rd.K,rd.z)))) :
    Cursor Kq zq last ∧ ∀rd∈rs,ZeroRule rd := by
  induction hs generalizing last with
  | nil =>
    have hl := trace_empty ht rfl
    subst last
    exact ⟨⟨rfl,rfl⟩,by simp⟩
  | @snoc T kp Kq zq rs hs K z L kend es ih =>
    simp only [List.map_append,List.map_cons,List.map_nil] at ht
    rcases trace_snoc _ K z ht with ⟨prev,hp,hl,hv,ho,hz⟩
    subst last
    have hr := ih hp
    refine ⟨⟨rfl,rfl,hv⟩,?_⟩
    intro rd hrd
    simp only [List.mem_append,List.mem_singleton] at hrd
    rcases hrd with hrd|rfl
    · exact hr.2 rd hrd
    · exact cursor_rule K z Kq zq prev hr.1 hv ho hz

/-- Full round order follows from the successful native process: pending zero
pushes establish the ordinal increment, and checked decreases bound the key. -/
theorem run_roundOrder (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau=.ok R) :
    ∀rd∈R.rounds,ProcHeader.RoundOk rd := by
  rcases run_stamped I tau R h with ⟨T,kp,Kq,zq,hs⟩
  rcases run_trace I tau R h with ⟨last,ht⟩
  have hz := (stamped_rules hs ht).2
  have hk := ProcActualRoundBounds.run_key_lt I tau R h
  exact fun rd hr=>⟨hk rd hr,hz rd hr⟩

theorem runData (I : Input) (tau : Nat) (R : Run)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (h : ActualRun.run I tau=.ok R) : ProcData.RunData R :=
  ProcActualReplayEntries.runData_of_roundOrder I tau R hp h (run_roundOrder I tau R h)
end ZkFormal.NearV3.Candidates.ProcActualRoundOrder
