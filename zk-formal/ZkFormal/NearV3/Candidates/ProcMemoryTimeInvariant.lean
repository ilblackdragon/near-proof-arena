import ZkFormal.NearV3.Candidates.ProcActualPushLogGuard
namespace ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def Ordered (ops : Array Gen.MOp) : Prop :=
  ops.toList.Pairwise (fun a b=>a.t<b.t) ∧ ∀o∈ops.toList,0<o.t

def Before (t : Nat) (ops : Array Gen.MOp) : Prop :=
  Ordered ops ∧ ∀o∈ops.toList,o.t<t

def AllBefore (t : Nat) (logs : Array (Array Gen.MOp)) : Prop :=
  ∀ops∈logs.toList,Before t ops

theorem before_mono (t u : Nat) (ops : Array Gen.MOp) (h : Before t ops) (htu : t≤u) :
    Before u ops := ⟨h.1,fun o ho=>Nat.lt_of_lt_of_le (h.2 o ho) htu⟩

theorem append_time (t : Nat) (ops : Array Gen.MOp) (o : Gen.MOp)
    (h : Before t ops) (ht : o.t=t) (hp : 0<t) : Before (t+1) (ops.push o) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [Array.toList_push,List.pairwise_append]
    refine ⟨h.1.1,by simp,?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    rw [ht]; exact h.2 a ha
  · intro a ha
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at ha
    rcases ha with ha|rfl
    · exact h.1.2 a ha
    · omega
  · intro a ha
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at ha
    rcases ha with ha|rfl
    · have := h.2 a ha; omega
    · omega

theorem modify_time (t : Nat) (logs : Array (Array Gen.MOp)) (i : Nat) (o : Gen.MOp)
    (h : AllBefore t logs) (ht : o.t=t) (hp : 0<t) :
    AllBefore (t+1) (logs.modify i (·.push o)) := by
  intro ops hm
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem hm
  have hj' : j<logs.size := by simpa using hj
  have h0 : Before t logs[j] := h _ (Array.getElem_mem_toList hj')
  subst ops
  simp only [Array.getElem_toList,Array.getElem_modify]
  split
  · exact append_time t _ o h0 ht hp
  · exact before_mono t (t+1) _ h0 (by omega)

theorem empty_logs (t n : Nat) : AllBefore t (Array.replicate n #[]) := by
  intro ops hm
  have he : ops=#[] := (by simpa using hm : n≠0 ∧ ops=#[]).2
  subst ops
  simp [Before,Ordered]

theorem read_step (aa gg : Array Nat) (c : CReq) (ops : Array (Array Gen.MOp))
    (h : AllBefore (c.cid+1) ops) :
    ∃out,ProcActualReplayFactor.readStep aa gg c ops=.ok (.yield out) ∧
      AllBefore (c.cid+2) out := by
  refine ⟨_,rfl,?_⟩
  exact modify_time (c.cid+1) ops c.link _ h rfl (by omega)
def scanStep (o : Gen.MOp) (s : Nat×Array (Nat×Nat×Nat)) :
    Except String (ForInStep (Nat×Array (Nat×Nat×Nat))) := do
  check (s.1<o.t) "memory times not increasing"
  let cmp (x y : Nat) := (x,y,if y≤x then 1 else 0)
  let cs := s.2.push (cmp o.t (s.1+1))
  return .yield (o.t,if o.op==OP_GRANT then cs.push (cmp o.vin o.inc) else cs)

theorem scan_success (os : List Gen.MOp) (tp : Nat) (cs : Array (Nat×Nat×Nat))
    (ho : os.Pairwise (fun a b=>a.t<b.t)) (hb : ∀o∈os,tp<o.t) :
    ∃out,forIn os (tp,cs) scanStep=.ok out := by
  induction os generalizing tp cs with
  | nil => exact ⟨(tp,cs),rfl⟩
  | cons o os ih =>
    have hp := List.pairwise_cons.mp ho
    have ht := hb o (by simp)
    have he : ∃next,scanStep o (tp,cs)=.ok (.yield next) := by
      simp [scanStep,check,ht,bind,Except.bind,pure,Except.pure]
    obtain ⟨next,hn⟩ := he
    have htime : next.1=o.t := by
      simp [scanStep,check,ht,bind,Except.bind,pure,Except.pure] at hn
      rw [←hn]
    obtain ⟨out,hout⟩ := ih next.1 next.2 hp.2 (by rw [htime]; exact hp.1)
    exact ⟨out,by simpa only [List.forIn_cons,hn,bind,Except.bind] using hout⟩

theorem ordered_scan (ops : Array Gen.MOp) (cs : Array (Nat×Nat×Nat)) (h : Ordered ops) :
    ∃out,forIn ops.toList (0,cs) scanStep=.ok out :=
  scan_success ops.toList 0 cs h.1 h.2
end ZkFormal.NearV3.Candidates.ProcMemoryTimeInvariant
