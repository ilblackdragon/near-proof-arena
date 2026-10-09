import ZkFormal.NearV3.Candidates.ProcActualMemoryScan
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryOperandBounds
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualMemoryScan

def Bounded (B : Nat) (cs : Cmps) : Prop := ∀c∈cs.toList,c.1<B ∧ c.2.1<B

def OpBound (B : Nat) (o : Gen.MOp) : Prop :=
  o.t<B ∧ (o.op=OP_GRANT → o.vin<B ∧ o.inc<B)

theorem push_bound (B : Nat) (cs : Cmps) (x y b : Nat) (hc : Bounded B cs)
    (hx : x<B) (hy : y<B) : Bounded B (cs.push (x,y,b)) := by
  intro c hm
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hm
  rcases hm with hm|rfl
  · exact hc c hm
  · exact ⟨hx,hy⟩

theorem step_bound (B : Nat) (o : Gen.MOp) (s out : Cmps×Nat)
    (hc : Bounded B s.1) (ho : OpBound B o)
    (h : actualStep o s=.ok (.yield out)) : Bounded B out.1 := by
  by_cases ht : s.2<o.t
  · have htime := ho.1
    have hp := push_bound B s.1 o.t (s.2+1) (if s.2+1≤o.t then 1 else 0) hc ho.1 (by omega)
    by_cases hg : o.op=OP_GRANT
    · simp [actualStep,check,ht,hg,bind,Except.bind,pure,Except.pure] at h
      cases h
      exact push_bound B _ o.vin o.inc _ hp (ho.2 hg).1 (ho.2 hg).2
    · simp [actualStep,check,ht,hg,bind,Except.bind,pure,Except.pure] at h
      cases h
      exact hp
  · simp [actualStep,check,ht,bind,Except.bind,pure,Except.pure] at h

theorem loop_bound (B : Nat) (os : List Gen.MOp) (s out : Cmps×Nat)
    (hc : Bounded B s.1) (ho : ∀o∈os,OpBound B o)
    (h : forIn os s actualStep=.ok out) : Bounded B out.1 := by
  apply ExceptLoop.invariant os actualStep (fun s=>Bounded B s.1) _ s out hc h
  intro o hm a ha next hn
  cases next with
  | done next =>
    unfold actualStep at hn
    simp only [check,bind,Except.bind,pure,Except.pure] at hn
    repeat first | cases hn | split at hn
  | yield next => exact step_bound B o a next ha (ho o hm) hn

theorem segment_bound (B : Nat) (g : Gen.Seg) (cs out : Cmps)
    (hc : Bounded B cs) (ho : ∀o∈g.ops,OpBound B o)
    (h : segmentStep g cs=.ok (.yield out)) : Bounded B out := by
  rw [segment_eq] at h
  cases he : forIn g.ops (cs,0) actualStep with
  | error e => simp only [he,bind,Except.bind] at h; cases h
  | ok next =>
    simp only [he,bind,Except.bind,pure,Except.pure] at h
    cases h
    exact loop_bound B g.ops (cs,0) next hc ho he

theorem operand_check (cs : Cmps) (hc : Bounded (2^29) cs) :
    check (cs.all fun (x,y,_)=>x<2^29 && y<2^29) "comparison operand ≥ 2^29"=.ok () := by
  have hh : (cs.all fun (x,y,_)=>x<2^29 && y<2^29)=true := by
    apply Array.all_eq_true.mpr
    intro c hm
    have hb := hc cs[c] (by simpa using Array.getElem_mem hm)
    simp [hb.1,hb.2]
  simp [hh,check,pure,Except.pure]
end ZkFormal.NearV3.Candidates.ProcActualMemoryOperandBounds
