import ZkFormal.NearV3.Candidates.ProcActualReplayMemory
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryScan
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcMemoryTimeInvariant
abbrev Cmps := Array (Nat×Nat×Nat)

def segmentStep (g : Gen.Seg) (cs : Cmps) : Except String (ForInStep Cmps) := do
  let mut cmps := cs
  let mut tp := 0
  let cmpOf (x y : Nat) : Nat×Nat×Nat := (x,y,if y≤x then 1 else 0)
  for o in g.ops do
    check (tp<o.t) "memory times not increasing"
    cmps := cmps.push (cmpOf o.t (tp+1))
    if o.op==OP_GRANT then cmps := cmps.push (cmpOf o.vin o.inc)
    tp := o.t
  return .yield cmps

def actualStep (o : Gen.MOp) (s : Cmps×Nat) : Except String (ForInStep (Cmps×Nat)) := do
  check (s.2<o.t) "memory times not increasing"
  let cmpOf (x y : Nat) : Nat×Nat×Nat := (x,y,if y≤x then 1 else 0)
  let mut cs := s.1.push (cmpOf o.t (s.2+1))
  if o.op==OP_GRANT then cs := cs.push (cmpOf o.vin o.inc)
  return .yield (cs,o.t)

theorem segment_eq (g : Gen.Seg) (cs : Cmps) : segmentStep g cs=(do
    let out ← forIn g.ops (cs,0) actualStep
    pure (.yield out.1)) := by rfl

theorem actual_success (os : List Gen.MOp) (tp : Nat) (cs : Cmps)
    (ho : os.Pairwise (fun a b=>a.t<b.t)) (hb : ∀o∈os,tp<o.t) :
    ∃out,forIn os (cs,tp) actualStep=.ok out := by
  induction os generalizing tp cs with
  | nil => exact ⟨(cs,tp),rfl⟩
  | cons o os ih =>
    have hp := List.pairwise_cons.mp ho
    have ht := hb o (by simp)
    have he : ∃next,actualStep o (cs,tp)=.ok (.yield (next,o.t)) := by
      unfold actualStep
      simp only [check,ht,decide_true,ite_true,bind,Except.bind,pure,Except.pure]
      split <;> exact ⟨_,rfl⟩
    obtain ⟨next,hn⟩ := he
    obtain ⟨out,hout⟩ := ih o.t next hp.2 hp.1
    exact ⟨out,by simpa only [List.forIn_cons,hn,bind,Except.bind] using hout⟩

def Good (g : Gen.Seg) : Prop := g.ops.Pairwise (fun a b=>a.t<b.t) ∧ ∀o∈g.ops,0<o.t

theorem segment_success (g : Gen.Seg) (cs : Cmps) (h : Good g) :
    ∃out,segmentStep g cs=.ok (.yield out) := by
  obtain ⟨out,ho⟩ := actual_success g.ops 0 cs h.1 h.2
  rw [segment_eq,ho]
  exact ⟨out.1,rfl⟩

theorem list_success (gs : List Gen.Seg) (cs : Cmps) (h : ∀g∈gs,Good g) :
    ∃out,forIn gs cs segmentStep=.ok out := by
  induction gs generalizing cs with
  | nil => exact ⟨cs,rfl⟩
  | cons g gs ih =>
    obtain ⟨next,hn⟩ := segment_success g cs (h g (by simp))
    obtain ⟨out,ho⟩ := ih next (fun g hg=>h g (by simp [hg]))
    exact ⟨out,by simpa only [List.forIn_cons,hn,bind,Except.bind] using ho⟩

theorem array_success (gs : Array Gen.Seg) (cs : Cmps) (h : ∀g∈gs.toList,Good g) :
    ∃out,forIn gs cs segmentStep=.ok out := by
  simpa only [Array.forIn_toList] using list_success gs.toList cs h
end ZkFormal.NearV3.Candidates.ProcActualMemoryScan
