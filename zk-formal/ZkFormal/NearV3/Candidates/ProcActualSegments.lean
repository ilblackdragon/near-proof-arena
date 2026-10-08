import ZkFormal.NearV3.Candidates.ProcActualMemoryFactor
namespace ZkFormal.NearV3.Candidates.ProcActualSegments
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound
open ProcActualMemoryScan

def make (I : Input) (tau : Nat) (s : Acc) (kind i : Nat) : Gen.Seg :=
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  if kind=0 then
    ⟨addrOf tau 0 i,true,I.allowed[i]!,b2n I.allowed[i]!,lp.a2[i]!,lp.g2[i]!,s.2.2.2.2.1[i]!.toList⟩
  else if kind=1 then
    ⟨addrOf tau 1 i,false,false,0,lp.sb[i]!,0,s.2.2.2.2.2.1[i]!.toList⟩
  else
    ⟨addrOf tau 2 i,false,false,0,lp.rb[i]!,0,s.2.2.2.2.2.2.1[i]!.toList⟩

def appendStep (f : Nat → Gen.Seg) (i : Nat) (gs : Array Gen.Seg) :
    Except String (ForInStep (Array Gen.Seg)) := .ok (.yield (gs.push (f i)))

def build (I : Input) (tau : Nat) (s : Acc) : Except String (Array Gen.Seg) := do
  let gs ← forIn (List.range (I.ids.length*I.ids.length)) #[] (appendStep (make I tau s 0))
  let gs ← forIn (List.range I.ids.length) gs (appendStep (make I tau s 1))
  forIn (List.range I.ids.length) gs (appendStep (make I tau s 2))

theorem make_good (I : Input) (tau : Nat) (s : Acc) (h : ProcActualReplayMemory.Memory s)
    (kind i : Nat) : Good (make I tau s kind i) := by
  have hl := ProcActualReplayMemory.selected_ordered _ _ h.1.1 i
  have hs := ProcActualReplayMemory.selected_ordered _ _ h.1.2.1 i
  have hr := ProcActualReplayMemory.selected_ordered _ _ h.1.2.2 i
  unfold make
  split
  · exact hl
  · split
    · exact hs
    · exact hr

theorem append_good (f : Nat → Gen.Seg) (xs : List Nat) (gs : Array Gen.Seg)
    (hf : ∀i∈xs,Good (f i)) (hg : ∀g∈gs.toList,Good g) :
    ∃out,forIn xs gs (appendStep f)=.ok out ∧ ∀g∈out.toList,Good g := by
  induction xs generalizing gs with
  | nil => exact ⟨gs,rfl,hg⟩
  | cons i xs ih =>
    obtain ⟨out,ho,hh⟩ := ih (gs.push (f i)) (fun j hj=>hf j (by simp [hj])) (by
      intro g h
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at h
      rcases h with h|rfl
      · exact hg g h
      · exact hf i (by simp))
    exact ⟨out,by simpa only [List.forIn_cons,appendStep,bind,Except.bind] using ho,hh⟩

theorem build_good (I : Input) (tau : Nat) (s : Acc) (h : ProcActualReplayMemory.Memory s) :
    ∃gs,build I tau s=.ok gs ∧ ∀g∈gs.toList,Good g := by
  obtain ⟨a,ha,hga⟩ := append_good (make I tau s 0) (List.range (I.ids.length*I.ids.length)) #[]
    (fun i _=>make_good I tau s h 0 i) (by simp)
  obtain ⟨b,hb,hgb⟩ := append_good (make I tau s 1) (List.range I.ids.length) a
    (fun i _=>make_good I tau s h 1 i) hga
  obtain ⟨c,hc,hgc⟩ := append_good (make I tau s 2) (List.range I.ids.length) b
    (fun i _=>make_good I tau s h 2 i) hgb
  exact ⟨c,by simp only [build,ha,hb,hc,bind,Except.bind],hgc⟩

theorem build_scan (I : Input) (tau : Nat) (s : Acc) (h : ProcActualReplayMemory.Memory s) :
    ∃gs cs,build I tau s=.ok gs ∧ forIn gs (#[] : Cmps) segmentStep=.ok cs := by
  obtain ⟨gs,hg,hgood⟩ := build_good I tau s h
  obtain ⟨cs,hc⟩ := array_success gs #[] hgood
  exact ⟨gs,cs,hg,hc⟩
end ZkFormal.NearV3.Candidates.ProcActualSegments
