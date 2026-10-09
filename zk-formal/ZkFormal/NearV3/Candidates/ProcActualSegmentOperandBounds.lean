import ZkFormal.NearV3.Candidates.ProcActualRoundOperandBounds
namespace ZkFormal.NearV3.Candidates.ProcActualSegmentOperandBounds
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound
open ProcActualMemoryScan ProcActualMemoryOperandBounds

def SegBound (B : Nat) (g : Gen.Seg) : Prop := ∀o∈g.ops,OpBound B o

theorem scan_list (B : Nat) (gs : List Gen.Seg) (cs : Cmps)
    (hg : ∀g∈gs,Good g) (hb : ∀g∈gs,SegBound B g) (hc : Bounded B cs) :
    ∃out,forIn gs cs segmentStep=.ok out ∧ Bounded B out := by
  induction gs generalizing cs with
  | nil => exact ⟨cs,rfl,hc⟩
  | cons g gs ih =>
    obtain ⟨mid,hm⟩ := segment_success g cs (hg g (by simp))
    have hmid := segment_bound B g cs mid hc (hb g (by simp)) hm
    obtain ⟨out,ho,hout⟩ := ih mid (fun x hx=>hg x (by simp [hx])) (fun x hx=>hb x (by simp [hx])) hmid
    exact ⟨out,by simpa only [List.forIn_cons,hm,bind,Except.bind] using ho,hout⟩

theorem scan_array (B : Nat) (gs : Array Gen.Seg) (cs : Cmps)
    (hg : ∀g∈gs.toList,Good g) (hb : ∀g∈gs.toList,SegBound B g) (hc : Bounded B cs) :
    ∃out,forIn gs cs segmentStep=.ok out ∧ Bounded B out := by
  simpa only [Array.forIn_toList] using scan_list B gs.toList cs hg hb hc

theorem append_bound (B : Nat) (f : Nat → Gen.Seg) (xs : List Nat) (gs : Array Gen.Seg)
    (hf : ∀i∈xs,SegBound B (f i)) (hg : ∀g∈gs.toList,SegBound B g) :
    ∃out,forIn xs gs (ProcActualSegments.appendStep f)=.ok out ∧ ∀g∈out.toList,SegBound B g := by
  induction xs generalizing gs with
  | nil => exact ⟨gs,rfl,hg⟩
  | cons i xs ih =>
    obtain ⟨out,ho,hh⟩ := ih (gs.push (f i)) (fun j hj=>hf j (by simp [hj])) (by
      intro g hm
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hm
      rcases hm with hm|rfl
      · exact hg g hm
      · exact hf i (by simp))
    exact ⟨out,by simpa only [List.forIn_cons,ProcActualSegments.appendStep,bind,Except.bind] using ho,hh⟩

theorem build_bound (B : Nat) (I : Input) (tau : Nat) (s : Acc)
    (hb : ∀kind i,SegBound B (ProcActualSegments.make I tau s kind i)) :
    ∃gs,ProcActualSegments.build I tau s=.ok gs ∧ ∀g∈gs.toList,SegBound B g := by
  obtain ⟨a,ha,hba⟩ := append_bound B (ProcActualSegments.make I tau s 0)
    (List.range (I.ids.length*I.ids.length)) #[] (fun i _=>hb 0 i) (by simp)
  obtain ⟨b,hb',hbb⟩ := append_bound B (ProcActualSegments.make I tau s 1)
    (List.range I.ids.length) a (fun i _=>hb 1 i) hba
  obtain ⟨c,hc,hbc⟩ := append_bound B (ProcActualSegments.make I tau s 2)
    (List.range I.ids.length) b (fun i _=>hb 2 i) hbb
  exact ⟨c,by simp only [ProcActualSegments.build,ha,hb',hc,bind,Except.bind],hbc⟩

theorem build_scan_bound (B : Nat) (I : Input) (tau : Nat) (s : Acc)
    (hm : ProcActualReplayMemory.Memory s)
    (hb : ∀kind i,SegBound B (ProcActualSegments.make I tau s kind i)) :
    ∃gs cs,ProcActualSegments.build I tau s=.ok gs ∧
      forIn gs (#[] : Cmps) segmentStep=.ok cs ∧ Bounded B cs := by
  obtain ⟨gs,hg,hbound⟩ := build_bound B I tau s hb
  obtain ⟨gs',hg',hgood⟩ := ProcActualSegments.build_good I tau s hm
  have he := Except.ok.inj (hg'.symm.trans hg)
  subst gs'
  obtain ⟨cs,hcs,hbcs⟩ := scan_array B gs #[] hgood hbound (by simp [Bounded])
  exact ⟨gs,cs,hg,hcs,hbcs⟩
theorem make_bound (B : Nat) (I : Input) (tau : Nat) (s : Acc)
    (hl : ∀(i : Nat) (o : Gen.MOp),o ∈ s.2.2.2.2.1[i]!.toList → OpBound B o)
    (hs : ∀(i : Nat) (o : Gen.MOp),o ∈ s.2.2.2.2.2.1[i]!.toList → OpBound B o)
    (hr : ∀(i : Nat) (o : Gen.MOp),o ∈ s.2.2.2.2.2.2.1[i]!.toList → OpBound B o)
    (kind i : Nat) : SegBound B (ProcActualSegments.make I tau s kind i) := by
  unfold ProcActualSegments.make
  split
  · exact hl i
  · split
    · exact hs i
    · exact hr i

open NearSpecV3.Scheduler in
theorem finish_success (sp : SchedPub) (hs : SchedPubOk sp) (prev : NearSpec.Bandwidth.State)
    (tau : Nat) (cv : Array CReq) (st : PState) (s : Acc)
    (hp : ProcActualAfterMemoryReduction.pushCheck s=.ok ())
    (hf : ProcActualFinalStateGuards.checks s st=.ok ())
    (hm : ProcActualReplayMemory.Memory s)
    (hg : ProcActualRoundTimes.AllGood s)
    (hT : ∀rd∈(ProcActualRoundTimes.rounds s).toList,rd.T<2^29)
    (hK : ∀rd∈(ProcActualRoundTimes.rounds s).toList,rd.K≠0 → rd.K<rd.Kq ∧ rd.Kq<2^29)
    (hb : ∀kind i,SegBound (2^29) (ProcActualSegments.make (ProcPreparedSequence.input sp prev) tau s kind i)) :
    ∃r,ProcActualReplayFactor.finish (ProcPreparedSequence.input sp prev) tau cv st s=.ok r := by
  obtain ⟨gs,cs,hgs,hcs,hbound⟩ := build_scan_bound (2^29) _ tau s hm hb
  obtain ⟨r,hr⟩ := ProcActualRoundOperandBounds.afterMemory_success sp hs prev tau cv st s gs cs hg hT hK hbound
  refine ⟨r,?_⟩
  rw [ProcActualMemoryFactor.finish_eq,ProcActualSegmentFactor.finish_eq,
    ProcActualAfterMemoryReduction.finish_group,hp]
  simp only [bind,Except.bind,hf,hgs,hcs]
  exact hr
end ZkFormal.NearV3.Candidates.ProcActualSegmentOperandBounds
