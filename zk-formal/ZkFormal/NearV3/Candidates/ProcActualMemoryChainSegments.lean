import ZkFormal.NearV3.Candidates.ProcActualMemoryChainReplay
import ZkFormal.NearV3.Candidates.ProcActualComparisonFactor
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcActualMemoryChains ProcActualMemoryChainEntry

def SegChain (g : Gen.Seg) :=OpsOk g g.v0 g.w0 g.ops

theorem metadata (g g' : Gen.Seg) (hl:g.isL=g'.isL) (ha:g.al=g'.al)
    (v w : Nat) (os : List Gen.MOp) (h:OpsOk g v w os) : OpsOk g' v w os := by
  induction os generalizing v w with
  | nil=>trivial
  | cons o os ih=>
    refine ⟨⟨h.1.kind,h.1.vin,h.1.wp,h.1.rd,?_⟩,ih _ _ h.2⟩
    intro hg
    simpa only [hl,ha] using h.1.gr hg

theorem selected (gs : Nat→Gen.Seg) (logs : Array (Array Gen.MOp))
    (h:Chains gs logs) (i : Nat) (g : Gen.Seg)
    (hl:(gs i).isL=g.isL) (ha:(gs i).al=g.al)
    (hv:(gs i).v0=g.v0) (hw:(gs i).w0=g.w0) :
    OpsOk g g.v0 g.w0 logs[i]!.toList := by
  by_cases hi:i<logs.size
  · have hh:=metadata (gs i) g hl ha _ _ _ (h i hi)
    simpa only [hv,hw] using hh
  · rw [getElem!_neg logs i hi];trivial

theorem make (I : Input) (tau : Nat) (s : ProcActualReplayRound.Acc)
    (hs:let lp:=linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev);
      Inv I lp.a2 lp.g2 lp.sb lp.rb (ProcActualReplayRound.entryAcc s)) (kind i : Nat) :
    SegChain (ProcActualSegments.make I tau s kind i) := by
  unfold ProcActualSegments.make
  split
  · exact selected _ _ hs.1 i _ rfl rfl rfl rfl
  · split
    · exact selected _ _ hs.2.1 i _ rfl rfl rfl rfl
    · exact selected _ _ hs.2.2 i _ rfl rfl rfl rfl

theorem append (f : Nat→Gen.Seg) (xs : List Nat) (gs out : Array Gen.Seg)
    (hf:∀i∈xs,SegChain (f i)) (hg:∀g∈gs.toList,SegChain g)
    (h:forIn xs gs (ProcActualSegments.appendStep f)=.ok out) : ∀g∈out.toList,SegChain g := by
  apply ExceptLoop.invariant xs _ (fun a=>∀g∈a.toList,SegChain g) ?_ gs out hg h
  intro i hi a ha u hu
  simp only [ProcActualSegments.appendStep,Except.ok.injEq] at hu
  subst u
  intro g hm
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hm
  rcases hm with hm|rfl
  · exact ha g hm
  · exact hf i hi

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem build (I : Input) (tau : Nat) (s : ProcActualReplayRound.Acc) (out : Array Gen.Seg)
    (hs:let lp:=linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev); ProcActualMemoryChainEntry.Inv I lp.a2 lp.g2 lp.sb lp.rb (ProcActualReplayRound.entryAcc s)) (h:ProcActualSegments.build I tau s=.ok out) :
    ∀g∈out.toList,SegChain g := by
  unfold ProcActualSegments.build at h
  obtain ⟨a,ha,h⟩:=bind_ok h
  obtain ⟨b,hb,h⟩:=bind_ok h
  have hfa:=append _ _ _ a (fun i _=>make I tau s hs 0 i) (by simp) ha
  have hfb:=append _ _ a b (fun i _=>make I tau s hs 1 i) hfa hb
  exact append _ _ b out (fun i _=>make I tau s hs 2 i) hfb h

theorem run (I : Input) (tau : Nat) (R : Run) (h:ActualRun.run I tau=.ok R) : ∀g∈R.segs,SegChain g := by
  rw [ProcActualRunFactor.run_eq_prefix] at h
  obtain ⟨⟨cv,st,rs,ev⟩,_,h⟩:=bind_ok h
  dsimp only at h
  rw [ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq,ProcActualReplayFactor.rest_eq] at h
  obtain ⟨s,hs,h⟩:=bind_ok h
  have htag:=ProcActualMemoryChainReplay.replay I cv rs s hs
  rw [ProcActualMemoryFactor.finish_eq,ProcActualSegmentFactor.finish_eq] at h
  unfold ProcActualSegmentFactor.finishSegments at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨gs,hgs,h⟩:=bind_ok h
  obtain ⟨cs,_,h⟩:=bind_ok h
  have hg:=build I tau s gs htag hgs
  rw [ProcActualComparisonFactor.afterMemory_eq] at h
  obtain ⟨ds,_,h⟩:=bind_ok h
  unfold ProcActualComparisonFactor.finish at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  exact hg
end ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments
