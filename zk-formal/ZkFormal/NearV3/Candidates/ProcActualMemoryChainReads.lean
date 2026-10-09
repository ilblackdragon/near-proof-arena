import ZkFormal.NearV3.Candidates.ProcActualMemoryOpSemantics
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcActualMemoryChains ProcActualMemoryFinal

def Inv (gs : Nat→Gen.Seg) (aa gg : Array Nat) (logs : Array (Array Gen.MOp)) : Prop :=
  Chains gs logs ∧ Ends Gen.MOp.v aa aa logs ∧ Ends Gen.MOp.w gg gg logs

theorem step (gs : Nat→Gen.Seg) (aa gg : Array Nat)
    (hv:∀i,(gs i).v0=aa[i]!) (hw:∀i,(gs i).w0=gg[i]!)
    (c : CReq) (logs out : Array (Array Gen.MOp)) (hs:Inv gs aa gg logs)
    (h:ProcActualReplayFactor.readStep aa gg c logs=.ok (.yield out)) : Inv gs aa gg out := by
  have he:forIn [c] logs (ProcActualReplayFactor.readStep aa gg)=.ok out := by
    simp only [List.forIn_cons,h,bind,Except.bind,List.forIn_nil,pure,Except.pure]
  have hf:=reads_final aa gg [c] logs out ⟨hs.2.1,hs.2.2⟩ he
  refine ⟨?_,hf⟩
  simp only [ProcActualReplayFactor.readStep,Except.ok.injEq,ForInStep.yield.injEq] at h
  subst out
  apply ProcActualMemoryChains.modify gs logs c.link _ hs.1
  intro hi
  rw [hv,hw,hs.2.1.2 c.link hi,hs.2.2.2 c.link hi]
  exact ProcActualMemoryOpSemantics.read _ _ _ _

theorem reads (gs : Nat→Gen.Seg) (aa gg : Array Nat)
    (hv:∀i,(gs i).v0=aa[i]!) (hw:∀i,(gs i).w0=gg[i]!)
    (cs : List CReq) (logs out : Array (Array Gen.MOp)) (hs:Inv gs aa gg logs)
    (h:forIn cs logs (ProcActualReplayFactor.readStep aa gg)=.ok out) : Inv gs aa gg out := by
  induction cs generalizing logs with
  | nil=>simp only [List.forIn_nil] at h;cases h;exact hs
  | cons c cs ih=>
    have he:ProcActualReplayFactor.readStep aa gg c logs=.ok (.yield
      (logs.modify c.link (·.push ⟨c.cid+1,OP_READ,aa[c.link]!,aa[c.link]!,gg[c.link]!,gg[c.link]!,0,false,false,false⟩))) :=rfl
    rw [List.forIn_cons,he] at h
    exact ih _ (step gs aa gg hv hw c logs _ hs he) h

theorem empty (gs : Nat→Gen.Seg) (aa gg : Array Nat) (n : Nat)
    (hv:n=aa.size) (hw:n=gg.size) : Inv gs aa gg (Array.replicate n #[]) :=
  ⟨ProcActualMemoryChains.empty gs n,empty_ends _ _ _ hv,empty_ends _ _ _ hw⟩
end ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads
