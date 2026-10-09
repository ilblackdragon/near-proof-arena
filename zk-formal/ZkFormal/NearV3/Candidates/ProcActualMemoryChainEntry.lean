import ZkFormal.NearV3.Candidates.ProcActualMemoryChainReads
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryChainEntry
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcActualMemoryChains ProcActualMemoryFinal ProcActualReplayEntry

def linkSeg (I : Input) (v0 w0 : Array Nat) (i : Nat) : Gen.Seg :=
  ⟨0,true,I.allowed[i]!,b2n I.allowed[i]!,v0[i]!,w0[i]!,[]⟩
def budgetSeg (v0 : Array Nat) (i : Nat) : Gen.Seg :=⟨0,false,false,0,v0[i]!,0,[]⟩
def Inv (I : Input) (v0 w0 s0 r0 : Array Nat) (s : Acc) : Prop :=
  Chains (linkSeg I v0 w0) s.2.2.2.2.1 ∧
  Chains (budgetSeg s0) s.2.2.2.2.2.1 ∧
  Chains (budgetSeg r0) s.2.2.2.2.2.2.1

theorem budget_last (g : Gen.Seg) (hl:g.isL=false) (v w : Nat) (ops : List Gen.MOp)
    (h:OpsOk g v w ops) :
    (match ops.getLast? with | some o=>o.w | none=>w)=w := by
  induction ops generalizing v w with
  | nil=>rfl
  | cons o ops ih=>
    have hw:o.w=w := by
      rcases h.1.kind with hr|hg
      · exact (h.1.rd hr).2.1.trans h.1.wp
      · simpa [hl,h.1.wp] using (h.1.gr hg).2.2.2.2
    cases ops with
    | nil=>exact hw
    | cons p ps=>
      have hh:=ih o.v o.w h.2
      cases he:(p::ps).getLast? with
      | none=>simp_all
      | some z=>simpa only [List.getLast?_cons_cons,he] using hh.trans hw

set_option maxHeartbeats 1200000 in
theorem entry (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat)
    (T x : Nat) (v0 w0 s0 r0 : Array Nat) (s out : Acc)
    (hs:Inv I v0 w0 s0 r0 s) (hf:ProcActualMemoryFinal.Inv v0 w0 s0 r0 s)
    (h:step I cv rd sh T x s=.ok (.yield out)) : Inv I v0 w0 s0 r0 out := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,used,gi,es⟩
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals refine ⟨ProcActualMemoryChains.modify _ _ _ _ hs.1 ?_,
    ProcActualMemoryChains.modify _ _ _ _ hs.2.1 ?_,ProcActualMemoryChains.modify _ _ _ _ hs.2.2 ?_⟩
  all_goals intro hi
  all_goals first
    | (change OpOk (linkSeg I v0 w0 _) _ _ _
       dsimp only [linkSeg]
       rw [hf.1.2 _ hi,hf.2.1.2 _ hi]
       apply ProcActualMemoryOpSemantics.link _ _ _ _ _ _ rfl
       simp only [linkSeg,Bool.and_eq_true];intro hk;exact hk.2)
    | (change OpOk (budgetSeg s0 _) _ _ _
       have hw:=budget_last _ rfl _ _ _ (hs.2.1 _ hi)
       change lastValue Gen.MOp.w (budgetSeg s0 _).w0 os[_]! =0 at hw
       rw [hw]
       dsimp only [budgetSeg]
       rw [hf.2.2.1.2 _ hi]
       apply ProcActualMemoryOpSemantics.budget _ _ _ _ _ rfl
       simp only [Bool.and_eq_true,decide_eq_true_eq];intro hk;exact hk.1.1)
    | (change OpOk (budgetSeg r0 _) _ _ _
       have hw:=budget_last _ rfl _ _ _ (hs.2.2 _ hi)
       change lastValue Gen.MOp.w (budgetSeg r0 _).w0 orr[_]! =0 at hw
       rw [hw]
       dsimp only [budgetSeg]
       rw [hf.2.2.2.2 _ hi]
       apply ProcActualMemoryOpSemantics.budget _ _ _ _ _ rfl
       simp only [Bool.and_eq_true,decide_eq_true_eq];intro hk;exact hk.1.2)
end ZkFormal.NearV3.Candidates.ProcActualMemoryChainEntry
