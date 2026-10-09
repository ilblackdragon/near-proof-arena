import ZkFormal.NearV3.Candidates.ProcPriorIdStrictOrder
import ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonValid
namespace ZkFormal.NearV3.Candidates.ProcPriorIdComparisonPair
open ProcIdTaggedCells ProcPriorComparisonRequests ProcPriorIdStrictOrder
open ZkFormal.NearV3.Sched.Complete

theorem limbs_order (a b : Nat) (h:a≤b) :
    ProcPriorIdLimbs.hi a≤ProcPriorIdLimbs.hi b ∧
    (ProcPriorIdLimbs.hi a=ProcPriorIdLimbs.hi b→ProcPriorIdLimbs.mid a≤ProcPriorIdLimbs.mid b) ∧
    (ProcPriorIdLimbs.hi a=ProcPriorIdLimbs.hi b→ProcPriorIdLimbs.mid a=ProcPriorIdLimbs.mid b→
      ProcPriorIdLimbs.lo a≤ProcPriorIdLimbs.lo b) := by
  have ha:=ProcPriorIdLimbs.reconstruct a
  have hb:=ProcPriorIdLimbs.reconstruct b
  have hal:ProcPriorIdLimbs.lo a<16777216:=Nat.mod_lt _ (by decide)
  have hbl:ProcPriorIdLimbs.lo b<16777216:=Nat.mod_lt _ (by decide)
  have ham:ProcPriorIdLimbs.mid a<16777216:=Nat.mod_lt _ (by decide)
  have hbm:ProcPriorIdLimbs.mid b<16777216:=Nat.mod_lt _ (by decide)
  omega

theorem pair_ok (a b : Tagged)
    (ha:a.1<32 ∧ a.2.event.key<2^64 ∧ a.2.event.ordinal+1<2^29)
    (hb:b.1<32 ∧ b.2.event.key<2^64 ∧ b.2.event.ordinal+1<2^29)
    (ho:Ordered a b) (q : Request) (hq:q∈idPair a b) : CmpOk q := by
  have hla:=ProcPriorIdLimbs.bounds a.2.event.key ha.2.1
  have hlb:=ProcPriorIdLimbs.bounds b.2.event.key hb.2.1
  have htop:top a≤top b:=by
    rcases ho with h|⟨ht,h⟩
    · unfold top;omega
    · have hl:=(limbs_order _ _ h.1).1
      unfold top;omega
  have hta:top a<2^29:=by unfold top;omega
  have htb:top b<2^29:=by unfold top;omega
  simp only [idPair,List.mem_append,List.mem_singleton] at hq
  rcases hq with rfl|hq
  · simp only [CmpOk,Prod.fst,Prod.snd,ite_eq_left htop]
    exact ⟨htb,hta,True.intro⟩
  · split at hq
    next ht=>
      have he:EventOrdered a.2.event b.2.event:=by rcases ho with h|⟨_,h⟩;omega;exact h
      have hl:=limbs_order _ _ he.1
      simp only [List.mem_append] at hq
      rcases hq with (hq|hq)|hq
      · split at hq
        next hg=>
          simp only [List.mem_singleton] at hq;subst q
          simp only [ProcPriorIdCells.sameTop,ProcPriorIdCells.eqLimb,decide_eq_true_eq] at hg
          have hh:=hl.2.1 hg
          simp only [CmpOk,Prod.fst,Prod.snd,ite_eq_left hh]
          exact ⟨by omega,by omega,True.intro⟩
        next=>simp at hq
      · split at hq
        next hg=>
          simp only [List.mem_singleton] at hq;subst q
          simp only [ProcPriorIdCells.gateMid,ProcPriorIdCells.sameTop,ProcPriorIdCells.sameMid,
            ProcPriorIdCells.eqLimb,Bool.and_eq_true,decide_eq_true_eq] at hg
          have hh:=hl.2.2 hg.1 hg.2
          simp only [CmpOk,Prod.fst,Prod.snd,ite_eq_left hh]
          exact ⟨by omega,by omega,True.intro⟩
        next=>simp at hq
      · split at hq
        next hg=>
          simp only [List.mem_singleton] at hq;subst q
          simp only [Bool.and_eq_true,ProcPriorIdCells.gateAll_key,decide_eq_true_eq] at hg
          have hh:=he.2 hg.1.1 hg.1.2 hg.2
          simp only [CmpOk,Prod.fst,Prod.snd,ite_eq_left (show a.2.event.ordinal+1≤b.2.event.ordinal by omega)]
          exact ⟨by omega,ha.2.2,True.intro⟩
        next=>simp at hq
    next=>simp at hq
end ZkFormal.NearV3.Candidates.ProcPriorIdComparisonPair
