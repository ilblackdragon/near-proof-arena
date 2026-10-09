import ZkFormal.NearV3.Candidates.ProcRawConcatActive
import ZkFormal.NearV3.Candidates.ProcPriorRawPhysical
namespace ZkFormal.NearV3.Candidates.ProcRawConcatLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Assembly.CodecDigest
open ProcRawConcatGeometry ProcRawConcatActive ProcPriorCells

theorem row_eval (bs : List NativeBlock) (t r : Nat) (pub : List Fp)
    (e : Expr) (he:e.pubBound=0) :
    e.eval (trace bs) t r pub=e.evalWith
      (env (cell bs r) (cell bs ((r+1)%2^22)) (if r=0 then 1 else 0)
        (if r+1=2^22 then 1 else 0) (if r+1=2^22 then 0 else 1)) := by
  let en:=env (cell bs r) (cell bs ((r+1)%2^22)) (if r=0 then 1 else 0)
    (if r+1=2^22 then 1 else 0) (if r+1=2^22 then 0 else 1)
  have hh:rowEnv (trace bs) t r pub={en with pub:=fun i=>pub.getD i 0} := by
    simp only [rowEnv,trace,Trace.height,en,env]
    congr 1
    funext c nx
    cases nx <;> rfl
  change e.evalWith (rowEnv (trace bs) t r pub)=e.evalWith en
  rw [hh]
  exact ProcPriorTrace.eval_pub e he en (fun i=>pub.getD i 0)

theorem field_bits (bs : List NativeBlock) (r c : Nat)
    (hc:c∈[0,3,6,7,8,12,14,16,18,20,22]) : cell bs r c=0 ∨ cell bs r c=1 := by
  by_cases hr:r<(rows bs).length
  · obtain ⟨pre,b,post,i,hbs,hi,he⟩:=active_cases bs r hr
    rw [he,block_lookup bs pre post b hbs i hi]
    have hn:c≠ProcPriorRawFrame.tau := by
      have hall:∀c∈([0,3,6,7,8,12,14,16,18,20,22]:List Nat),c≠ProcPriorRawFrame.tau := by decide +kernel
      exact hall c hc
    simp only [blockCell,ProcRawConcatBoundary.stamp,hn,ite_false,ProcPriorRawGen.trace]
    exact ProcPriorRawBoolean.boolean_cells b.old b.vid i b.prior.isSome _ c hc
  · rw [padding bs r (by omega)]
    exact Or.inl rfl

/-- Full physical original RawFrame local legality of ordered native blocks.
The aggregate length bound includes a physical inactive terminal row. -/
theorem table (bs : List NativeBlock) (hb:∀b∈bs,Good b)
    (hfirst:∀b rest,bs=b::rest→b.run.tau=0)
    (hnext:∀pre b c rest,bs=pre++b::c::rest→c.run.tau=b.run.tau+1)
    (hcap:(rows bs).length<2^22) (t pb lb bb sb rb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRawFrame.table pb lb bb sb rb) (trace bs) t pub := by
  refine ⟨by change 1≤22; decide +kernel,by change 22≤22; decide +kernel,?_,?_⟩
  · intro r hr e he
    have hpub:=ProcPriorRawPhysical.bounds pb lb bb sb rb e (List.mem_append_left _ he)
    rw [row_eval bs t r pub e hpub]
    by_cases ha:r<(rows bs).length
    · have hlt:r+1<2^22 := by omega
      rw [Nat.mod_eq_of_lt hlt,ite_eq_right (show r+1≠2^22 by omega),ite_eq_right (show r+1≠2^22 by omega)]
      exact active bs hb hfirst hnext r ha e he
    · rw [padding bs r (by omega)]
      apply ProcPriorRawPadding.padding_constraints
      · by_cases hz:r+1=2^22
        · left; simp [hz]
        · right
          have hlt:r+1<2^22 := by change r<2^22 at hr; omega
          rw [Nat.mod_eq_of_lt hlt,padding bs (r+1) (by omega)]
      · exact he
  · intro r hr i hi e he
    change i∈ProcPriorRawFrame.interactions pb lb bb sb rb at hi
    simp only [ProcPriorRawFrame.interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    all_goals simp only [List.mem_singleton] at he
    all_goals subst e
    all_goals exact field_bits bs r _ (by decide +kernel)
end ZkFormal.NearV3.Candidates.ProcRawConcatLocal
