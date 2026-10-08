import ZkFormal.NearV3.Candidates.ProcPriorRawActive
import ZkFormal.NearV3.Candidates.ProcPriorTrace
namespace ZkFormal.NearV3.Candidates.ProcPriorRawPhysical
open ZkFormal.Air ZkFormal.Algebra NearSpec.Bandwidth
open ProcPriorCells ProcPriorRawGen

theorem bounds (pb lb bb sb rb : Nat) :
    ∀ e ∈ (ProcPriorRawFrame.table pb lb bb sb rb).exprs, e.pubBound=0 := by
  have h : ((ProcPriorRawFrame.table pb lb bb sb rb).exprs.all
      (fun e=>decide (e.pubBound=0)))=true := by
    change ((ProcPriorRawFrame.table 0 0 0 0 0).exprs.all (fun e=>decide (e.pubBound=0)))=true
    decide +kernel
  exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)

theorem row_eval (st : State) (vid tt j : Nat) (present : Bool)
    (pub : List Fp) (e : Expr) (he:e.pubBound=0) :
    e.eval (trace st vid present) tt j pub=
      e.evalWith (env ((trace st vid present).cell 0 j)
        ((trace st vid present).cell 0 ((j+1)%2^22))
        (bit (decide (j=0))) (if j+1=2^22 then 1 else 0)
        (if j+1=2^22 then 0 else 1)) := by
  let en:=env ((trace st vid present).cell 0 j) ((trace st vid present).cell 0 ((j+1)%2^22))
    (bit (decide (j=0))) (if j+1=2^22 then 1 else 0) (if j+1=2^22 then 0 else 1)
  have hc:rowEnv (trace st vid present) tt j pub={en with pub:=fun i=>pub.getD i 0} := by
    simp only [rowEnv,trace,Trace.height,en,env,bit,decide_eq_true_eq]
    congr 1
    funext c nx
    cases nx <;> rfl
  change e.evalWith (rowEnv (trace st vid present) tt j pub)=e.evalWith en
  rw [hc]
  exact ProcPriorTrace.eval_pub e he en (fun i=>pub.getD i 0)

theorem constraints (st : State) (vid tt j : Nat) (present : Bool)
    (hc:ProcPriorRawSlots.length st.links.length<2^22)
    (hp:present=false→st=State.initial) (hj:j<2^22)
    (pub : List Fp) (e : Expr) (he:e∈ProcPriorRawFrame.constraints) :
    e.eval (trace st vid present) tt j pub=0 := by
  have hn:st.links.length<16777216 := by unfold ProcPriorRawSlots.length at hc; omega
  have hpub:e.pubBound=0:=bounds 0 0 0 0 0 e (List.mem_append_left _ he)
  rw [row_eval st vid tt j present pub e hpub]
  by_cases ha:j<ProcPriorRawSlots.length st.links.length
  · have hl:j+1≠2^22:=by omega
    have hm:(j+1)%2^22=j+1:=Nat.mod_eq_of_lt (by omega)
    rw [hm,if_neg hl,if_neg hl]
    exact ProcPriorRawActive.active_constraints st vid j present hn hp ha e he
  · rw [padding_slot st vid j present (by omega)]
    apply ProcPriorRawPadding.padding_constraints
    · by_cases hl:j+1=2^22
      · left; simp [hl]
      · right
        have hm:(j+1)%2^22=j+1:=Nat.mod_eq_of_lt (by omega)
        rw [hm,padding_slot st vid (j+1) present (by omega)]
    · exact he

end ZkFormal.NearV3.Candidates.ProcPriorRawPhysical
