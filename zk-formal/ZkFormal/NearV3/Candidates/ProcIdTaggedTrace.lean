import ZkFormal.NearV3.Candidates.ProcIdTaggedRows
namespace ZkFormal.NearV3.Candidates.ProcIdTaggedTrace
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorCells ProcIdTaggedCells ProcIdTaggedLocal

def cell (xs : List Tagged) (r : Nat) : Nat→Fp :=
  match xs[r]? with
  | none=>fun _=>0
  | some a=>cells a (xs[r+1]?)
def trace (xs : List Tagged) : Trace Fp := ⟨fun _=>22,fun _ r=>cell xs r⟩

theorem cell_some (xs : List Tagged) (r : Nat) (a : Tagged) (h:xs[r]?=some a) :
    cell xs r=cells a (xs[r+1]?) := by simp [cell,h]
theorem padding (xs : List Tagged) (r : Nat) (h:xs.length≤r) : cell xs r=(fun _=>0) := by
  simp [cell,List.getElem?_eq_none h]

theorem row_eval (xs : List Tagged) (t r : Nat) (pub : List Fp) (e : Expr) (he:e.pubBound=0) :
    e.eval (trace xs) t r pub=e.evalWith
      (env (cell xs r) (cell xs ((r+1)%2^22)) (if r=0 then 1 else 0)
        (if r+1=2^22 then 1 else 0) (if r+1=2^22 then 0 else 1)) := by
  let en:=env (cell xs r) (cell xs ((r+1)%2^22)) (if r=0 then 1 else 0)
    (if r+1=2^22 then 1 else 0) (if r+1=2^22 then 0 else 1)
  have hh:rowEnv (trace xs) t r pub={en with pub:=fun i=>pub.getD i 0} := by
    simp only [rowEnv,trace,Trace.height,en,env]
    congr 1
    funext c nx
    cases nx <;> rfl
  change e.evalWith (rowEnv (trace xs) t r pub)=e.evalWith en
  rw [hh]
  exact ProcPriorTrace.eval_pub e he en (fun i=>pub.getD i 0)

theorem boolean (xs : List Tagged) (r c : Nat) (hc:c∈[0,6,7,9,10,11,12,16,17,18,19]) :
    cell xs r c=0 ∨ cell xs r c=1 := by
  cases h:xs[r]? with
  | none=>simp [cell,h]
  | some a=>rw [cell_some xs r a h]; exact ProcIdTaggedLocal.boolean a _ c hc

theorem bits (xs : List Tagged) (t r : Nat) (pub : List Fp) (i : Interaction)
    (hi:i∈ProcPriorIdTable.interactions 70 71 72 69) (e : Expr) (he:e∈i.mult) :
    e.eval (trace xs) t r pub=0 ∨ e.eval (trace xs) t r pub=1 := by
  simp only [ProcPriorIdTable.interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he
  all_goals subst e
  all_goals simp only [Expr.eval,Expr.evalWith,rowEnv,trace,Trace.height,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Table.E.sub,ProcPriorIdTable.act,ProcPriorIdTable.isPublic,
    ProcPriorIdTable.notE,ProcPriorIdTable.adjacent,ProcPriorIdTable.gTop,
    ProcPriorIdTable.gMid,ProcPriorIdTable.gPublic]
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals first
    | exact boolean xs r 16 (by decide +kernel)
    | exact boolean xs r 17 (by decide +kernel)
    | exact boolean xs r 19 (by decide +kernel)
    | (rcases boolean xs r 0 (by decide +kernel) with h0|h0
       all_goals rcases boolean xs r 6 (by decide +kernel) with h6|h6
       all_goals rcases boolean xs ((r+1)%2^22) 0 (by decide +kernel) with hn|hn
       all_goals rw [h0]
       all_goals grind)

theorem table (xs : List Tagged) (hcap:xs.length<2^22)
    (hbound:∀a∈xs,a.1<32 ∧ a.2.event.key<2^64)
    (hfirst:∀a,xs[0]?=some a→a.2.before=none)
    (hchain:ProcIdTaggedRows.Chain Adjacent xs) (t : Nat) (pub : List Fp) :
    TableLocal (ProcPriorIdTable.table 70 71 72 69) (trace xs) t pub := by
  refine ⟨by change 1≤22; decide +kernel,by change 22≤22; decide +kernel,?_,?_⟩
  · intro r hr e he
    have hpub:=ProcPriorIdTrace.bounds 70 71 72 69 e (List.mem_append_left _ he)
    rw [row_eval xs t r pub e hpub]
    cases ha:xs[r]? with
    | none=>
      have hlen:xs.length≤r:=List.getElem?_eq_none_iff.mp ha
      rw [padding xs r hlen]
      apply ProcPriorIdPadding.padding_constraints
      · by_cases hz:r+1=2^22
        · left; simp [hz]
        · right
          have hlt:r+1<2^22:=by change r<2^22 at hr; omega
          rw [Nat.mod_eq_of_lt hlt,padding xs (r+1) (by omega)]
      · exact he
    | some a=>
      have hra:r<xs.length:=(List.getElem?_eq_some_iff.mp ha).1
      have hlt:r+1<2^22:=by omega
      rw [Nat.mod_eq_of_lt hlt,cell_some xs r a ha]
      have hf:(if r=0 then (1:Fp) else 0)=0 ∨ a.2.before=none := by
        by_cases hz:r=0
        · right; exact hfirst a (by simpa [hz] using ha)
        · left; exact ite_eq_right hz
      cases hb:xs[r+1]? with
      | none=>
        rw [padding xs (r+1) (List.getElem?_eq_none_iff.mp hb)]
        simp only [hb,ite_eq_right (show r+1≠2^22 by omega)]
        exact terminal a _ hf e he
      | some b=>
        rw [cell_some xs (r+1) b hb]
        simp only [hb,ite_eq_right (show r+1≠2^22 by omega)]
        have hab:=hbound a (List.mem_of_getElem? ha)
        have hbb:=hbound b (List.mem_of_getElem? hb)
        exact pair a b _ _ hab.1 hbb.1 hab.2 hbb.2 hf (hchain r a b ha hb) e he
  · intro r hr i hi e he
    exact bits xs t r pub i hi e he
end ZkFormal.NearV3.Candidates.ProcIdTaggedTrace
