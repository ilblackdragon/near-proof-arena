import ZkFormal.NearV3.Candidates.ProcPriorRecordPadding
import ZkFormal.NearV3.Candidates.ProcPriorTrace
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordTrace
open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.Bandwidth
open ProcPriorCells ProcPriorRecordRows

def place (j w g : Nat) : Nat:=1+9*j+3*w+g

def cells (ids : List Nat) (tau : Nat) (rs : List LinkAllowance) (p : Nat) : Nat→Fp:=
  if p=0 then ProcPriorRecordCells.header ids tau else
  let j:=(p-1)/9
  match rs[j]? with
  | none=>fun _=>0
  | some r=>ProcPriorRecordCells.cell ids tau ⟨j,((p-1)%9)/3,(p-1)%3,r⟩

def trace (ids : List Nat) (tau : Nat) (rs : List LinkAllowance) : Trace Fp:=
  {log:=fun _=>22,cell:=fun _ p=>cells ids tau rs p}

theorem header (ids : List Nat) (tau : Nat) (rs : List LinkAllowance) :
    cells ids tau rs 0=ProcPriorRecordCells.header ids tau := by simp [cells]

theorem active (ids : List Nat) (tau : Nat) (rs : List LinkAllowance)
    (j w g : Nat) (r : LinkAllowance) (hr:rs[j]?=some r) (hw:w<3) (hg:g<3) :
    cells ids tau rs (place j w g)=ProcPriorRecordCells.cell ids tau ⟨j,w,g,r⟩ := by
  have hp:place j w g≠0:=by unfold place; omega
  have hj:(place j w g-1)/9=j:=by unfold place; omega
  have hwm:((place j w g-1)%9)/3=w:=by unfold place; omega
  have hgm:(place j w g-1)%3=g:=by unfold place; omega
  simp [cells,hp,hj,hwm,hgm,hr]

theorem padding (ids : List Nat) (tau : Nat) (rs : List LinkAllowance) (p : Nat)
    (hp:1+9*rs.length≤p) : cells ids tau rs p=fun _=>0 := by
  have h0:p≠0:=by omega
  have hn:rs[(p-1)/9]?=none:=List.getElem?_eq_none_iff.mpr (by omega)
  simp [cells,h0,hn]

theorem bounds (rb qb ib wb pb : Nat) :
    ∀e∈(ProcPriorRecordTable.table rb qb ib wb pb).exprs,e.pubBound=0 := by
  have h:((ProcPriorRecordTable.table rb qb ib wb pb).exprs.all (fun e=>decide (e.pubBound=0)))=true := by
    change ((ProcPriorRecordTable.table 0 0 0 0 0).exprs.all (fun e=>decide (e.pubBound=0)))=true
    decide +kernel
  exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)

theorem row_eval (ids : List Nat) (tau : Nat) (rs : List LinkAllowance)
    (tt j : Nat) (pub : List Fp) (e : Expr) (he:e.pubBound=0) :
    e.eval (trace ids tau rs) tt j pub=e.evalWith
      (env (cells ids tau rs j) (cells ids tau rs ((j+1)%2^22))
        (if j=0 then 1 else 0) (if j+1=2^22 then 1 else 0) (if j+1=2^22 then 0 else 1)) := by
  let en:=env (cells ids tau rs j) (cells ids tau rs ((j+1)%2^22))
    (if j=0 then 1 else 0) (if j+1=2^22 then 1 else 0) (if j+1=2^22 then 0 else 1)
  have hc:rowEnv (trace ids tau rs) tt j pub={en with pub:=fun i=>pub.getD i 0} := by
    simp only [rowEnv,trace,Trace.height,en,env]
    congr 1
    funext c nx
    cases nx <;> rfl
  change e.evalWith (rowEnv (trace ids tau rs) tt j pub)=e.evalWith en
  rw [hc]
  exact ProcPriorTrace.eval_pub e he en (fun i=>pub.getD i 0)

end ZkFormal.NearV3.Candidates.ProcPriorRecordTrace
