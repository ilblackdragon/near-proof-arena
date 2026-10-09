import ZkFormal.NearV3.Rcpt.Extract.AcctProof

set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra

def oldFirst : Expr := .mul .isFirst (Dsl.not (c Acct.af))
def newFirst : Expr := .mul .isFirst (sub (c Acct.act) (c Acct.af))
def replaceFirst (e : Expr) : Expr := if e=oldFirst then newFirst else e

/-- Permit an all-inactive account table. All segment and padding rules and all
bus interactions remain unchanged; an active first row still starts a segment. -/
def table : Air.Table :=
  {AcctV3.table with constraints:=Acct.constraints.map replaceFirst}

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem table_wf : table.wf ⟨[table],67,202⟩ 8=true := by decide +kernel

theorem shape_unchanged : table.width=AcctV3.table.width ∧
    table.maxLog=AcctV3.table.maxLog ∧ table.interactions=AcctV3.table.interactions ∧
    table.constraints.length=AcctV3.table.constraints.length := by
  simp [table,AcctV3.table]

def emptyTrace : Trace Fp := {log:=fun _ => 1,cell:=fun _ _ _ => 0}

private theorem empty_constraint (tt r : Nat) (pub : List Fp) (e : Expr)
    (he : e∈table.constraints) : e.eval emptyTrace tt r pub=0 := by
  simp only [table,List.mem_map] at he
  obtain ⟨e,he,rfl⟩ := he
  simp only [Acct.constraints,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,
    or_false] at he
  rcases he with ⟨x,hx,rfl⟩|he
  · rcases hx with rfl|rfl|rfl|rfl|rfl <;>
      simp [replaceFirst,oldFirst,newFirst,Acct.act,Acct.af,Acct.al,Acct.lo8,Acct.gS,
        Dsl.bool,Dsl.not,sub,c,k,Expr.eval,Expr.evalWith,rowEnv,emptyTrace] <;> grind
  · rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [replaceFirst,oldFirst,newFirst,Acct.act,Acct.af,Acct.al,Acct.lo8,Acct.gS,
      Dsl.bool,Dsl.not,mul3,sub,c,n,k,Expr.eval,Expr.evalWith,rowEnv,emptyTrace] <;> grind

theorem empty_local (tt : Nat) (pub : List Fp) : TableLocal table emptyTrace tt pub := by
  refine ⟨by change 1≤1; omega,by change 1≤17; omega,?_,?_⟩
  · intro r _ e he
    exact empty_constraint tt r pub e he
  · intro r _ it hit e he
    simp only [table,AcctV3.table,AcctV3.interactions,AcctV3.vpre,Acct.vbytes,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hit
    rcases hit with ((rfl|rfl|rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl))|(rfl|rfl|rfl)
    all_goals simp only [send,recv,List.mem_cons,List.not_mem_nil,or_false] at he
    all_goals subst e
    all_goals exact Or.inl (by simp [c,Expr.eval,Expr.evalWith,rowEnv,emptyTrace])

end ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty
