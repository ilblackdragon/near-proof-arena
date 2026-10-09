import ZkFormal.NearV3.Candidates.ProcPriorRecordConstraints
import ZkFormal.NearV3.Candidates.ProcPriorRecordLinear
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordBits
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open NearSpec NearSpec.Bandwidth NearSpecV3.Scheduler
open ProcPriorCells ProcPriorRecordTable

theorem active_bits (ids : List Nat) (tau j w g : Nat) (r : LinkAllowance)
    (hw:w<3) (hg:g<3) (nxt : Nat→Fp) (fi la tr : Fp) (rb qb ib wb pb : Nat)
    (i : Interaction) (hi:i∈ProcPriorRecordLinear.interactions rb qb ib wb pb)
    (e : Expr) (he:e∈i.mult) :
    e.evalWith (env (ProcPriorRecordCells.cell ids tau ⟨j,w,g,r⟩) nxt fi la tr)=0 ∨
    e.evalWith (env (ProcPriorRecordCells.cell ids tau ⟨j,w,g,r⟩) nxt fi la tr)=1 := by
  let C:=ProcPriorRecordCells.cell ids tau ⟨j,w,g,r⟩
  have hword:w=0 ∨ w=1 ∨ w=2:=by omega
  have hs:C 4+C 5+C 6=1:=by
    rcases hword with rfl|rfl|rfl <;> simp [C,ProcPriorRecordCells.cell,bit] <;> decide +kernel
  have hq:C 4+C 5=0 ∨ C 4+C 5=1:=by
    rcases hword with rfl|rfl|rfl <;> simp [C,ProcPriorRecordCells.cell,bit] <;> decide +kernel
  have hb (k : Nat) (hk:k∈[0,4,5,6,7,8,9,16,18,20,22]) : C k=0 ∨ C k=1:=
    ProcPriorRecordCells.boolean_cells ids tau ⟨j,w,g,r⟩ k hk
  have mulbit (x y : Fp) (hx:x=0 ∨ x=1) (hy:y=0 ∨ y=1) : x*y=0 ∨ x*y=1:=by
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> decide +kernel
  simp only [ProcPriorRecordLinear.interactions,interactions,List.take,List.drop,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  · exact Or.inr hs
  · exact Or.inr hs
  · change C 4+C 5+C 6+ -(C 9)=0 ∨ C 4+C 5+C 6+ -(C 9)=1
    rw [hs]
    rcases hb 9 (by simp) with h|h <;> rw [h] <;> decide +kernel
  · exact mulbit (C 9) (C 4+C 5) (hb 9 (by simp)) hq
  · exact mulbit (C 9) (C 4) (hb 9 (by simp)) (hb 4 (by simp))
  · exact mulbit (C 9) (C 5) (hb 9 (by simp)) (hb 5 (by simp))
  · exact hb 22 (by simp)
  · change C 0+ -(C 4+C 5+C 6)=0 ∨ C 0+ -(C 4+C 5+C 6)=1
    rw [hs]
    exact Or.inl (by change (1:Fp)+ -1=0; decide +kernel)

theorem header_bits (ids : List Nat) (tau : Nat) (nxt : Nat→Fp) (fi la tr : Fp)
    (rb qb ib wb pb : Nat) (i : Interaction)
    (hi:i∈ProcPriorRecordLinear.interactions rb qb ib wb pb) (e : Expr) (he:e∈i.mult) :
    e.evalWith (env (ProcPriorRecordCells.header ids tau) nxt fi la tr)=0 ∨
    e.evalWith (env (ProcPriorRecordCells.header ids tau) nxt fi la tr)=1 := by
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  simp only [ProcPriorRecordLinear.interactions,interactions,List.take,List.drop,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals simp [words,queryGate,header,sub,k,c,Expr.evalWith,env,ProcPriorRecordCells.header,
    act,sender,receiver,amount,topLimb,writeGate,hone]
  all_goals grind

theorem padding_bits (nxt : Nat→Fp) (fi la tr : Fp) (rb qb ib wb pb : Nat)
    (i : Interaction) (hi:i∈ProcPriorRecordLinear.interactions rb qb ib wb pb)
    (e : Expr) (he:e∈i.mult) : e.evalWith (env (fun _=>0) nxt fi la tr)=0 := by
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  simp only [ProcPriorRecordLinear.interactions,interactions,List.take,List.drop,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he; subst e
  all_goals simp [words,queryGate,header,sub,k,c,Expr.evalWith,env,hone]
  all_goals grind

end ZkFormal.NearV3.Candidates.ProcPriorRecordBits
