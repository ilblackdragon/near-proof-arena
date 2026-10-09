import ZkFormal.NearV3.Candidates.ProcIdTaggedBoundary
namespace ZkFormal.NearV3.Candidates.ProcIdTaggedLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open ProcPriorCells ProcPriorIdTable ProcIdTaggedCells

theorem next_data (cur nxt nxt' : Nat→Fp) (fi la tr : Fp)
    (hn:∀c,c<9→nxt c=nxt' c) (e : Expr) (he:e∈constraints) :
    e.evalWith (env cur nxt fi la tr)=e.evalWith (env cur nxt' fi la tr) := by
  have hm:constraints.map (fun e=>e.evalWith (env cur nxt fi la tr))=
      constraints.map (fun e=>e.evalWith (env cur nxt' fi la tr)) := by
    simp [constraints,ZkFormal.Chacha.Table.boolC,eqs,dTop,dMid,dLo,ProcPriorIdTable.top,
      adjacent,notE,sub,k,c,n,Expr.evalWith,env,
      act,tau,keyLo,keyMid,keyHi,ordinal,isPublic,found,index,ProcPriorIdTable.take,
      eqTop,eqMid,eqLo,invTop,invMid,invLo,gTop,gMid,gAll,gPublic,
      hn 0 (by omega),hn 1 (by omega),hn 2 (by omega),hn 3 (by omega),hn 4 (by omega),
      hn 5 (by omega),hn 6 (by omega),hn 7 (by omega),hn 8 (by omega)]
  exact List.map_inj_left.mp hm e he

def Adjacent (a b : Tagged) : Prop :=
  (a.1=b.1 ∧
    b.2.before=(if a.2.event.key=b.2.event.key then ProcPriorIdCarry.update a.2.before a.2.event else none) ∧
    ProcPriorIds.precedes a.2.event b.2.event=true) ∨
  (a.1<b.1 ∧ b.2.before=none)

theorem pair (a b : Tagged) (after : Option Tagged) (fi : Fp)
    (hat:a.1<32) (hbt:b.1<32) (ha:a.2.event.key<2^64) (hb:b.2.event.key<2^64)
    (hf:fi=0 ∨ a.2.before=none) (hab:Adjacent a b)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cells a (some b)) (cells b after) fi 0 1)=0 := by
  have hd (c:Nat) (hc:c<9) : cells b after c=ProcPriorIdCells.cells b.2 none b.1 c :=
    (data b after c (by omega)).trans (data_next b.2 _ none b.1 c (by omega))
  rw [next_data _ _ _ fi 0 1 hd e he]
  rcases hab with ⟨ht,hn,ho⟩|⟨ht,hn⟩
  · rw [cells,ite_eq_left ht,←ht]
    exact ProcPriorIdActive.pair_constraints a.2 b.2 none a.1 fi ha hb hf hn ho e he
  · rw [cells,ite_eq_right (by omega : a.1≠b.1)]
    exact ProcIdTaggedBoundary.cross_constraints a b none fi hat hbt ht ha hb hf hn e he

theorem terminal (a : Tagged) (fi : Fp) (hf:fi=0 ∨ a.2.before=none)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cells a none) (fun _=>0) fi 0 1)=0 :=
  ProcPriorIdBoundary.end_constraints a.2 a.1 fi hf e he

theorem boolean (a : Tagged) (next : Option Tagged) (col : Nat)
    (hc:col∈[0,6,7,9,10,11,12,16,17,18,19]) : cells a next col=0 ∨ cells a next col=1 := by
  cases next with
  | none=>exact ProcPriorIdCells.boolean_cells a.2 none a.1 col hc
  | some b=>
    simp only [cells]
    split
    · exact ProcPriorIdCells.boolean_cells a.2 (some b.2) a.1 col hc
    · exact ProcIdTaggedBoundary.boolean_cross a b col hc
end ZkFormal.NearV3.Candidates.ProcIdTaggedLocal
