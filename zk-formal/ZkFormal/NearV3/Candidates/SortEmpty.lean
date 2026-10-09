import ZkFormal.Near.Render.Proof.SortLocal
namespace ZkFormal.NearV3.Candidates.SortEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra

def firstSegment : Expr:=.mul .isFirst (Dsl.not (c Sort.sf))
def firstFlag : Expr:=.mul .isFirst (Dsl.not (c Sort.ft))
def replaceFirst (e : Expr) : Expr:=
  if e=firstSegment then .mul .isFirst (sub (c Sort.act) (c Sort.sf)) else
  if e=firstFlag then .mul .isFirst (sub (c Sort.act) (c Sort.ft)) else e

def table : Table:={Sort.table with maxLog:=18,constraints:=Sort.constraints.map replaceFirst}
def emptyTrace : Trace Fp:={log:=fun _=>1,cell:=fun _ _ _=>0}

theorem old_empty_impossible (t : Nat) (pub : List Fp) :
    ¬TableLocal {Sort.table with maxLog:=18} emptyTrace t pub := by
  intro h
  have he:firstSegment∈Sort.constraints:=by simp [Sort.table,Sort.constraints,firstSegment]
  have hh:=h.constr 0 (by change 0<2^1;decide) firstSegment he
  have hn:(1:Fp)≠0:=by decide
  simp only [firstSegment,Dsl.not,sub,k,c,Expr.eval,Expr.evalWith,rowEnv,emptyTrace] at hh
  grind


theorem old_first_active (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal {Sort.table with maxLog:=18} tr t pub) : tr.cell t 0 Sort.act=1 := by
  have hr:0<tr.height t:=Nat.two_pow_pos _
  have hs:=h.constr 0 hr firstSegment (by simp [Sort.table,Sort.constraints,firstSegment])
  have ha:=h.constr 0 hr (.mul (c Sort.sf) (Dsl.not (c Sort.act))) (by simp [Sort.table,Sort.constraints])
  simp only [firstSegment,Dsl.not,sub,k,c,Expr.eval,Expr.evalWith,rowEnv] at hs ha
  grind

theorem old_rids_nonempty (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal {Sort.table with maxLog:=18} tr t pub) :
    (List.range (tr.height t)).flatMap (fun r=>rowTraffic Sort.interactions tr t r pub B_RIDS false)≠[] := by
  have ha:=old_first_active tr t pub h
  intro hz
  have hz:rowTraffic Sort.interactions tr t 0 pub B_RIDS false=[]:=
    List.flatMap_eq_nil_iff.mp hz 0 (List.mem_range.mpr (Nat.two_pow_pos _))
  simp [rowTraffic,Sort.interactions,recv,Interaction.multNat,Interaction.multNat.go,
    c,Expr.eval,Expr.evalWith,rowEnv,ha] at hz

private theorem empty_constraint (t r : Nat) (pub : List Fp) (e : Expr)
    (he:e∈table.constraints) : e.eval emptyTrace t r pub=0 := by
  simp only [table,List.mem_map] at he
  obtain ⟨e,he,rfl⟩:=he
  simp only [Sort.constraints,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (⟨x,hx,rfl⟩|he)|⟨j,hj,rfl⟩
  · rcases hx with (rfl|rfl|rfl|rfl|rfl|rfl)|⟨j,hj,rfl⟩
    all_goals simp [replaceFirst,firstSegment,firstFlag,Dsl.bool,Dsl.not,sub,k,c,Expr.eval,Expr.evalWith,rowEnv,emptyTrace] <;> grind
  · rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp +decide [replaceFirst,firstSegment,firstFlag,Dsl.bool,Dsl.not,mul3,sub,smul,c,n,k,Sort.diffE,bits,Expr.eval,Expr.evalWith,rowEnv,emptyTrace] <;> grind
  · simp +decide [replaceFirst,firstSegment,firstFlag,Dsl.bool,Dsl.not,mul3,sub,smul,c,n,k,Expr.eval,Expr.evalWith,rowEnv,emptyTrace] <;> grind

theorem empty_local (t : Nat) (pub : List Fp) : TableLocal table emptyTrace t pub := by
  refine ⟨by change 1≤1;decide,by change 1≤18;decide,?_,?_⟩
  · intro r _ e he;exact empty_constraint t r pub e he
  · intro r hr i hi b hb
    simp only [table,Sort.table,Sort.interactions,recv,List.mem_cons,List.not_mem_nil,or_false] at hi
    subst i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    subst b
    exact Or.inl rfl

theorem empty_count (t : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount table.interactions emptyTrace t pub bus sd msg=0 := by
  rw [tableBusCount_eq]
  simp [table,Sort.table,Sort.interactions,rowTraffic,recv,Interaction.multNat,Interaction.multNat.go,
    c,Expr.eval,Expr.evalWith,rowEnv,emptyTrace]
  rw [List.flatMap_eq_nil_iff.mpr (fun _ _=>rfl)]
  rfl
end ZkFormal.NearV3.Candidates.SortEmpty
