import ZkFormal.NearV3.Qv.Extract.ParserRows

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {r : Nat} (hr : r<tr.height tt) (hw : tr.cell tt r Candidates.CombinedTable.walk=0)
include hL hr hw

theorem con {e : Expr} (he : e∈constraints) : e.eval tr tt r pub=0 :=
  parser_constraints hL hr hw e he

theorem isBool {x : Nat}
    (hx : x∈([act,vf,vl,vz,gb,cont] ++ modes ++ [header,shard,firstIndex,nextIndex] ++ selectors)) :
    tr.cell tt r x=0 ∨ tr.cell tt r x=1 := by
  have he : Dsl.bool (c x)∈constraints := by
    have hm := List.mem_map_of_mem (f:=fun x => Dsl.bool (c x)) hx
    unfold constraints
    simp only [List.mem_append,hm,true_or,or_true]
  have hh := con hL hr hw he
  simp only [eval_bool,eval_c] at hh
  exact bool_cases hh

theorem continuation : tr.cell tt r cont=tr.cell tt r act*(1-tr.cell tt r vl) := by
  have hh := con hL hr hw (e:=sub (c cont) (.mul (c act) (Dsl.not (c vl)))) (by simp [constraints])
  simp only [eval_sub,eval_c,eval_mul,eval_not] at hh
  grind

theorem marker {x : Nat} (hx : x=vf ∨ x=vl) (h : tr.cell tt r x=1) : tr.cell tt r act=1 := by
  have he : Expr.mul (c x) (Dsl.not (c act))∈constraints := by
    rcases hx with rfl | rfl <;> simp [constraints]
  have hh := con hL hr hw he
  simp only [eval_mul,eval_c,eval_not,h] at hh
  grind

theorem empty_marker (hz : tr.cell tt r vz=1) :
    tr.cell tt r mRaw=1 ∧ tr.cell tt r vf=1 ∧ tr.cell tt r vl=1 ∧
    tr.cell tt r len=0 ∧ tr.cell tt r byte=0 := by
  have h1 := con hL hr hw (e:=.mul (c vz) (Dsl.not (c mRaw))) (by simp [constraints])
  have h2 := con hL hr hw (e:=.mul (c vz) (Dsl.not (c vf))) (by simp [constraints])
  have h3 := con hL hr hw (e:=.mul (c vz) (Dsl.not (c vl))) (by simp [constraints])
  have h4 := con hL hr hw (e:=.mul (c vz) (c len)) (by simp [constraints])
  have h5 := con hL hr hw (e:=.mul (c vz) (c byte)) (by simp [constraints])
  simp only [eval_mul,eval_c,eval_not,hz] at h1 h2 h3 h4 h5
  grind

theorem inside_next (hn : r+1<tr.height tt) (ha : tr.cell tt r act=1) (hl : tr.cell tt r vl=0) :
    tr.cell tt (r+1) act=1 ∧ tr.cell tt (r+1) vf=0 ∧
    tr.cell tt (r+1) pos=tr.cell tt r pos+1 := by
  have hc : tr.cell tt r cont=1 := by have hh := continuation hL hr hw; rw [ha,hl] at hh; grind
  have h1 := con hL hr hw (e:=.mul (c cont) (Dsl.not (n act))) (by simp [constraints])
  have h2 := con hL hr hw (e:=.mul (c cont) (n vf)) (by simp [constraints])
  have h3 := con hL hr hw (e:=eqG (c cont) (n pos) (.add (c pos) (k 1))) (by simp [constraints])
  simp only [eval_mul,eval_not,eval_c,eval_n,eval_eqG,eval_add,eval_k,hc,Nat.mod_eq_of_lt hn] at h1 h2 h3
  grind

theorem inside_metadata (hn : r+1<tr.height tt) (ha : tr.cell tt r act=1) (hl : tr.cell tt r vl=0)
    {x : Nat} (hx : x∈[vid,len,users,tau,count,mEmpty,mBuffer,mRaw]) :
    tr.cell tt (r+1) x=tr.cell tt r x := by
  have hc : tr.cell tt r cont=1 := by have hh := continuation hL hr hw; rw [ha,hl] at hh; grind
  have he : same x∈constraints := by
    have hm := List.mem_map_of_mem (f:=same) hx
    unfold constraints
    simp only [List.mem_append,hm,true_or,or_true]
  have hh := con hL hr hw he
  simp only [same,eval_eqG,eval_c,eval_n,hc,Nat.mod_eq_of_lt hn] at hh
  grind

theorem next_record (hn : r+1<tr.height tt) (hl : tr.cell tt r vl=1)
    (ha : tr.cell tt (r+1) act=1) : tr.cell tt (r+1) vf=1 := by
  have hh := con hL hr hw (e:=mul3 .isTransition (c vl) (.mul (n act) (Dsl.not (n vf))))
    (by simp [constraints])
  simp only [eval_mul3,eval_mul,eval_isTransition,if_neg (show ¬r+1=tr.height tt by omega),
    eval_c,eval_n,eval_not,Nat.mod_eq_of_lt hn,hl,ha] at hh
  grind

theorem padding_next (hn : r+1<tr.height tt) (ha : tr.cell tt r act=0) :
    tr.cell tt (r+1) act=0 := by
  have hh := con hL hr hw (e:=mul3 .isTransition (Dsl.not (c act)) (n act)) (by simp [constraints])
  simp only [eval_mul3,eval_isTransition,if_neg (show ¬r+1=tr.height tt by omega),
    eval_c,eval_n,eval_not,Nat.mod_eq_of_lt hn,ha] at hh
  grind

theorem physical_stop (hn : r+1=tr.height tt) (ha : tr.cell tt r act=1) :
    tr.cell tt r vl=1 := by
  have hh := con hL hr hw (e:=mul3 .isLast (c act) (Dsl.not (c vl))) (by simp [constraints])
  simp only [eval_mul3,eval_isLast,if_pos hn,eval_c,eval_not,ha] at hh
  grind

end ZkFormal.NearV3.Qv.Extract.Parser
