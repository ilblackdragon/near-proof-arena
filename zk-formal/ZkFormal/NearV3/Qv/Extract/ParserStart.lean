import ZkFormal.NearV3.Qv.Extract.ParserRecord

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem walk_parser_last {r : Nat} (hr : r<tr.height tt) (ha : tr.cell tt r walk=1) :
    tr.cell tt r Candidates.ValueTable.vl=1 := by
  have hz := con hL hr (e:=eqG (c walk) (c Candidates.ValueTable.vz) (k 1)) (by simp [constraints])
  simp only [eval_eqG,eval_c,eval_k,ha] at hz
  have hv : tr.cell tt r Candidates.ValueTable.vz=1 := by grind
  have hh := con hL hr (parser_constraint_mem (e:=.mul (c Candidates.ValueTable.vz)
    (Dsl.not (c Candidates.ValueTable.vl))) (by simp [Candidates.ValueTable.constraints]))
  change (Expr.mul (c Candidates.ValueTable.vz) (Dsl.not (c Candidates.ValueTable.vl))).eval tr tt r pub=0 at hh
  simp only [eval_mul,eval_c,eval_not,hv] at hh
  grind

/-- This parser boundary constraint contains no overlaid length cell, so it
also holds on walk-marker rows. -/
theorem any_next_record {r : Nat} (hr : r+1<tr.height tt)
    (hl : tr.cell tt r Candidates.ValueTable.vl=1)
    (ha : tr.cell tt (r+1) Candidates.ValueTable.act=1) :
    tr.cell tt (r+1) Candidates.ValueTable.vf=1 := by
  have hh := con hL (show r<tr.height tt by omega)
    (parser_constraint_mem (e:=mul3 .isTransition (c Candidates.ValueTable.vl)
      (.mul (n Candidates.ValueTable.act) (Dsl.not (n Candidates.ValueTable.vf))))
      (by simp [Candidates.ValueTable.constraints]))
  change (mul3 .isTransition (c Candidates.ValueTable.vl)
    (.mul (n Candidates.ValueTable.act) (Dsl.not (n Candidates.ValueTable.vf)))).eval tr tt r pub=0 at hh
  simp only [eval_mul3,eval_mul,eval_isTransition,if_neg (show ¬r+1=tr.height tt by omega),
    eval_c,eval_n,eval_not,Nat.mod_eq_of_lt hr,hl,ha] at hh
  grind

theorem parser_suffix_start (q : WalkChain tr tt) (hr : segEnd 0 q.segs<tr.height tt)
    (ha : tr.cell tt (segEnd 0 q.segs) Candidates.ValueTable.act=1) :
    tr.cell tt (segEnd 0 q.segs) Candidates.ValueTable.vf=1 := by
  have hp : 0<q.segs.length := List.length_pos_iff.mpr q.nonempty
  let p := q.segs[q.segs.length-1]'(by omega)
  have hm : p∈q.segs := List.getElem_mem (by omega)
  have hv := q.valid p hm
  have hn := hv.1
  have he : segEnd 0 q.segs=p.1+p.2 := segEnd_last q.segs 0 q.consecutive hp
  have hpos : 0<segEnd 0 q.segs := by omega
  have hw : tr.cell tt (segEnd 0 q.segs-1) walk=1 := by
    rw [he]
    simpa only [isOne,decide_eq_true_eq] using hv.2.2.2.1 (p.1+p.2-1) (by omega) (by omega)
  have hl := walk_parser_last hL (show segEnd 0 q.segs-1<tr.height tt by omega) hw
  have he' : segEnd 0 q.segs-1+1=segEnd 0 q.segs := by omega
  have hh := any_next_record hL (show segEnd 0 q.segs-1+1<tr.height tt by omega) hl (by simpa only [he'] using ha)
  simpa only [he'] using hh

end ZkFormal.NearV3.Qv.Extract
