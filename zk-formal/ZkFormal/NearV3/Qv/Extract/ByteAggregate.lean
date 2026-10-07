import ZkFormal.NearV3.Qv.Extract.ParserAggregate
import ZkFormal.NearV3.Qv.Extract.ParserStream

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

/-- The combined table's only VBYTES interaction is its parser byte gate. -/
theorem combined_byte_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (sd : Bool) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_VBYTES sd=
      if sd ∧ tr.cell tt r gb=1 then [Parser.byteMessage tr tt r] else [] := by
  cases sd <;> by_cases hg : tr.cell tt r gb=1 <;>
    simp [rowTraffic,Candidates.CombinedTable.interactions,send,recv,B_QVC,B_VBYTES,B_QSH,
      B_FINAL,B_KEYNIB,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,
      Parser.byteMessage,hg,eval_c]

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem walk_byte_silent {r : Nat} (hr : r<tr.height tt)
    (hw : tr.cell tt r Candidates.CombinedTable.walk=1) (sd : Bool) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_VBYTES sd=[] := by
  have ha := con hL hr (e:=eqG (c Candidates.CombinedTable.walk) (c act) (k 1))
    (by simp [Candidates.CombinedTable.constraints])
  have hz := con hL hr (e:=eqG (c Candidates.CombinedTable.walk) (c vz) (k 1))
    (by simp [Candidates.CombinedTable.constraints])
  have hg := con hL hr (Candidates.CombinedTable.parser_constraint_mem
    (e:=sub (c gb) (sub (c act) (c vz))) (by simp [constraints]))
  simp only [eval_eqG,eval_c,eval_k,hw] at ha hz
  simp [sub,c,Candidates.CombinedTable.parserExpr,gb,act,vz,len,
    Expr.eval,Expr.evalWith,rowEnv] at hg
  have hgb : tr.cell tt r gb=0 := by
    simp only [act,vz] at ha hz
    dsimp only [gb]
    grind
  rw [combined_byte_row]
  simp [hgb]

theorem parser_byte_suffix (q : WalkChain tr tt)
    (v : ParserChain tr tt (segEnd 0 q.segs)) :
    (List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_VBYTES true)=
    v.segs.flatMap (fun p => physicalRecordBytes tr tt p.1 p.2 pub) := by
  apply range_from_segments _ _ v.segs _ v.consecutive v.fits
  intro r hr hb
  have hstart := segEnd_ge v.segs (segEnd 0 q.segs) v.consecutive
  have hw := zero_of_false hL hb (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
    (q.suffix r (by omega) hb)
  have hz := v.suffix r hr hb
  have ha : tr.cell tt r act=0 := by
    rcases Parser.isBool hL hb hw (x:=act) (by simp) with ha | ha
    · exact ha
    · simp [isOne,ha] at hz
  have hgb := Parser.byte_gate hL hb hw
  have hbool := Parser.isBool hL hb hw (x:=vz) (by simp)
  have hgbbool := Parser.isBool hL hb hw (x:=gb) (by simp)
  have hg : tr.cell tt r gb≠1 := by
    have htwo : (0:Fp)≠2 := by decide
    rcases hbool with hz | hz <;> grind
  rw [combined_byte_row]
  simp [hg]

theorem byte_all_physical (q : WalkChain tr tt)
    (v : ParserChain tr tt (segEnd 0 q.segs)) :
    (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_VBYTES true)=
    v.segs.flatMap (fun p => physicalRecordBytes tr tt p.1 p.2 pub) := by
  have he : List.range (tr.height tt)=List.range (segEnd 0 q.segs) ++
      List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs) := by
    simpa only [List.range_eq_range'] using range'_split (segEnd 0 q.segs) (tr.height tt) q.fits
  rw [he,List.flatMap_append,parser_byte_suffix hL q v]
  have hz : (List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_VBYTES true)=[] := by
    have hrange := range'_segs q.segs 0 q.consecutive
    simp only [Nat.sub_zero] at hrange
    rw [List.range_eq_range',hrange,List.flatMap_assoc]
    apply List.flatMap_eq_nil_iff.mpr
    intro p hp
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    obtain ⟨i,hi,he⟩ := List.mem_range'.mp hr
    simp only [Nat.one_mul] at he
    have hb := seg_le_end q.segs 0 q.consecutive p hp
    have hw : tr.cell tt r Candidates.CombinedTable.walk=1 := by
      simpa only [isOne,decide_eq_true_eq] using (q.valid p hp).2.2.2.1 r (by omega) (by omega)
    exact walk_byte_silent hL (by have := q.fits; omega) hw true
  rw [hz,List.nil_append]

end ZkFormal.NearV3.Qv.Extract
