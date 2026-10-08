import ZkFormal.NearV3.Qv.Extract.ShardSilentModes
import ZkFormal.NearV3.Qv.Extract.ParserAggregate

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

/-- Inactive parser padding cannot introduce shard traffic. -/
theorem inactive_shard_row {r : Nat} (hr : r<tr.height tt)
    (hw : tr.cell tt r Candidates.CombinedTable.walk=0)
    (ha : tr.cell tt r act=0) (sd : Bool) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd=[] := by
  have hs : tr.cell tt r shard≠1 := by
    intro h
    have he := (Parser.phase_exclusive hL hr hw (x:=shard) (by simp [phases]) h).1
    rw [ha] at he
    exact (by decide : (0:Fp)≠1) he
  have hh : tr.cell tt r header=0 := by
    rcases Parser.isBool hL hr hw (x:=header) (by simp) with h|h
    · exact h
    · have he := (Parser.phase_exclusive hL hr hw (x:=header) (by simp [phases]) h).1
      rw [ha] at he
      exact False.elim ((by decide : (0:Fp)≠1) he)
  rw [parser_traffic hL hr hw,Parser.shard_row]
  have hz : (0:Fp)*tr.cell tt r (sel 3)≠1 := by grind
  simp [hs,hh,hz]

/-- Every physical parser shard message belongs to an extracted record. -/
theorem parser_shard_suffix (q : WalkChain tr tt)
    (v : ParserChain tr tt (segEnd 0 q.segs)) (sd : Bool) :
    (List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd)=
    v.segs.flatMap (fun p => (List.range' p.1 p.2).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd)) := by
  apply range_from_segments _ _ v.segs _ v.consecutive v.fits
  intro r hr hb
  have hstart := segEnd_ge v.segs (segEnd 0 q.segs) v.consecutive
  have hw := zero_of_false hL hb (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
    (q.suffix r (by omega) hb)
  have hz := v.suffix r hr hb
  have ha : tr.cell tt r act=0 := by
    rcases Parser.isBool hL hb hw (x:=act) (by simp) with ha|ha
    · exact ha
    · simp [isOne,ha] at hz
  exact inactive_shard_row hL hb hw ha sd

/-- Parser records never receive shard messages. -/
theorem parser_shard_receives (q : WalkChain tr tt) :
    (List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH false)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro r hr
  have hb := List.mem_range'.mp hr
  have hw := zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
    (q.suffix r (by omega) (by omega))
  exact Parser.shard_parser_recv hL (by omega) hw

/-- Every nonbuffer record is silent, including an absent raw value marker. -/
theorem nonbuffer_record_silent (q : WalkChain tr tt)
    (v : ParserChain tr tt (segEnd 0 q.segs)) (p : Nat × Nat) (hp : p∈v.segs)
    (hm : tr.cell tt p.1 mBuffer≠1) (sd : Bool) :
    (List.range' p.1 p.2).flatMap (fun r =>
      rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd)=[] := by
  have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hs := v.valid p hp
  have hfit : p.1+p.2≤tr.height tt := Nat.le_trans hb.2 v.fits
  have hn := hs.1
  have hw : ∀ r, p.1≤r → r<p.1+p.2 → tr.cell tt r Candidates.CombinedTable.walk=0 := by
    intro r hr hlt
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  have ha : tr.cell tt p.1 act=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 p.1 (by omega) (by omega)
  apply Parser.nonbuffer_shard_segment hL hfit hw hs _ sd
  rcases Parser.mode_cases hL (by omega) (hw p.1 (by omega) (by omega)) ha with h|h|h
  · exact Or.inl h.1
  · exact False.elim (hm h.2.1)
  · exact Or.inr h.2.2

/-- Full-table traffic splits exactly into walk requests and parser records. -/
theorem shard_all_physical (q : WalkChain tr tt)
    (v : ParserChain tr tt (segEnd 0 q.segs)) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd)=
    (List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd) ++
    v.segs.flatMap (fun p => (List.range' p.1 p.2).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd)) := by
  have he : List.range (tr.height tt)=List.range (segEnd 0 q.segs) ++
      List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs) := by
    simpa only [List.range_eq_range'] using range'_split (segEnd 0 q.segs) (tr.height tt) q.fits
  rw [he,List.flatMap_append,parser_shard_suffix hL q v sd]

end ZkFormal.NearV3.Qv.Extract
