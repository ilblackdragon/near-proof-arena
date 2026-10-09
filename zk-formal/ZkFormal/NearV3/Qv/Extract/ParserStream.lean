import ZkFormal.NearV3.Qv.Extract.ValueByteKeys
import ZkFormal.NearV3.Qv.Extract.ParserView

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

def byteKey (m : List Fp) : Fp × Fp := (m.getD 0 0,m.getD 1 0)
def physicalRecordBytes (tr : Trace Fp) (tt s n : Nat) (pub : List Fp) : List (List Fp) :=
  (List.range' s n).flatMap (fun r =>
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_VBYTES true)

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s n : Nat} (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
include hL hfit hw hs

theorem physical_record_id : ∀ m∈physicalRecordBytes tr tt s n pub,
    (byteKey m).1=tr.cell tt s vid := by
  intro m hm
  unfold physicalRecordBytes at hm
  rw [Parser.byte_segment hL hfit hw hs true] at hm
  by_cases hn : cv tr tt s len=0
  · simp [hn] at hm
  · simp only [hn,ne_eq,not_false_eq_true,and_self,ite_true] at hm
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    rfl

theorem physical_record_start (hn : cv tr tt s len≠0) :
    ∃ m∈physicalRecordBytes tr tt s n pub, byteKey m=(tr.cell tt s vid,0) := by
  have hp := hs.1
  refine ⟨[tr.cell tt s vid,0,tr.cell tt s byte],?_,rfl⟩
  unfold physicalRecordBytes
  apply List.mem_flatMap.mpr
  refine ⟨s,List.mem_range'.mpr ⟨0,hp,by simp⟩,?_⟩
  rw [Parser.byte_segment_row hL hfit hw hs s (Nat.le_refl _) (by omega) true]
  simp [hn,Lean.Grind.Semiring.natCast_zero]

/-- Physical parser records satisfy the stream-start hypothesis even for raw
mode: any emitted byte entails a position-zero byte of the same value ID. -/
theorem physical_record_closed : ∀ m∈physicalRecordBytes tr tt s n pub,
    ∃ z∈physicalRecordBytes tr tt s n pub, byteKey z=((byteKey m).1,0) := by
  intro m hm
  have hn : cv tr tt s len≠0 := by
    intro hz
    have hh := hm
    unfold physicalRecordBytes at hh
    rw [Parser.byte_segment hL hfit hw hs true] at hh
    simp [hz] at hh
  obtain ⟨z,hz,hkey⟩ := physical_record_start hL hfit hw hs hn
  exact ⟨z,hz,by rw [physical_record_id hL hfit hw hs m hm]; exact hkey⟩

/-- Complete demanded byte stream for a nonempty physical parser record.
Only global balance and the other suppliers' start-closure remain to be
supplied by whole-table assembly. -/
theorem physical_record_complete {es : List ValE} (hv : ValWf es)
    (hn : cv tr tt s len≠0) (others : List (List Fp))
    (hbalance : (physicalRecordBytes tr tt s n pub++others).Perm
      ((valRecvs es B_VBYTES).map Msg.toFp))
    (hclosed : ∀ m∈others, ∃ z∈others, byteKey z=((byteKey m).1,0)) :
    (physicalRecordBytes tr tt s n pub).Perm
      (((valRecvs es B_VBYTES).map Msg.toFp).filter
        (fun m => decide ((byteKey m).1=tr.cell tt s vid))) := by
  exact stream_isolate byteKey (tr.cell tt s vid) _ _ _ hbalance
    (value_byte_keys_unique hv) (physical_record_start hL hfit hw hs hn)
    (physical_record_id hL hfit hw hs) hclosed

omit hfit hw hs in
/-- Any subcollection of extracted parser records is start-closed. In
particular this applies to the records left after selecting one occurrence. -/
theorem physical_records_closed (q : WalkChain tr tt)
    (v : ParserChain tr tt (segEnd 0 q.segs)) (l : List (Nat × Nat))
    (hl : ∀ p∈l, p∈v.segs) :
    ∀ m∈l.flatMap (fun p => physicalRecordBytes tr tt p.1 p.2 pub),
      ∃ z∈l.flatMap (fun p => physicalRecordBytes tr tt p.1 p.2 pub),
        byteKey z=((byteKey m).1,0) := by
  intro m hm
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp hm
  have hv := hl p hp
  have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hv
  have hfit : p.1+p.2≤tr.height tt := Nat.le_trans hb.2 v.fits
  have hw : ∀ r, p.1≤r → r<p.1+p.2 → tr.cell tt r Candidates.CombinedTable.walk=0 := by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  obtain ⟨z,hz,he⟩ := physical_record_closed hL hfit hw (v.valid p hv) m hm
  exact ⟨z,List.mem_flatMap.mpr ⟨p,hp,hz⟩,he⟩

end ZkFormal.NearV3.Qv.Extract
