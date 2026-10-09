import ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

/-- Native zero-based byte-key traffic consumed by WalkV3, without START. -/
def repairedKeyRow (id : Fp) (bs : NearSpec.Bytes) (i : Nat) : List (List Fp) :=
  [[id,2*(i:Fp),(((bs.getD i 0).toNat/16:Nat):Fp),0],
   [id,2*(i:Fp)+1,(((bs.getD i 0).toNat%16:Nat):Fp),0]] ++
  (if i+1=bs.length then [[id,2*(i:Fp)+2,(SYM_END:Nat),1]] else [])

def repairedKeyTraffic (id : Fp) (bs : NearSpec.Bytes) : List (List Fp) :=
  (List.range bs.length).flatMap (repairedKeyRow id bs)

theorem repaired_key_row {tr : Trace Fp} {tt s n : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (hfit : s+n≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s n)
    (i : Nat) (hi : i<n) :
    rowTraffic Candidates.KeyTrafficRepair.interactions tr tt (s+i) pub B_KEYNIB true=
      repairedKeyRow (wid.eval tr tt s pub) (physicalWalkBytes tr tt (s,n)) i := by
  have hL := Candidates.KeyTrafficRepair.local_to_base h
  have hw : tr.cell tt (s+i) walk=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 (s+i) (by omega) (by omega)
  obtain ⟨hb,hlo,hhi⟩ := walk_nibbles_byte hL (by omega) hw
  have hget : (physicalWalkBytes tr tt (s,n)).getD i 0=UInt8.ofNat (cv tr tt (s+i) wb) := by
    simp [physicalWalkBytes,List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_eq_getElem (show i<(List.range n).length by simpa using hi)]
  have hnat : ((physicalWalkBytes tr tt (s,n)).getD i 0).toNat=cv tr tt (s+i) wb := by
    rw [hget,Link.toNat_ofNat_byte hb]
  have hlast : tr.cell tt (s+i) wl=1 ↔ i+1=n := by
    constructor
    · intro hl
      by_cases he : i+1=n
      · exact he
      · have hz := hs.2.2.2.2.2 (s+i) (by omega) (by omega)
        simp [isOne,hl] at hz
    · intro he
      have hr : s+i=s+n-1 := by omega
      rw [hr]
      simpa only [isOne,decide_eq_true_eq] using hs.2.2.1
  have ht := walk_metadata hL hfit hs (x:=Candidates.ValueTable.tau) (by simp) (s+i) (by omega) (by omega)
  have hslot := walk_metadata hL hfit hs (x:=slot) (by simp) (s+i) (by omega) (by omega)
  have hid : wid.eval tr tt (s+i) pub=wid.eval tr tt s pub := by
    simp only [wid,eval_sum_cons,eval_sum_nil,eval_k,eval_c,eval_smul,ht,hslot]
  have hlen : (physicalWalkBytes tr tt (s,n)).length=n := by simp [physicalWalkBytes]
  rw [Candidates.KeyTrafficRepair.key_row]
  simp only [hw,ite_true,hlast,hid,hlo,hhi,walk_position hL hfit hs (s+i) (by omega) (by omega),
    Nat.add_sub_cancel_left,repairedKeyRow,hnat,hlen]

theorem repaired_key_segment {tr : Trace Fp} {tt s n : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (hfit : s+n≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s n) :
    (List.range' s n).flatMap (fun r =>
      rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true)=
      repairedKeyTraffic (wid.eval tr tt s pub) (physicalWalkBytes tr tt (s,n)) := by
  rw [List.range'_eq_map_range,List.flatMap_map]
  simp only [repairedKeyTraffic,physicalWalkBytes,List.length_map,List.length_range,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i hi
  exact repaired_key_row h hfit hs i (List.mem_range.mp hi)

/-- Complete actual table sends, including silence of the parser/padding suffix. -/
theorem repaired_key_physical {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt) :
    (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true)=
    q.segs.flatMap (fun p => repairedKeyTraffic (wid.eval tr tt p.1 pub)
      (physicalWalkBytes tr tt p)) := by
  have hL := Candidates.KeyTrafficRepair.local_to_base h
  rw [flatMap_rows_segs (tr.height tt) q.segs
    (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true)
    q.consecutive q.fits (by
      intro r hr hb
      have hw := zero_of_false hL hb (x:=walk) (by simp [walkBools]) (q.suffix r hr hb)
      have hl : ¬tr.cell tt r wl=1 := by
        intro hh
        have he := flag_walk hL hb (x:=wl) (by simp) hh
        rw [hw] at he
        contradiction
      simp [Candidates.KeyTrafficRepair.key_row,hw,hl])]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro p hp
  exact repaired_key_segment h
    (Nat.le_trans (seg_le_end q.segs 0 q.consecutive p hp).2 q.fits) (q.valid p hp)

end ZkFormal.NearV3.Qv.Extract
