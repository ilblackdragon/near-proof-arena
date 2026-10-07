import ZkFormal.NearV3.Qv.Extract.ParserBytes
import ZkFormal.NearV3.Extract.ValProof
import ZkFormal.Near.Link.Bus

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link
open Candidates.ValueTable

/-- Decode membership in the canonical value-byte demand without treating
field equality as natural equality outside the canonical range. -/
theorem value_byte_member {es : List ValE} (hv : ValWf es) {id pos b : Fp}
    (hm : [id,pos,b]∈(valRecvs es B_VBYTES).map Msg.toFp) :
    ∃ e∈es, ∃ i, i<e.bytes.length ∧ e.vz=false ∧
      id.toNat=e.vid ∧ pos.toNat=i ∧ b.toNat=e.bytes.getD i 0 := by
  obtain ⟨m,hm,he⟩ := List.mem_map.mp hm
  simp only [valRecvs,ite_true] at hm
  obtain ⟨e,he',hm⟩ := List.mem_flatMap.mp hm
  cases hz : e.vz with
  | true => simp [hz] at hm
  | false =>
    simp only [hz,Bool.false_eq_true,ite_false] at hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    have hi' := List.mem_range.mp hi
    have hc := hv.canon e he'
    have hs := (hv.shape e he').2 hz
    have hib : i<P := by omega
    have hbyte : e.bytes.getD i 0<P := by
      simpa [List.getD_eq_getElem?_getD,hi'] using hc.2.2.2 _ (List.getElem_mem hi')
    simp only [Msg.toFp,List.map_cons,List.map_nil,List.cons.injEq] at he
    refine ⟨e,he',i,hi',hz,?_,?_,?_⟩
    · rw [←he.1,Fp.toNat_ofNat,Nat.mod_eq_of_lt hc.1]
    · rw [←he.2.1,Fp.toNat_ofNat,Nat.mod_eq_of_lt hib]
    · rw [←he.2.2.1,Fp.toNat_ofNat,Nat.mod_eq_of_lt hbyte]

/-- A physical parser byte agrees with a canonical value record whenever the
global VBYTES balance accounts for this table's sends in value-table demand.
The count inequality remains explicit until whole-air bus composition. -/
theorem physical_byte_value {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    {es : List ValE} (hv : ValWf es)
    (hbalance : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tt pub B_VBYTES true m≤
      ((valRecvs es B_VBYTES).map Msg.toFp).count m)
    {s n : Nat} (hfit : s+n≤tr.height tt)
    (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
    (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
    (hne : cv tr tt s len≠0) (r : Nat) (hr : s≤r) (hb : r<s+n) :
    ∃ e∈es, e.vz=false ∧ e.vid=cv tr tt s vid ∧ r-s<e.bytes.length ∧
      cv tr tt r byte=e.bytes.getD (r-s) 0 := by
  let m : List Fp := [tr.cell tt s vid,((r-s:Nat):Fp),tr.cell tt r byte]
  have hm : m∈(List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_VBYTES true) := by
    apply List.mem_flatMap.mpr
    refine ⟨r,List.mem_range.mpr (by omega),?_⟩
    rw [Parser.byte_segment_row hL hfit hw hs r hr hb true]
    simp [hne,m]
  have hcount := List.count_pos_iff.mpr hm
  have hbal := hbalance m
  rw [tableBusCount_eq] at hbal
  have hmem : m∈(valRecvs es B_VBYTES).map Msg.toFp :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨e,he,i,hi,hz,hid,hpos,hbyte⟩ := value_byte_member hv hmem
  have ht := height_le hL
  have hsmall : r-s<P := by unfold P; omega
  have hip : i=r-s := by
    simpa only [toNat_natCast,Nat.mod_eq_of_lt hsmall] using hpos.symm
  rw [hip] at hi hbyte
  exact ⟨e,he,hz,hid.symm,hi,hbyte⟩

end ZkFormal.NearV3.Qv.Extract
