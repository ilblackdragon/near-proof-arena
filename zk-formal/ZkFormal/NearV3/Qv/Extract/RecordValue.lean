import ZkFormal.NearV3.Qv.Extract.PhysicalByteBalance
import ZkFormal.NearV3.Qv.Extract.ValueStream

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- Complete stream ownership recovers a single value record's exact natural
length and each ordered byte, not just a matching prefix. -/
theorem record_value_exact {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    {s n : Nat} (hfit : s+n≤tr.height tt)
    (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
    (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
    (hn : cv tr tt s len≠0) {vals : List ValE} (hv : ValWf vals)
    (hc : (physicalRecordBytes tr tt s n pub).Perm
      (((valRecvs vals B_VBYTES).map Msg.toFp).filter
        (fun m => decide ((byteKey m).1=tr.cell tt s vid)))) :
    ∃ e∈vals, e.vz=false ∧ e.vid=cv tr tt s vid ∧ e.len=n ∧
      cv tr tt s len=n ∧ ∀ i, i<n → cv tr tt (s+i) byte=e.bytes.getD i 0 := by
  have hp := hs.1
  have hzero : [tr.cell tt s vid,0,tr.cell tt s byte]∈physicalRecordBytes tr tt s n pub := by
    unfold physicalRecordBytes
    apply List.mem_flatMap.mpr
    refine ⟨s,List.mem_range'.mpr ⟨0,hp,by simp⟩,?_⟩
    rw [Parser.byte_segment_row hL hfit hw hs s (Nat.le_refl _) (by omega) true]
    simp [hn,Lean.Grind.Semiring.natCast_zero]
  have hmem := (List.mem_filter.mp (hc.mem_iff.mp hzero)).1
  obtain ⟨e,he,j,hj,hz,hid,_,_⟩ := value_byte_member hv hmem
  have hidF : tr.cell tt s vid=Fp.ofNat e.vid := by rw [←hid,Fp.ofNat_toNat]
  have hc' : (physicalRecordBytes tr tt s n pub).Perm (valueRecordStream e) := by
    have heq := value_stream_filter hv e he
    simpa only [byteKey,hidF,heq] using hc
  have hlength := hc'.length_eq
  unfold physicalRecordBytes at hlength
  rw [Parser.byte_segment hL hfit hw hs true] at hlength
  simp [hn,valueRecordStream,hz] at hlength
  have hshape := (hv.shape e he).2 hz
  have hlogical : cv tr tt s len=n := by
    rcases Parser.length_cases hL hfit hw hs with h | h
    · exact False.elim (hn h.2)
    · exact h
  refine ⟨e,he,hz,hid.symm,by omega,hlogical,?_⟩
  intro i hi
  have hm : [tr.cell tt s vid,(i: Fp),tr.cell tt (s+i) byte]∈physicalRecordBytes tr tt s n pub := by
    unfold physicalRecordBytes
    apply List.mem_flatMap.mpr
    refine ⟨s+i,List.mem_range'.mpr ⟨i,hi,by simp⟩,?_⟩
    rw [Parser.byte_segment_row hL hfit hw hs (s+i) (by omega) (by omega) true]
    simp [hn]
  have hvmsg := hc'.mem_iff.mp hm
  simp only [valueRecordStream,hz,Bool.false_eq_true,ite_false] at hvmsg
  obtain ⟨k,hk,heq⟩ := List.mem_map.mp hvmsg
  have hk' := List.mem_range.mp hk
  have hcanon := hv.canon e he
  have hb := height_le hL
  have hiP : i<P := by unfold P; omega
  have hkP : k<P := by omega
  simp only [Msg.toFp,List.map_cons,List.map_nil,List.cons.injEq] at heq
  have hki : k=i := Link.ofNat_inj hkP hiP (by simpa only [natCast_eq] using heq.2.1)
  subst k
  have hbyte : e.bytes.getD i 0<P := by
    simpa [List.getD_eq_getElem?_getD,hk'] using hcanon.2.2.2 _ (List.getElem_mem hk')
  change (tr.cell tt (s+i) byte).toNat=_
  rw [←heq.2.2.1,Fp.toNat_ofNat,Nat.mod_eq_of_lt hbyte]

end ZkFormal.NearV3.Qv.Extract
