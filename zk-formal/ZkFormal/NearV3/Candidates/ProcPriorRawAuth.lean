import ZkFormal.NearV3.Candidates.ProcPriorRawPositions
namespace ZkFormal.NearV3.Candidates.ProcPriorRawAuth
open NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched ProcPriorRawRows ProcPriorRawPositions

theorem encoded_zip (st : State) : (rows st).map (fun r=>(r.byte,r.pos))=st.encode.zipIdx := by
  have hb0:(rows st).map (·.byte)=st.encode := by rw [rows,rows_bytes,chunks_bytes]
  have hp0:(rows st).map (·.pos)=List.range st.encode.length := by
    rw [rows,positions,chunks_bytes]
    simp [List.range'_eq_map_range]
  apply List.ext_getElem?
  intro j
  have hb:=congrArg (fun xs:Bytes=>xs[j]?) hb0
  have hp:=congrArg (fun xs:List Nat=>xs[j]?) hp0
  simp only [List.getElem?_map] at hb hp
  cases hr:(rows st)[j]? with
  | none => simp [hr] at hb hp; simp [List.getElem?_map,hr,hb]
  | some r =>
    simp only [hr,Option.map_some] at hb hp
    have hj:j<st.encode.length:=(List.getElem?_eq_some_iff.mp hb.symm).1
    have hpos:r.pos=j := by simpa [List.getElem?_range,hj] using hp
    simp [List.getElem?_map,hr,List.getElem?_zipIdx,hb.symm,hpos]

/-- Exact length and authenticated point bytes identify the entire original
value. Without the length premise the checked trailing-byte fixture applies. -/
theorem authenticated_bytes (st : State) (bs : Bytes) (hl:bs.length=st.encode.length)
    (ha:∀r∈rows st,bs[r.pos]?=some r.byte) : bs=st.encode := by
  apply List.ext_getElem hl
  intro j hj hk
  have hm:(st.encode[j],j)∈st.encode.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr (by simp)
  rw [←encoded_zip st] at hm
  obtain ⟨r,hr,he⟩:=List.mem_map.mp hm
  have hb:=ha r hr
  have hbyte:r.byte=st.encode[j]:=congrArg Prod.fst he
  have hpos:r.pos=j:=congrArg Prod.snd he
  simpa only [hpos,hbyte,List.getElem?_eq_getElem hj,Option.some.injEq] using hb

/-- Sound native decoding interface for the parser: ordinary encoded fields,
exact authenticated length, and exact authenticated original byte positions. -/
theorem authenticated_decode (st : State) (bs : Bytes)
    (hc:st.links.length<2^32) (hh:st.sanityHash.length=32) (hw:∀r∈st.links,LinkOk r)
    (hl:bs.length=st.encode.length) (ha:∀r∈rows st,bs[r.pos]?=some r.byte) :
    State.decode bs=some st := by
  rw [authenticated_bytes st bs hl ha]
  exact decode_encode st hw hh hc

end ZkFormal.NearV3.Candidates.ProcPriorRawAuth
