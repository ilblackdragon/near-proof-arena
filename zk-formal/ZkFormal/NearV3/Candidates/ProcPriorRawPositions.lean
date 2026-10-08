import ZkFormal.NearV3.Candidates.ProcPriorRawRows
namespace ZkFormal.NearV3.Candidates.ProcPriorRawPositions
open NearSpec NearSpec.Bandwidth ProcPriorRawRows

theorem chunk_positions (start : Nat) (c : Chunk) :
    (chunkRows start c).map (·.pos)=List.range' start c.bytes.length := by
  simp only [chunkRows,List.map_map]
  change (c.bytes.zipIdx.map (fun x=>start+x.2))=List.range' start c.bytes.length
  calc
    _ = (c.bytes.zipIdx.map Prod.snd).map (fun n=>start+n) := by rw [List.map_map]; rfl
    _ = _ := by rw [List.zipIdx_map_snd,List.map_add_range']; rfl

theorem positions (start : Nat) (cs : List Chunk) :
    (rowsFrom start cs).map (·.pos)=List.range' start (cs.flatMap (·.bytes)).length := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    simp only [rowsFrom,List.map_append,chunk_positions,ih,List.flatMap_cons,List.length_append]
    exact List.range'_append_1

theorem decoded_positions (bs : Bytes) (st : State) (hd:State.decode bs=some st) :
    (rows st).map (·.pos)=List.range bs.length := by
  rw [rows,positions,chunks_bytes,←(ProcPriorDecode.decode_exact bs st hd).2.2.2]
  simp [List.range'_eq_map_range]

/-- Every original authenticated byte is requested at its original position
exactly once; unknown IDs and duplicate records do not alter that stream. -/
theorem decoded_zip (bs : Bytes) (st : State) (hd:State.decode bs=some st) :
    (rows st).map (fun r=>(r.byte,r.pos))=bs.zipIdx := by
  apply List.ext_getElem?
  intro j
  have hb:=congrArg (fun xs:Bytes=>xs[j]?) (decoded_bytes bs st hd)
  have hp:=congrArg (fun xs:List Nat=>xs[j]?) (decoded_positions bs st hd)
  simp only [List.getElem?_map] at hb hp
  cases hr:(rows st)[j]? with
  | none => simp [hr] at hb hp; simp [List.getElem?_map,hr,hb]
  | some r =>
    simp only [hr,Option.map_some] at hb hp
    have hj:j<bs.length:= (List.getElem?_eq_some_iff.mp hb.symm).1
    have hpos:r.pos=j := by simpa [List.getElem?_range,hj] using hp
    simp [List.getElem?_map,hr,List.getElem?_zipIdx,hb.symm,hpos]

end ZkFormal.NearV3.Candidates.ProcPriorRawPositions
