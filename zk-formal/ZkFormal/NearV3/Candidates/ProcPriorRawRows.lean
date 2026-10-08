import ZkFormal.NearV3.Candidates.ProcPriorBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRawRows
open NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched

inductive Kind where
  | tag | count | sender | receiver | allowance | sanity
  deriving DecidableEq, Repr
structure Chunk where
  kind : Kind
  record : Nat
  bytes : Bytes
  deriving DecidableEq, Repr
structure Row where
  kind : Kind
  record : Nat
  offset : Nat
  pos : Nat
  byte : UInt8
  deriving DecidableEq, Repr

def recordChunks (j : Nat) (r : LinkAllowance) : List Chunk :=
  [⟨.sender,j,u64 r.sender⟩,⟨.receiver,j,u64 r.receiver⟩,⟨.allowance,j,u64 r.allowance⟩]
def chunks (st : State) : List Chunk :=
  [⟨.tag,0,[0]⟩,⟨.count,0,u32 st.links.length⟩] ++
  st.links.zipIdx.flatMap (fun (r,j)=>recordChunks j r) ++ [⟨.sanity,0,st.sanityHash⟩]
def chunkRows (start : Nat) (c : Chunk) : List Row :=
  c.bytes.zipIdx.map fun (b,j)=>⟨c.kind,c.record,j,start+j,b⟩
def rowsFrom (start : Nat) : List Chunk→List Row
  | []=>[]
  | c::cs=>chunkRows start c++rowsFrom (start+c.bytes.length) cs
def rows (st : State) : List Row:=rowsFrom 0 (chunks st)

theorem record_bytes (j : Nat) (r : LinkAllowance) :
    (recordChunks j r).flatMap (·.bytes)=r.encode := by
  simp [recordChunks,LinkAllowance.encode,List.append_assoc]

theorem records_bytes (rs : List LinkAllowance) (start : Nat) :
    ((rs.zipIdx start).flatMap (fun (r,j)=>recordChunks j r)).flatMap (·.bytes)=
      concatAll (rs.map LinkAllowance.encode) := by
  induction rs generalizing start with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.zipIdx_cons,List.flatMap_cons,List.flatMap_append,record_bytes,
      List.map_cons,concatAll,ih]

theorem chunks_bytes (st : State) : (chunks st).flatMap (·.bytes)=st.encode := by
  simp only [chunks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    records_bytes,State.encode,List.append_assoc]

theorem chunk_rows_bytes (start : Nat) (c : Chunk) : (chunkRows start c).map (·.byte)=c.bytes := by
  simp only [chunkRows,List.map_map]
  exact List.zipIdx_map_fst 0 c.bytes

theorem rows_bytes (start : Nat) (cs : List Chunk) :
    (rowsFrom start cs).map (·.byte)=cs.flatMap (·.bytes) := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih => simp [rowsFrom,List.map_append,chunk_rows_bytes,ih]

/-- Original decoding determines the complete parser byte stream, including
its actual record count and all original IDs and ordering. -/
theorem decoded_bytes (bs : Bytes) (st : State) (hd:State.decode bs=some st) :
    (rows st).map (·.byte)=bs := by
  rw [rows,rows_bytes,chunks_bytes,(ProcPriorDecode.decode_exact bs st hd).2.2.2]

theorem decoded_length (bs : Bytes) (st : State) (hd:State.decode bs=some st) :
    (rows st).length=bs.length := by
  have h:=congrArg List.length (decoded_bytes bs st hd)
  simpa only [List.length_map] using h

end ZkFormal.NearV3.Candidates.ProcPriorRawRows
