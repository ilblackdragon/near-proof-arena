import ZkFormal.NearV3.Candidates.ProcPriorRecordTable
import ZkFormal.NearV3.Candidates.ProcPriorIdRows
import ZkFormal.NearV3.Candidates.ProcPriorRawRows
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordRows
open NearSpec NearSpec.Bandwidth ProcPriorLookup

structure Row where
  index : Nat
  word : Nat
  limb : Nat
  source : LinkAllowance
  deriving DecidableEq, Repr

def value (r : Row) : Nat:=
  if r.word=0 then r.source.sender else if r.word=1 then r.source.receiver else r.source.allowance

def byteOffset (r : Row) : Nat:=8*r.word+3*r.limb

def bytes (r : Row) : Bytes:=
  ((u64 (value r)).drop (3*r.limb)).take (if r.limb=2 then 2 else 3)

def rowsFor (r : LinkAllowance) (j : Nat) : List Row:=
  [0,1,2].flatMap fun w=>[0,1,2].map fun l=>⟨j,w,l,r⟩

def rows (rs : List LinkAllowance) : List Row:=rs.zipIdx.flatMap fun (r,j)=>rowsFor r j

theorem rowsFor_length (r : LinkAllowance) (j : Nat) : (rowsFor r j).length=9 := by rfl

theorem rows_length (rs : List LinkAllowance) : (rows rs).length=9*rs.length := by
  simp only [rows,List.length_flatMap]
  simp [rowsFor_length,List.map_const',List.sum_replicate_nat,Nat.mul_comm]

theorem word_bytes (r : LinkAllowance) (j w : Nat) :
    ([0,1,2].map fun l=>Row.mk j w l r).flatMap bytes=u64 (value ⟨j,w,0,r⟩) := by
  simp [bytes,value,u64,leN,List.range_succ]

theorem rowsFor_bytes (r : LinkAllowance) (j : Nat) :
    (rowsFor r j).flatMap bytes=u64 r.sender++u64 r.receiver++u64 r.allowance := by
  simp only [rowsFor,List.flatMap_assoc]
  simp only [List.flatMap_cons,List.flatMap_nil,word_bytes]
  simp [value,List.append_assoc]

/-- The physical limb parser consumes every original byte, in its original
position, even when either ID lookup fails. -/
theorem rows_bytes (rs : List LinkAllowance) :
    (rows rs).flatMap bytes=rs.flatMap (fun r=>u64 r.sender++u64 r.receiver++u64 r.allowance) := by
  simp only [rows,List.flatMap_assoc,rowsFor_bytes]
  have hm:rs.zipIdx.map Prod.fst=rs:=List.zipIdx_map_fst 0 rs
  simpa only [List.flatMap_map] using
    congrArg (List.flatMap (fun r=>u64 r.sender++u64 r.receiver++u64 r.allowance)) hm

theorem block_capacity (rs : List LinkAllowance) (h:37+24*rs.length≤2000000) :
    1+(rows rs).length<2^22 := by rw [rows_length]; omega

end ZkFormal.NearV3.Candidates.ProcPriorRecordRows
