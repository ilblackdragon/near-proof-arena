import ZkFormal.NearV3.Candidates.ProcRecordConcatCells
namespace ZkFormal.NearV3.Candidates.ProcRecordConcatGeometry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly.CodecDigest
open ProcRecordConcatTraffic ProcRecordConcatCells

def start (ids : NativeBlock→List Nat) (bs : List NativeBlock) := (rows ids bs).length
def cell (ids : NativeBlock→List Nat) (bs : List NativeBlock) (r : Nat) := (rows ids bs).getD r (fun _=>0)
theorem block_length (ids : NativeBlock→List Nat) (b : NativeBlock) : (blockRows (ids b) b).length=blockLength b := by rw [ProcRecordConcatCells.block_rows]; simp
theorem block_pos (b : NativeBlock) : 0<blockLength b := by unfold blockLength; omega

theorem block_lookup (ids : NativeBlock→List Nat) (bs pre post : List NativeBlock) (b : NativeBlock)
    (he:bs=pre++b::post) (i : Nat) (hi:i<blockLength b) :
    cell ids bs (start ids pre+i)=blockCell (ids b) b i := by
  have hlt:start ids pre+i<(rows ids bs).length := by simp [start,rows,he,List.flatMap_append,block_length]; omega
  unfold cell
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlt]
  simp only [Option.getD_some]
  unfold start rows
  simp only [he,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simpa [block_length] using hi)]
  simp [ProcRecordConcatCells.block_rows]

theorem padding (ids : NativeBlock→List Nat) (bs : List NativeBlock) (r : Nat) (hr:(rows ids bs).length≤r) :
    cell ids bs r=(fun _=>0) := by
  simp [cell,List.getD_eq_getElem?_getD,List.getElem?_eq_none hr]

theorem active_cases (ids : NativeBlock→List Nat) (bs : List NativeBlock) (r : Nat) (hr:r<(rows ids bs).length) :
    ∃pre b post i,bs=pre++b::post ∧ i<blockLength b ∧ r=start ids pre+i := by
  obtain ⟨pre,b,post,i,he,hi,hr⟩:=ProcPositionCases.flat_position (fun b=>blockRows (ids b) b) bs r hr
  exact ⟨pre,b,post,i,he,by simpa [block_length] using hi,hr⟩

theorem after_block (ids : NativeBlock→List Nat) (bs pre post : List NativeBlock) (b : NativeBlock) (he:bs=pre++b::post) :
    cell ids bs (start ids pre+blockLength b)=
      match post with | []=>(fun _=>0) | c::_=>blockCell (ids c) c 0 := by
  cases post with
  | nil =>
    apply padding ids
    simp [start,rows,he,List.flatMap_append,block_length]
  | cons c rest =>
    have hs:bs=(pre++[b])++c::rest := by simpa [List.append_assoc] using he
    have hh:=block_lookup ids bs (pre++[b]) rest c hs 0 (block_pos c)
    simpa [start,rows,List.flatMap_append,block_length] using hh
end ZkFormal.NearV3.Candidates.ProcRecordConcatGeometry
