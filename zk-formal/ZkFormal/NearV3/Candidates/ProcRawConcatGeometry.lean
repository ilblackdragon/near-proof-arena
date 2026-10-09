import ZkFormal.NearV3.Candidates.ProcRawConcatInterior
import ZkFormal.NearV3.Candidates.ProcPositionCases
import ZkFormal.NearV3.Assembly.SchedulerCodecNativeBlocks
namespace ZkFormal.NearV3.Candidates.ProcRawConcatGeometry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly.CodecDigest
open ProcRawConcatBoundary

def blockLength (b : NativeBlock) : Nat := ProcPriorRawSlots.length b.old.links.length
def blockCell (b : NativeBlock) (i : Nat) : Nat→Fp :=
  stamp (Fp.ofNat b.run.tau) ((ProcPriorRawGen.trace b.old b.vid b.prior.isSome).cell 0 i)
def blockRows (b : NativeBlock) : List (Nat→Fp) := (List.range (blockLength b)).map (blockCell b)
def rows (bs : List NativeBlock) : List (Nat→Fp) := bs.flatMap blockRows
def start (bs : List NativeBlock) : Nat := (rows bs).length
def cell (bs : List NativeBlock) (r : Nat) : Nat→Fp := (rows bs).getD r (fun _=>0)
def trace (bs : List NativeBlock) : Trace Fp := ⟨fun _=>22,fun _ r=>cell bs r⟩

theorem block_length (b : NativeBlock) : (blockRows b).length=blockLength b := by simp [blockRows]
theorem block_pos (b : NativeBlock) : 0<blockLength b := by unfold blockLength ProcPriorRawSlots.length; omega

theorem block_lookup (bs pre post : List NativeBlock) (b : NativeBlock)
    (he:bs=pre++b::post) (i : Nat) (hi:i<blockLength b) :
    cell bs (start pre+i)=blockCell b i := by
  have hlt:start pre+i<(rows bs).length := by simp [start,rows,he,List.flatMap_append,block_length]; omega
  unfold cell
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlt]
  simp only [Option.getD_some]
  unfold start rows
  simp only [he,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simpa [block_length] using hi)]
  simp [blockRows]

theorem padding (bs : List NativeBlock) (r : Nat) (hr:(rows bs).length≤r) :
    cell bs r=(fun _=>0) := by
  simp [cell,List.getD_eq_getElem?_getD,List.getElem?_eq_none hr]

theorem active_cases (bs : List NativeBlock) (r : Nat) (hr:r<(rows bs).length) :
    ∃pre b post i,bs=pre++b::post ∧ i<blockLength b ∧ r=start pre+i := by
  obtain ⟨pre,b,post,i,he,hi,hr⟩:=ProcPositionCases.flat_position blockRows bs r hr
  exact ⟨pre,b,post,i,he,by simpa [block_length] using hi,hr⟩

theorem after_block (bs pre post : List NativeBlock) (b : NativeBlock) (he:bs=pre++b::post) :
    cell bs (start pre+blockLength b)=
      match post with | []=>(fun _=>0) | c::_=>blockCell c 0 := by
  cases post with
  | nil =>
    apply padding
    simp [start,rows,he,List.flatMap_append,block_length]
  | cons c rest =>
    have hs:bs=(pre++[b])++c::rest := by simpa [List.append_assoc] using he
    have hh:=block_lookup bs (pre++[b]) rest c hs 0 (block_pos c)
    simpa [start,rows,List.flatMap_append,block_length] using hh
end ZkFormal.NearV3.Candidates.ProcRawConcatGeometry
