import ZkFormal.NearV3.Candidates.ProcCodecGeneratedBits
import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeBytes
set_option maxRecDepth 4096
namespace ZkFormal.NearV3.Candidates.ProcCodecSuffixCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecAssignments ProcPriorCodecNativeHash

theorem appended_map {α : Type} [Inhabited α] (lead tail : List α)
    (f : Nat→α) (n j : Nat) (hj : j<n) :
    (lead++(List.range n).map f++tail)[lead.length+j]! = f j := by
  have h : lead.length+j<(lead++(List.range n).map f++tail).length := by simp; omega
  rw [_root_.getElem!_pos (lead++(List.range n).map f++tail) (lead.length+j) h,List.getElem_append_left (by simp; omega),
    List.getElem_append_right (by omega)]
  simp

theorem hash_cell (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (j : Nat) (hj : j<32) :
    out.rows[5+24*(R.n*R.n)+j]! = hashRow (instanceCells I R present vid)
      (ProcPriorCodecNativeBytes.digest I present) (ProcPriorCodecNativeBytes.priorHash I present)
      present (5+24*(R.n*R.n)) j := by
  obtain ⟨lead,_,hl,he⟩ := generated_placement I R present vid gb fwd out h
  rw [←Array.getElem!_toList,he]
  simpa only [hl,hashRows,ProcPriorCodecNativeBytes.digest,ProcPriorCodecNativeBytes.priorHash] using appended_map lead (ashRows I R present vid)
    (hashRow (instanceCells I R present vid) (ProcPriorCodecNativeBytes.digest I present)
      (ProcPriorCodecNativeBytes.priorHash I present) present (5+24*(R.n*R.n))) 32 j hj

theorem ash_cell (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (j : Nat) (hj : j<32) :
    out.rows[5+24*(R.n*R.n)+32+j]! = ashRow (instanceCells I R present vid)
      I (5+24*(R.n*R.n)) j := by
  obtain ⟨lead,_,hl,he⟩ := generated_placement I R present vid gb fwd out h
  have hn : (lead++hashRows I R present vid).length=5+24*(R.n*R.n)+32 := by
    simp [hashRows,hl]
  rw [←Array.getElem!_toList,he,←hn]
  simpa only [List.append_nil,ashRows] using
    appended_map (lead++hashRows I R present vid) []
      (ashRow (instanceCells I R present vid) I (5+24*(R.n*R.n))) 32 j hj
end ZkFormal.NearV3.Candidates.ProcCodecSuffixCells
