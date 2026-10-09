import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordByteCells
import ZkFormal.NearV3.Candidates.ProcCodecRecordTransitionShape
import ZkFormal.NearV3.Candidates.SchedSetAllRange
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSenderCells
set_option maxRecDepth 8192
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecExtra ProcPriorCodecExtraColumns SchedSetAll SchedSetAllRange

theorem row (I : Input) (present : Bool) (n k gg p bpo bpr a b : Nat)
    (inst tail : List (Nat×Nat)) (ht:Tail tail) (i : Nat) (hi:i<8) :
    (recordRow I present n k 0 gg p bpo bpr inst (baseExtra n k 0 gg a b++tail))[prbit i]! =
      (bytesLE (I.ids.getD (k/n) 0) 8).getD (gg+i) 0 := by
  have hc:prbit i<Codec.width := by unfold prbit Codec.width; omega
  have hp:prbit i∈protectedColumns := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have hbase:∀v,lookup (baseExtra n k 0 gg a b) (prbit i) v=v := by
    intro v
    apply lookup_miss
    intro p hp
    have hh:∀j:Fin 8,∀p∈baseExtra n k 0 gg a b,p.1≠prbit j.val := by
      intro j p hp
      simp only [baseExtra,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals dsimp only
      all_goals simp only [prbit,rs,al,gb,srcC,hasC,useC]
      all_goals omega
    exact hh ⟨i,hi⟩ p hp
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ hc,append,append,tail_preserves tail ht _ _ hp,hbase]
  simp only [ite_true]
  rw [append]
  change lookup (block 79 8 (fun j=>(bytesLE (I.ids.getD (k/n) 0) 8).getD (gg+j) 0)) (79+i) _=_
  rw [lookup_block,ite_eq_left (by omega)]
  congr 1
  omega

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k gg : Nat) (s out : ProcPriorCodecRecordStep.State)
    (hg:gg<8)
    (h:ProcPriorCodecRecordStep.step I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid) k 0 gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[bpost]! =idByte I.ids k gg ∧
      ∀i<8,a[prbit i]! =(bytesLE (I.ids.getD (k/R.n) 0) 8).getD (gg+i) 0 := by
  obtain ⟨tail,ht,ha⟩:=ProcPriorCodecStepRows.successful_row I R present gb fwd
    (ProcPriorCodecNativeHash.instanceCells I R present vid) k 0 gg s out (by decide) hg h
  refine ⟨_,ha,?_,?_⟩
  · simp only [ProcPriorCodecStepRows.record,Nat.mul_zero,Nat.add_zero,Nat.zero_add,show (0:Nat)<2 by decide,ite_true]
    have hc:=ProcPriorCodecRecordByteCells.cells I R present vid k 0 gg (5+24*k+gg) (idByte I.ids k gg)
      (if ¬present then 0 else idByte I.ids k gg) (b2n I.allowed[k]!) gb[k]! tail ht
    exact hc.2.1
  · intro i hi
    simp only [ProcPriorCodecStepRows.record,Nat.mul_zero,Nat.add_zero,Nat.zero_add,show (0:Nat)<2 by decide,ite_true]
    apply row I present R.n k gg _ _ _ _ _ _ tail ht i hi

theorem position (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (k g : Nat) (hk:k<R.n*R.n) (hg:g<8) :
    out.rows[5+24*k+8*0+g]![bpost]! =idByte I.ids k g ∧
    ∀i<8,out.rows[5+24*k+8*0+g]![prbit i]! =(bytesLE (I.ids.getD (k/R.n) 0) 8).getD (g+i) 0 := by
  apply ProcCodecGeneratedRecordPosition.property I R present vid gb fwd out h k 0 g hk (by decide) hg
    (fun a=>a[bpost]! =idByte I.ids k g ∧ ∀i<8,a[prbit i]! =(bytesLE (I.ids.getD (k/R.n) 0) 8).getD (g+i) 0)
  intro before after hs
  exact actual I R present gb fwd vid k g before after hg hs

theorem bytes_get (x g : Nat) (hg:g<8) : (bytesLE x 8).getD g 0=x/256^g%256 := by
  simp [bytesLE,List.getD_eq_getElem?_getD,hg]

end ZkFormal.NearV3.Candidates.ProcPriorCodecSenderCells
