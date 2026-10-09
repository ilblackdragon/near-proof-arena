import ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderFlow
import ZkFormal.NearV3.Candidates.ProcPriorCodecPlainAdjacent
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderRecord
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll SchedSetAllRange
open ProcPriorCodecPlainStep ProcPriorCodecStepRows ProcPriorCodecExtra ProcPriorCodecRecordReads

theorem first_rs (I : Input) (R : Run) (present : Bool) (gbA : Array Nat) (vidV : Nat) :
    (row I R present gbA (instanceCells I R present vidV) 0 0 0)[rs]! = 1 := by
  unfold row record
  rw [projection _ _ _ _ _ _ _ _ _ _ _ rs (by decide +kernel)]
  simp [baseExtra,startExtra,lookup,rs,al,gb,srcC,hasC,useC,nzb,ig2,ib]

theorem record_position (I : Input) (present : Bool) (n k f gg p bpo bpr : Nat)
    (inst extra : List (Nat×Nat)) :
    (recordRow I present n k f gg p bpo bpr inst extra)[pos]! = lookup extra pos p := by
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ (by decide +kernel),append,append]
  have hp:∀v,lookup ((List.range 8).map fun i=>(pbit i,bit bpo i)) pos v=v :=
    fun v=>miss_block 16 8 pos v _ (by decide +kernel)
  have hq:∀v,lookup ((List.range 8).map fun i=>(prbit i,(bytesLE (I.ids.getD (k/n) 0) 8).getD (gg+i) 0)) pos v=v :=
    fun v=>miss_block 79 8 pos v _ (by decide +kernel)
  split
  all_goals simp only [hq,show ∀v,lookup [] pos v=v from fun _=>rfl,append,hp]
  all_goals congr 1
  all_goals simp [lookup,kR,pos,bpost,bpre,vbg,kidx,klo,khi,fS,fR,fA,Codec.g,ig7,e7,ikl,ekl]

theorem first_position (I : Input) (R : Run) (present : Bool) (gbA : Array Nat) (vidV : Nat) :
    (row I R present gbA (instanceCells I R present vidV) 0 0 0)[pos]! = 5 := by
  unfold row record
  rw [record_position]
  simp [baseExtra,startExtra,lookup,rs,al,gb,srcC,hasC,useC,nzb,ig2,ib,pos]

theorem first_instance (I : Input) (R : Run) (present : Bool) (gbA : Array Nat) (vidV : Nat) :
    ProcPriorCodecSideCarry.Instance I R present vidV
      (row I R present gbA (instanceCells I R present vidV) 0 0 0) := by
  intro c hc
  have hu:c∈ProcPriorCodecRegisterMiss.untouched := by
    simp only [ProcPriorCodecSideCarry.instanceColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  unfold row record
  rw [projection _ _ _ _ _ _ _ _ _ _ _ c hu]
  simp only [ProcPriorCodecSideCarry.instanceColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ProcPriorCodecSideCarry.instanceValue,scalars,baseExtra,startExtra,lookup,
    List.foldl_append,rs,al,gb,srcC,hasC,useC,nzb,ig2,ib,pos,tau,pres,vid,nn,NN,base,fair,
    kR,bpost,bpre,vbg,kidx,klo,khi,fS,fR,fA,Codec.g,ig7,e7,ikl,ekl]

end ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderRecord
