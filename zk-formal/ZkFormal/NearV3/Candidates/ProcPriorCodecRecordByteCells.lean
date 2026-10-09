import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordByteCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash ProcPriorCodecExtra ProcPriorCodecExtraColumns
open SchedSetAll SchedSetAllRange

def columns : List Nat := [pres,bpost,bpre,vbg,kH,kR,kZ]

theorem projection (I : Input) (R : Run) (present : Bool) (vidV k f g p bpo bpr a b : Nat)
    (tail : List (Nat×Nat)) (ht : Tail tail) (c : Nat) (hc : c∈columns) :
    (recordRow I present R.n k f g p bpo bpr (instanceCells I R present vidV)
      (baseExtra R.n k f g a b++tail))[c]! =
    lookup (instanceCells I R present vidV++ProcPriorCodecRecordReads.scalars present R.n k f g p bpo bpr) c 0 := by
  have bounds : c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c) :=
    (by decide +kernel : ∀c∈columns,c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c)) c hc
  have hm : ∀v,lookup (baseExtra R.n k f g a b++tail) c v=v := by
    intro v
    apply lookup_miss
    intro q hq he
    rcases List.mem_append.mp hq with hq|hq
    · have dis : ∀c∈columns,c∉[rs,al,gb,srcC,hasC,useC] := by decide +kernel
      apply dis c hc
      simp only [baseExtra,List.mem_cons,List.mem_nil_iff,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all
    · have dis : ∀c∈columns,c∉tailColumns := by decide +kernel
      exact dis c hc (he ▸ ht q hq)
  unfold recordRow
  rw [SchedSetAll.cell _ _ c bounds.1,append,append]
  have hp : ∀v,lookup ((List.range 8).map fun i=>(pbit i,bit bpo i)) c v=v :=
    fun v=>miss_block 16 8 c v _ bounds.2.1
  have hq : ∀v,lookup ((List.range 8).map fun i=>(prbit i,(bytesLE (I.ids.getD (k/R.n) 0) 8).getD (g+i) 0)) c v=v :=
    fun v=>miss_block 79 8 c v _ bounds.2.2
  simp only [append] at hm
  split
  all_goals simp only [hq,show ∀v,lookup [] c v=v from fun _=>rfl,append,hp,hm]
  all_goals simp [ProcPriorCodecRecordReads.scalars, *]

theorem cells (I : Input) (R : Run) (present : Bool) (vidV k f g p bpo bpr a b : Nat)
    (tail : List (Nat×Nat)) (ht : Tail tail) :
    let row:=recordRow I present R.n k f g p bpo bpr (instanceCells I R present vidV)
      (baseExtra R.n k f g a b++tail)
    row[pres]! =b2n present ∧ row[bpost]! =bpo ∧ row[bpre]! =bpr ∧
    row[vbg]! =b2n present ∧ row[kH]! =0 ∧ row[kR]! =1 ∧ row[kZ]! =0 := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [projection I R present vidV k f g p bpo bpr a b tail ht _ (by simp [columns])]
  all_goals simp [lookup,instanceCells,ProcPriorCodecRecordReads.scalars,act,tau,pres,vid,nn,NN,
    base,fair,itz,zt,kR,pos,bpost,bpre,vbg,kidx,klo,khi,fS,fR,fA,Codec.g,ig7,e7,ikl,ekl,kH,kZ]
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordByteCells
