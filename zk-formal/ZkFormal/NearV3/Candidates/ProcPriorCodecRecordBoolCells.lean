import ZkFormal.NearV3.Candidates.ProcPriorCodecSideKind
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBoolCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecRecordReads ProcPriorCodecNativeHash
open SchedSetAll SchedSetAllRange

def columns : List Nat := ProcPriorCodecSideKind.scalarBits++recBoolCols
def Gates (xs : List (Nat×Nat)) : Prop := ∀p∈xs,p.1∈columns→p.2≤1

theorem append (a b : List (Nat×Nat)) (ha : Gates a) (hb : Gates b) : Gates (a++b) := by
  intro p hp hc
  rcases List.mem_append.mp hp with hp|hp
  · exact ha p hp hc
  · exact hb p hp hc

theorem lookup_bound (xs : List (Nat×Nat)) (c v : Nat) (hc : c∈columns)
    (hv : v≤1) (h : Gates xs) : lookup xs c v≤1 := by
  induction xs generalizing v with
  | nil => exact hv
  | cons p ps ih =>
    change lookup ps c (if p.1=c then p.2 else v)≤1
    apply ih
    · split
      · exact h p (by simp) (by simp_all)
      · exact hv
    · intro q hq hqc; exact h q (by simp [hq]) hqc

theorem row (I : Input) (R : Run) (present : Bool) (vid k f g p bpo bpr : Nat)
    (extra : List (Nat×Nat)) (he : Gates extra) (c : Nat) (hc : c∈columns) :
    (recordRow I present R.n k f g p bpo bpr (instanceCells I R present vid) extra)[c]! ≤1 := by
  have bounds : c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c) := by
    have h : ∀c∈columns,c<Codec.width ∧ (c<16∨24≤c) ∧ (c<79∨87≤c) := by decide +kernel
    exact h c hc
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ bounds.1,SchedSetAll.append,SchedSetAll.append]
  apply lookup_bound _ c _ hc _ he
  have hp : ∀v,lookup ((List.range 8).map fun i=>(pbit i,bit bpo i)) c v=v :=
    fun v=>miss_block 16 8 c v (fun i=>bit bpo i) bounds.2.1
  have hq : ∀v,lookup ((List.range 8).map fun i=>(prbit i,(bytesLE (I.ids.getD (k/R.n) 0) 8).getD (g+i) 0)) c v=v :=
    fun v=>miss_block 79 8 c v _ bounds.2.2
  split
  all_goals simp only [hq,show ∀v,lookup [] c v=v from fun _=>rfl,SchedSetAll.append,hp]
  all_goals simp only [columns,ProcPriorCodecSideKind.scalarBits,recBoolCols,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hc
  all_goals rcases hc with hc|hc
  all_goals first
    | (rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    | (rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl)
  all_goals simp [lookup,instanceCells,List.foldl_append,fwg,rend,cg,rs,nzb,fA,e2,
    act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kR,pos,bpost,bpre,vbg,kidx,klo,khi,
    fS,fR,Codec.g,ig7,e7,ikl,ekl,kH,kZ,kA,kF,ehp,esj,cbit,dgg,lowf,al,cb,bF,hasC,bigR]
  all_goals repeat first | split | omega
  all_goals cases present <;> simp [b2n]
theorem post_bit (I : Input) (present : Bool) (n k f gg p bpo bpr : Nat)
    (inst extra : List (Nat×Nat)) (i : Nat) (hi:i<8)
    (he:∀x∈extra,x.1≠pbit i) :
    (recordRow I present n k f gg p bpo bpr inst extra)[pbit i]! = bit bpo i := by
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ (by unfold pbit Codec.width; omega),SchedSetAll.append,lookup_miss _ _ _ he,SchedSetAll.append]
  have hq:∀v,lookup ((List.range 8).map fun j=>(prbit j,(bytesLE (I.ids.getD (k/n) 0) 8).getD (gg+j) 0)) (pbit i) v=v :=
    fun v=>miss_block 79 8 (pbit i) v _ (by left; unfold pbit; omega)
  have hp:∀v,lookup ((List.range 8).map fun j=>(pbit j,bit bpo j)) (pbit i) v=bit bpo i := by
    intro v
    have hh:=lookup_block 16 8 (fun j=>bit bpo j) (pbit i) v
    simpa [SchedSetAllRange.block,pbit,show 16+i<24 by omega] using hh
  split
  all_goals simp only [hq,show ∀v,lookup [] (pbit i) v=v from fun _=>rfl,SchedSetAll.append,hp]

theorem actual_post_bits (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f gg : Nat) (s out : ProcPriorCodecRecordStep.State)
    (hf:f<3) (hg:gg<8)
    (h:ProcPriorCodecRecordStep.step I R present gbA fwd inst k f gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ ∀i,i<8→a[pbit i]!≤1 := by
  obtain ⟨tail,ht,ha⟩:=ProcPriorCodecStepRows.successful_row I R present gbA fwd inst k f gg s out hf hg h
  refine ⟨_,ha,?_⟩
  intro i hi
  unfold ProcPriorCodecStepRows.record
  rw [post_bit _ _ _ _ _ _ _ _ _ _ _ i hi]
  · have hb (x : Nat) : bit x i≤1 := by
      have hh:=ProcPriorCodecSideKind.native_bit x i
      omega
    exact hb _
  · intro x hx heq
    have hm:∀c∈[rs,al,gb,srcC,hasC,useC]++ProcPriorCodecExtraColumns.tailColumns,
        ∀i:Fin 8,c≠pbit i.val := by decide +kernel
    apply hm x.1 _ ⟨i,hi⟩ heq
    rcases List.mem_append.mp hx with hx|hx
    · simp only [ProcPriorCodecExtra.baseExtra,List.mem_cons,List.mem_nil_iff,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    · exact List.mem_append_right _ (ht x hx)

end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBoolCells
