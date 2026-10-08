import ZkFormal.NearV3.Candidates.ProcPriorCodecPlainStep
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecPlainCells
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecExtra ProcPriorCodecStepRows
open ProcPriorCodecPlainStep ProcPriorCodecRecordReads SchedSetAll SchedSetAllRange

def columns : List Nat := [kR,Codec.g,e7,fS,fR,fA,kidx,rend,ekl,kZ,sj,dgg]

theorem projection (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (inst : List (Nat×Nat)) (k f g c : Nat) (hf:f<2) (hc:c∈columns) :
    (row I R present gbA inst k f g)[c]! =
      lookup (inst++scalars present R.n k f g (5+24*k+8*f+g)
        (if f<2 then idByte I.ids k (8*f+g) else if g<3 then (R.segs.getD k default).vfin/256^g%256 else 0)
        (if ¬present then 0 else if f<2 then idByte I.ids k (8*f+g) else 0)) c 0 := by
  have hw:c<Codec.width := by
    have h:∀c∈columns,c<Codec.width := by decide +kernel
    exact h c hc
  have hb:(c<16∨24≤c)∧(c<79∨87≤c) := by
    have h:∀c∈columns,(c<16∨24≤c)∧(c<79∨87≤c) := by decide +kernel
    exact h c hc
  have hm:∀x∈baseExtra R.n k f g (b2n I.allowed[k]!) gbA[k]!++
      (if f=0∧g=0 then startExtra R.n k else []),x.1≠c := by
    have hn:∀c∈columns,c∉[rs,al,gb,srcC,hasC,useC,nzb,ig2,ib] := by decide +kernel
    intro x hx he
    apply hn c hc
    rw [← he]
    simp only [List.mem_append] at hx
    rcases hx with hx|hx
    · simp only [baseExtra,List.mem_cons,List.mem_nil_iff,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    · split at hx
      · simp only [startExtra,List.mem_cons,List.mem_nil_iff,or_false] at hx
        rcases hx with rfl|rfl|rfl <;> simp
      · simp at hx
  have hpr (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun i=>(prbit i,values i)) c v=v :=
    miss_block 79 8 c v values hb.2
  have hpb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun i=>(pbit i,values i)) c v=v :=
    miss_block 16 8 c v values hb.1
  unfold row record recordRow
  rw [SchedSetAll.cell _ _ _ hw,append,lookup_miss _ _ _ hm,append]
  split
  · rw [hpr,append,hpb]
    simp [scalars, *]
  · simp only [show ∀v,lookup [] c v=v from fun _=>rfl]
    rw [append,hpb]
    simp [scalars, *]
end ZkFormal.NearV3.Candidates.ProcPriorCodecPlainCells
