import ZkFormal.NearV3.Candidates.ProcPriorCodecPlainCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecPlainProjection
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecExtra ProcPriorCodecStepRows ProcPriorCodecPlainStep
open ProcPriorCodecRecordReads SchedSetAll SchedSetAllRange

def assignments (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (inst : List (Nat×Nat)) (k f g : Nat) : List (Nat×Nat) :=
  let bpo:=idByte I.ids k (8*f+g)
  inst++scalars present R.n k f g (5+24*k+8*f+g) bpo (if present then bpo else 0)++
    baseExtra R.n k f g (b2n I.allowed[k]!) gbA[k]!++
    (if f=0∧g=0 then startExtra R.n k else [])

theorem scalar (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (inst : List (Nat×Nat)) (k f g c : Nat) (hf:f<2) (hw:c<Codec.width)
    (hb:c<16∨24≤c) (hq:c<79∨87≤c) :
    (row I R present gbA inst k f g)[c]! = lookup (assignments I R present gbA inst k f g) c 0 := by
  have hpr (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun i=>(prbit i,values i)) c v=v :=
    miss_block 79 8 c v values hq
  have hpb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun i=>(pbit i,values i)) c v=v :=
    miss_block 16 8 c v values hb
  by_cases hf0:f=0
  all_goals unfold row record recordRow
  all_goals rw [SchedSetAll.cell _ _ _ hw]
  all_goals simp only [hf0,ite_true,ite_false,append,hpr,hpb,
    show ∀v,lookup [] c v=v from fun _=>rfl]
  all_goals cases present <;> simp [assignments,scalars,append,hf,hf0]
  all_goals simp [lookup,List.foldl_append]
end ZkFormal.NearV3.Candidates.ProcPriorCodecPlainProjection
