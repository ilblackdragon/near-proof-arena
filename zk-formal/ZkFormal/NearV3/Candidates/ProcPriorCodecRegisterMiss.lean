import ZkFormal.NearV3.Candidates.SchedSetAllRange
import ZkFormal.NearV3.Candidates.ProcPriorCodecAssignments
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRegisterMiss
open ZkFormal.NearV3.Sched.Codec SchedSetAll SchedSetAllRange

/-- Columns outside both overlaid digest registers and the two byte-bit blocks. -/
def untouched : List Nat :=
  [act,tau,pres,vid,nn,NN,base,fair,kH,kR,kZ,kA,kF,rs,ehp,rend,fS,fR,fA,bpost,bpre]

theorem reg_avoids (c i : Nat) (hc:c∈untouched) (hi:i<32) : reg i≠c := by
  have h : ∀i:Fin 32,∀c∈untouched,reg i.val≠c := by decide +kernel
  exact h ⟨i,hi⟩ c hc

theorem bits_avoid (c : Nat) (hc:c∈untouched) :
    (c<16 ∨ 24≤c) ∧ (c<79 ∨ 87≤c) := by
  have h : ∀c∈untouched,(c<16 ∨ 24≤c) ∧ (c<79 ∨ 87≤c) := by decide +kernel
  exact h c hc

theorem registers (c v : Nat) (values : Nat→Nat) (hc:c∈untouched) :
    lookup ((List.range 32).map fun i=>(reg i,values i)) c v=v := by
  apply lookup_miss
  intro p hp
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hp
  exact reg_avoids c i hc (List.mem_range.mp hi)

theorem post_bits (c v : Nat) (values : Nat→Nat) (hc:c∈untouched) :
    lookup ((List.range 8).map fun i=>(pbit i,values i)) c v=v := by
  exact miss_block 16 8 c v values (bits_avoid c hc).1

theorem prior_bits (c v : Nat) (values : Nat→Nat) (hc:c∈untouched) :
    lookup ((List.range 8).map fun i=>(prbit i,values i)) c v=v := by
  exact miss_block 79 8 c v values (bits_avoid c hc).2

end ZkFormal.NearV3.Candidates.ProcPriorCodecRegisterMiss
