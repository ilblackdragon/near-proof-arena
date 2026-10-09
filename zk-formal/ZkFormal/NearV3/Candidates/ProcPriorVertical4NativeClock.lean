import ZkFormal.NearV3.Candidates.ProcPriorVertical4ClockTrace
import ZkFormal.NearV3.Candidates.ProcPriorFourStageBudget
namespace ZkFormal.NearV3.Candidates.ProcPriorVertical4NativeClock
open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.Bandwidth
open ProcPriorBudget ProcPriorFourStageBudget

def cutMemory (xs : List Input) : Nat:=writeRows xs+1
def cutIds (xs : List Input) : Nat:=cutMemory xs+idRows xs+1
def cutRaw (xs : List Input) : Nat:=cutIds xs+byteRows xs+1

theorem cuts (xs : List Input) (h:∀x∈xs,Valid x) (hk:xs.length≤33) (hb:byteRows xs≤2000000) :
    0<cutMemory xs ∧ cutMemory xs<cutIds xs ∧ cutIds xs<cutRaw xs ∧
    cutRaw xs<2^22 ∧ joinRows xs+1<2^22-cutRaw xs := by
  have hc:=(capacity xs h hk hb).2
  unfold cutRaw cutIds cutMemory
  omega

/-- A concrete log22 clock for the four actual native row inventories. The
record stage absorbs all remaining padding. The input inventory/source-byte
binding remains explicit, and this theorem only installs the window clock. -/
def trace (xs : List Input) (data : Nat→Nat→Fp) : Trace Fp:=
  ProcPriorVertical4ClockTrace.trace (cutMemory xs) (cutIds xs) (cutRaw xs) data

theorem constraints (xs : List Input) (h:∀x∈xs,Valid x) (hk:xs.length≤33) (hb:byteRows xs≤2000000)
    (data : Nat→Nat→Fp) (tt j : Nat) (hj:j<2^22) (pub : List Fp) :
    ∀e∈ProcPriorVertical4Linear.windows,e.eval (trace xs data) tt j pub=0 := by
  obtain ⟨ha,hab,hbc,hcn,_⟩:=cuts xs h hk hb
  exact ProcPriorVertical4ClockTrace.constraints _ _ _ ha hab hbc hcn data tt j hj pub
end ZkFormal.NearV3.Candidates.ProcPriorVertical4NativeClock
