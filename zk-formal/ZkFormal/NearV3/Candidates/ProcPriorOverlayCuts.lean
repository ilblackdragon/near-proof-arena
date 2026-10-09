import ZkFormal.NearV3.Candidates.ProcPriorOverlayBudget
import ZkFormal.NearV3.Candidates.ProcPriorVertical4DataEval
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayCuts
open ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Assembly.CodecDigest

def cutMemory (bs : List NativeBlock) : Nat :=(ProcPriorNativeMemory.allRows bs).length+1
def cutIds (bs : List NativeBlock) : Nat :=cutMemory bs+(ProcPriorOverlayBudget.idRows bs).length+1
def cutRaw (bs : List NativeBlock) : Nat :=cutIds bs+(ProcRawConcatGeometry.rows bs).length+1

theorem cuts (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184) :
    0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧ cutIds bs<cutRaw bs ∧
    cutRaw bs<2^22 ∧
    (ProcRecordConcatTraffic.rows (fun b=>b.pub.ids) bs).length+1<2^22-cutRaw bs := by
  have hc:=(ProcPriorOverlayBudget.capacity bs hn hlen hraw).2
  unfold ProcPriorOverlayBudget.occupied at hc
  unfold cutRaw cutIds cutMemory
  omega

/-- The data source for each selected component is read at its actual local
row position; the final Record stage absorbs the unused physical rows. -/
def data (bs : List NativeBlock) (component : Nat→Nat→Nat→Fp) (j : Nat) : Nat→Fp :=
  if j<cutMemory bs then component 0 j
  else if j<cutIds bs then component 1 (j-cutMemory bs)
  else if j<cutRaw bs then component 2 (j-cutIds bs)
  else component 3 (j-cutRaw bs)
def trace (bs : List NativeBlock) (component : Nat→Nat→Nat→Fp) : Trace Fp :=
  ProcPriorVertical4ClockTrace.trace (cutMemory bs) (cutIds bs) (cutRaw bs) (data bs component)

theorem windows (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (component : Nat→Nat→Nat→Fp) (t j : Nat) (hj:j<2^22) (pub : List Fp) :
    ∀e∈ProcPriorVertical4Linear.windows,e.eval (trace bs component) t j pub=0 := by
  obtain ⟨ha,hab,hbc,hc,_⟩:=cuts bs hn hlen hraw
  exact ProcPriorVertical4ClockTrace.constraints _ _ _ ha hab hbc hc _ t j hj pub
end ZkFormal.NearV3.Candidates.ProcPriorOverlayCuts
