import ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic
namespace ZkFormal.NearV3.Candidates.ProcScanRequestCount
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor

/-- Number of consumed bitmap bits before the indicated two-bit row. -/
def before (bm:List UInt8)(rho:Nat) : Nat :=
  ((List.range (2*rho)).filter (getBit bm)).length

theorem zero (bm:List UInt8) : before bm 0=0 := by simp [before]

theorem next (c:CReq)(rho:Nat) :
    nextCount c rho (before c.bm rho)=before c.bm (rho+1) := by
  have hp:=ProcScanRequestArithmetic.position rho
  have h:2*(rho+1)=2*rho+1+1:=by omega
  simp only [before,h,List.range_succ,List.filter_append,List.length_append,
    List.filter_cons,List.filter_nil,List.length_cons,List.length_nil,nextCount,hp,b2n]
  split <;> split <;> simp_all <;> omega

theorem finish (c:CReq)(hbits:c.bits=setBits c.bm) :
    nextCount c 19 (before c.bm 19)=c.bits.length := by
  rw [next,hbits]
  rfl

end ZkFormal.NearV3.Candidates.ProcScanRequestCount
