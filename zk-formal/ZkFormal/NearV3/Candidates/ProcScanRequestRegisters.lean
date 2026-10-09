import ZkFormal.NearV3.Candidates.ProcScanRequestByteCells
import ZkFormal.NearV3.Candidates.ProcScanByteTransition
namespace ZkFormal.NearV3.Candidates.ProcScanRequestRegisters
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row

theorem mapped (bm:List UInt8)(j:Nat) :
    (bm.map (·.toNat)).getD j 0=(bm.getD j 0).toNat := by
  simp only [List.getD,List.getElem?_map]
  cases bm[j]? <;> rfl

theorem cell (R:Run)(c:CReq)(rho jj cv i:Nat)(hi:i<5) :
    (row R c rho jj cv)[Scan.q i]! =ProcScanByteTransition.reg c.bm rho i := by
  by_cases h:i=0
  · subst i
    rw [ProcScanRequestByteCells.first_byte,mapped]
    rfl
  · rw [ProcScanRequestByteCells.following_bytes R c rho jj cv i (by omega),mapped]
    simp [ProcScanByteTransition.reg,h]

theorem rotates (R:Run)(c:CReq)(rho jj cv jn cn i:Nat)(hi:i<4)(hu:rho%4=3) :
    (row R c (rho+1) jn cn)[Scan.q i]! =(row R c rho jj cv)[Scan.q (i+1)]! := by
  rw [cell R c (rho+1) jn cn i (by omega),cell R c rho jj cv (i+1) (by omega)]
  exact ProcScanByteTransition.rotates c.bm rho i hu

theorem stays (R:Run)(c:CReq)(rho jj cv jn cn i:Nat)(hi:1≤i ∧i<5)(hu:rho%4≠3) :
    (row R c (rho+1) jn cn)[Scan.q i]! =(row R c rho jj cv)[Scan.q i]! := by
  rw [cell R c (rho+1) jn cn i hi.2,cell R c rho jj cv i hi.2]
  exact ProcScanByteTransition.stays c.bm rho i hi.1 hu
end ZkFormal.NearV3.Candidates.ProcScanRequestRegisters
