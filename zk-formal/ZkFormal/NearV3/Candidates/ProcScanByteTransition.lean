import ZkFormal.NearV3.Candidates.ProcScanBitmapArithmetic
namespace ZkFormal.NearV3.Candidates.ProcScanByteTransition
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def reg (bm:List UInt8)(rho i:Nat) : Nat :=
  if i=0 then (bm.getD (rho/4) 0).toNat/4^(rho%4)
  else (bm.getD (rho/4+i) 0).toNat

theorem stays (bm:List UInt8)(rho i:Nat)(hi:0<i)(hu:rho%4≠3) :
    reg bm (rho+1) i=reg bm rho i := by
  have hy:(rho+1)/4=rho/4:=by omega
  simp [reg,show i≠0 by omega,hy]

theorem rotates (bm:List UInt8)(rho i:Nat)(hu:rho%4=3) :
    reg bm (rho+1) i=reg bm rho (i+1) := by
  have hy:(rho+1)/4=rho/4+1:=by omega
  have hn:(rho+1)%4=0:=by omega
  simp only [reg,hy,hn]
  by_cases hi:i=0
  · subst i;simp
  · simp [hi,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem exhausted (bm:List UInt8)(rho:Nat)(hu:rho%4=3) :
    reg bm rho 0=b2n (getBit bm (2*rho))+2*b2n (getBit bm (2*rho+1)) := by
  have hp:=ProcScanRequestArithmetic.position rho
  unfold ProcScanRequestFactor.pos at hp
  have hb:=ProcScanBitmapArithmetic.native_pair bm rho
  have he:8*(rho/4)+6=2*rho:=by omega
  simpa [reg,hu,ProcScanRequestFactor.pos,he] using hb

theorem consumes (bm:List UInt8)(rho:Nat)(hu:rho%4≠3) :
    reg bm rho 0=b2n (getBit bm (2*rho))+2*b2n (getBit bm (2*rho+1))+
      4*reg bm (rho+1) 0 := by
  have hp:=ProcScanRequestArithmetic.position rho
  unfold ProcScanRequestFactor.pos at hp
  have hb:=ProcScanBitmapArithmetic.native_pair bm rho
  have hy:(rho+1)/4=rho/4:=by omega
  have hn:(rho+1)%4=rho%4+1:=by omega
  simpa only [reg,ite_true,hy,hn,ProcScanRequestFactor.pos,hp,
    if_neg hu] using hb

end ZkFormal.NearV3.Candidates.ProcScanByteTransition
