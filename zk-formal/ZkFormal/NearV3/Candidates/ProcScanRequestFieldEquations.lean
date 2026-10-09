import ZkFormal.NearV3.Candidates.ProcScanRequestState
import ZkFormal.NearV3.Candidates.ProcScanRequestCells
namespace ZkFormal.NearV3.Candidates.ProcScanRequestFieldEquations
open NearSpecV3.Scheduler ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row Scan.reqRows

def cell (R:Run)(c:CReq)(rho jj cv col:Nat) : Fp := Fp.ofNat (row R c rho jj cv)[col]!

theorem intermediate (R:Run)(c:CReq)(rho jj cv:Nat) :
    cell R c rho jj cv Scan.cm =
      cell R c rho jj cv Scan.b0 * (cell R c rho jj cv Scan.base+cell R c rho jj cv Scan.Q0)+
      (1-cell R c rho jj cv Scan.b0)*cell R c rho jj cv Scan.cur := by
  have hc:=ProcScanRequestCells.controls R c rho jj cv
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  have hq:=ProcScanRequestCells.quotients R c rho jj cv
  simp only [cell,hp.2.2.1,hp.2.2.2.1,hp.2.1,hc.2.2.2.2.2.1,hq.1]
  cases getBit c.bm (pos rho) <;> simp only [b2n,ite_true,ite_false]
  all_goals try simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals try simp [ofNat_add']
  all_goals try simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals clear hc hp hq
  all_goals try clear hn
  all_goals grind

theorem current_next (R:Run)(c:CReq)(rho jj cv:Nat) :
    cell R c (rho+1) (nextCount c rho jj) (nextCur R c rho cv) Scan.cur =
      cell R c rho jj cv Scan.b1*(cell R c rho jj cv Scan.base+cell R c rho jj cv Scan.Q1)+
      (1-cell R c rho jj cv Scan.b1)*cell R c rho jj cv Scan.cm := by
  have hc:=ProcScanRequestCells.controls R c rho jj cv
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  have hn:=ProcScanRequestCells.progress R c (rho+1) (nextCount c rho jj) (nextCur R c rho cv)
  have hq:=ProcScanRequestCells.quotients R c rho jj cv
  simp only [cell]
  rw [hn.2.1]
  simp only [hp.2.2.1,hp.2.2.2.2.1,hc.2.2.2.2.2.1,hq.2.1,nextCur]
  cases getBit c.bm (pos rho+1) <;> simp only [b2n,ite_true,ite_false]
  all_goals try simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals try simp [ofNat_add']
  all_goals try simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals clear hc hp hq
  all_goals try clear hn
  all_goals grind

theorem count_next (R:Run)(c:CReq)(rho jj cv:Nat) :
    cell R c (rho+1) (nextCount c rho jj) (nextCur R c rho cv) Scan.j =
      cell R c rho jj cv Scan.j+cell R c rho jj cv Scan.b0+cell R c rho jj cv Scan.b1 := by
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  have hn:=ProcScanRequestCells.progress R c (rho+1) (nextCount c rho jj) (nextCur R c rho cv)
  simp only [cell]
  rw [hn.1]
  simp only [hp.1,hp.2.2.2.1,hp.2.2.2.2.1,nextCount,ofNat_add']

theorem constants (R:Run)(c:CReq)(rho jj cv rn jn cn col:Nat)(hc:col∈Scan.reqCols) :
    cell R c rn jn cn col=cell R c rho jj cv col := by
  have ha:=ProcScanRequestCells.controls R c rho jj cv
  have hb:=ProcScanRequestCells.controls R c rn jn cn
  have hp:=ProcScanRequestCells.payload R c rho jj cv
  have hq:=ProcScanRequestCells.payload R c rn jn cn
  simp only [Scan.reqCols,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [cell]
  all_goals grind only

theorem native_current_next (R:Run)(c:CReq)(rho:Nat)(hr:rho+1<20) :
    Fp.ofNat (Scan.reqRows R c)[rho+1]![Scan.cur]! =
      Fp.ofNat (Scan.reqRows R c)[rho]![Scan.b1]! *
        (Fp.ofNat (Scan.reqRows R c)[rho]![Scan.base]!+Fp.ofNat (Scan.reqRows R c)[rho]![Scan.Q1]!) +
      (1-Fp.ofNat (Scan.reqRows R c)[rho]![Scan.b1]!)*Fp.ofNat (Scan.reqRows R c)[rho]![Scan.cm]! := by
  rw [ProcScanRequestState.native_at R c (rho+1) hr,
    ProcScanRequestState.native_at R c rho (by omega)]
  have hcount:=ProcScanRequestCount.next c rho
  have hstate:=ProcScanRequestState.succ R c rho
  have hcur:(ProcScanRequestState.state R c (rho+1)).2.2=
      nextCur R c rho (ProcScanRequestState.state R c rho).2.2 := by rw [hstate];rfl
  rw [hcur,←hcount]
  exact current_next R c rho _ _

theorem native_count_next (R:Run)(c:CReq)(rho:Nat)(hr:rho+1<20) :
    Fp.ofNat (Scan.reqRows R c)[rho+1]![Scan.j]! =
      Fp.ofNat (Scan.reqRows R c)[rho]![Scan.j]!+
      Fp.ofNat (Scan.reqRows R c)[rho]![Scan.b0]!+Fp.ofNat (Scan.reqRows R c)[rho]![Scan.b1]! := by
  rw [ProcScanRequestState.native_at R c (rho+1) hr,
    ProcScanRequestState.native_at R c rho (by omega)]
  have hcount:=ProcScanRequestCount.next c rho
  have hstate:=ProcScanRequestState.succ R c rho
  have hcur:(ProcScanRequestState.state R c (rho+1)).2.2=
      nextCur R c rho (ProcScanRequestState.state R c rho).2.2 := by rw [hstate];rfl
  rw [hcur,←hcount]
  exact count_next R c rho _ _

theorem terminal_count (R:Run)(c:CReq)(hbits:c.bits=setBits c.bm) :
    Fp.ofNat (Scan.reqRows R c)[19]![Scan.m]! =
      Fp.ofNat (Scan.reqRows R c)[19]![Scan.j]!+
      Fp.ofNat (Scan.reqRows R c)[19]![Scan.b0]!+Fp.ofNat (Scan.reqRows R c)[19]![Scan.b1]! := by
  rw [ProcScanRequestState.native_at R c 19 (by decide)]
  have hp:=ProcScanRequestCells.progress R c 19 (ProcScanRequestCount.before c.bm 19)
    (ProcScanRequestState.state R c 19).2.2
  have hv:=ProcScanRequestCells.payload R c 19 (ProcScanRequestCount.before c.bm 19)
    (ProcScanRequestState.state R c 19).2.2
  rw [hv.2.2.2.2.1,hp.1,hp.2.2.2.1,hp.2.2.2.2.1,ofNat_add',ofNat_add']
  exact congrArg Fp.ofNat (ProcScanRequestCount.finish c hbits).symm

end ZkFormal.NearV3.Candidates.ProcScanRequestFieldEquations
