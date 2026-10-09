import ZkFormal.NearV3.Candidates.ProcDistShardBools
namespace ZkFormal.NearV3.Candidates.ProcDistCellRow
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcDistGeneratorFactor
open Dist NearSpecV3.Scheduler

def quot (allowed:Bool)(count left:Nat) := if allowed then left/count else 0
def remn (allowed:Bool)(count left:Nat) := if allowed then left%count else 0
def grant (allowed:Bool)(n1 l1 n2 l2:Nat) :=
  if allowed then min (l1/n1) (l2/n2) else 0

def core (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool) : List (Nat×Nat) :=
  let link:=sv*n+rr
  let q1v:=quot allowed n1 l1
  let q2v:=quot allowed n2 l2
  let gbv:=grant allowed n1 l1 n2 l2
  let e1v:=if j+1=n then 1 else 0
  let e2v:=if i+1=n then 1 else 0
  [(act,1),(kC,1),(tau,tv),(nn,n),(a,i),(b,j),(s,sv),(r,rr),
    (N1,n1),(L1,l1),(N2,n2),(L2,l2),(q1,q1v),(r1,remn allowed n1 l1),
    (q2,q2v),(r2,remn allowed n2 l2),(llo,link%256),(lhi,link/256),
    (al,b2n allowed),(alc,b2n allowed),
    (side,(srcFields ids link)[0]!),(shd,(srcFields ids link)[1]!),
    (lnk,(srcFields ids link)[2]!),(by0,(srcFields ids link)[3]!),
    (gb,gbv),(cx,q1v),(cy,q2v),(cb,if allowed && q2v≤q1v then 1 else 0),
    (cg,b2n allowed),(da,i+1),(db,j),(sL,l2-gbv),(dlsg,1-e2v),(dlrg,1),
    (e1,e1v),(ig1,finv (fsub j (n-1))),(e2,e2v),(ig2,finv (fsub i (n-1))),
    (eI,e1v*e2v)]

def row (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool) : Array Nat :=
  Gen.setAll width (core ids tv n i j sv rr n1 l1 n2 l2 allowed ++
    (if allowed then bitsOf bt1 (n1-1-remn allowed n1 l1) ++bitsOf bt2 (n2-1-remn allowed n2 l2) else []) ++
    bitsN qb1 23 (quot allowed n1 l1) ++bitsN qb2 23 (quot allowed n2 l2) ++
    bitsN rb1 6 (remn allowed n1 l1) ++bitsN rb2 6 (remn allowed n2 l2))

theorem emitted (I:Input)(R:Run)(i j:Nat)(acc out:CellAcc)
    (h:cellStep I R i j acc=.ok (.yield out)) :
    out.1=acc.1.push (row I.ids R.tau R.n i j
      (ProcDistCellBridge.sender I R i) (ProcDistCellBridge.receiver I R j)
      acc.2.2.2.2.1 acc.2.2.2.2.2
      (acc.2.2.2.1[ProcDistCellBridge.receiver I R j]!).1
      (acc.2.2.2.1[ProcDistCellBridge.receiver I R j]!).2
      I.allowed[ProcDistCellBridge.sender I R i*R.n+ProcDistCellBridge.receiver I R j]!) := by
  by_cases hal:I.allowed[ProcDistCellBridge.sender I R i*R.n+ProcDistCellBridge.receiver I R j]! =true
  all_goals
    unfold cellStep at h
    dsimp only at h
    dsimp only [ProcDistCellBridge.sender,ProcDistCellBridge.receiver] at hal
    simp only [hal,Bool.false_eq_true,ite_true,ite_false] at h
  · simp only [bind,Except.bind] at h
    split at h
    · cases h
    · simp only [pure,Except.pure,Except.ok.injEq,ForInStep.yield.injEq] at h
      subst out
      simp only [row,core,quot,remn,grant,ProcDistCellBridge.sender,ProcDistCellBridge.receiver,
        hal,ite_true,Bool.true_and]
  · cases h
    have hf:I.allowed[ProcDistCellBridge.sender I R i*R.n+ProcDistCellBridge.receiver I R j]! =false := by
      simpa only [ProcDistCellBridge.sender,ProcDistCellBridge.receiver] using Bool.eq_false_iff.mpr hal
    dsimp only [ProcDistCellBridge.sender,ProcDistCellBridge.receiver] at hf
    simp only [row,core,quot,remn,grant,ProcDistCellBridge.sender,ProcDistCellBridge.receiver,
      hf,hal,ite_false,Bool.false_and,Bool.false_eq_true]
end ZkFormal.NearV3.Candidates.ProcDistCellRow
