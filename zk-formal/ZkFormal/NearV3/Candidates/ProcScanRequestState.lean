import ZkFormal.NearV3.Candidates.ProcScanRequestCount
namespace ZkFormal.NearV3.Candidates.ProcScanRequestState
open NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row Scan.reqRows

def advance (R:Run)(c:CReq)(a:Acc)(rho:Nat) : Acc :=
  (a.1.push (row R c rho a.2.1 a.2.2),nextCount c rho a.2.1,nextCur R c rho a.2.2)
def state (R:Run)(c:CReq)(n:Nat) : Acc :=
  (List.range n).foldl (advance R c) (#[],0,R.base)

theorem zero (R:Run)(c:CReq) : state R c 0=(#[],0,R.base) := rfl

theorem succ (R:Run)(c:CReq)(n:Nat) :
    state R c (n+1)=advance R c (state R c n) n := by
  simp only [state,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem count (R:Run)(c:CReq)(n:Nat) :
    (state R c n).2.1=ProcScanRequestCount.before c.bm n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [succ]
    change nextCount c n (state R c n).2.1=_
    rw [ih,ProcScanRequestCount.next]

theorem size (R:Run)(c:CReq)(n:Nat) : (state R c n).1.size=n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [succ]
    change ((state R c n).1.push _).size=n+1
    rw [Array.size_push,ih]

theorem native (R:Run)(c:CReq) : Scan.reqRows R c=(state R c 20).1 := by
  rw [native_eq]
  unfold build
  have hs : step R c=(fun rho a=>pure (ForInStep.yield (advance R c a rho))) := by
    funext rho a
    exact step_eq R c rho a
  rw [hs]
  simp only [List.forIn_pure_yield_eq_foldl,Id.run]
  rfl

theorem row_at (R:Run)(c:CReq)(n rho:Nat)(h:rho<n) :
    (state R c n).1[rho]! =row R c rho
      (ProcScanRequestCount.before c.bm rho) (state R c rho).2.2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [succ]
    change ((state R c n).1.push _)[rho]! =_
    have hb : rho<((state R c n).1.push
      (row R c n (state R c n).2.1 (state R c n).2.2)).size := by
      rw [Array.size_push,size];omega
    rw [getElem!_pos ((state R c n).1.push (row R c n (state R c n).2.1 (state R c n).2.2)) rho hb,Array.getElem_push]
    by_cases he:rho=n
    · subst rho
      simp only [size,Nat.lt_irrefl,dite_false,count]
    · have hl:rho<n:=by omega
      have hs : rho<(state R c n).1.size:=by rw [size];exact hl
      rw [dif_pos hs]
      simpa only [getElem!_pos (state R c n).1 rho hs] using ih hl

theorem native_at (R:Run)(c:CReq)(rho:Nat)(h:rho<20) :
    (Scan.reqRows R c)[rho]! =row R c rho
      (ProcScanRequestCount.before c.bm rho) (state R c rho).2.2 := by
  rw [native]
  exact row_at R c 20 rho h

end ZkFormal.NearV3.Candidates.ProcScanRequestState
