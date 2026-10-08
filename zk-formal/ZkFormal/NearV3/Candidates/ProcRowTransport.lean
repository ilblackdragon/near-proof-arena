import ZkFormal.NearV3.Candidates.ProcBoundaryRepair
namespace ZkFormal.NearV3.Candidates.ProcRowTransport
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched

def noClock : Expr→Bool
  | .isFirst | .isLast | .isTransition => false
  | .add a b | .mul a b => noClock a && noClock b
  | .neg a => noClock a
  | _ => true

theorem eval_transport (e : Expr) (he : noClock e=true)
    (tr ts : Trace Fp) (t u r s : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=ts.cell u s c)
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=ts.cell u ((s+1)%ts.height u) c) :
    e.eval tr t r pub=e.eval ts u s pub := by
  induction e with
  | const => rfl
  | col c nx => cases nx <;> first | exact hc c | exact hn c
  | pub => rfl
  | isFirst | isLast | isTransition => simp [noClock] at he
  | add a b ia ib =>
    have h : noClock a=true ∧ noClock b=true := by simpa only [noClock,Bool.and_eq_true] using he
    change a.eval tr t r pub+b.eval tr t r pub=a.eval ts u s pub+b.eval ts u s pub
    rw [ia h.1,ib h.2]
  | mul a b ia ib =>
    have h : noClock a=true ∧ noClock b=true := by simpa only [noClock,Bool.and_eq_true] using he
    change a.eval tr t r pub*b.eval tr t r pub=a.eval ts u s pub*b.eval ts u s pub
    rw [ia h.1,ib h.2]
  | neg a ia => exact congrArg Neg.neg (ia he)

theorem groups_noClock :
    (ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt).all noClock=true := by decide +kernel

theorem groups_transport (tr ts : Trace Fp) (t u r s : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=ts.cell u s c)
    (hn : ∀ c,tr.cell t ((r+1)%tr.height t) c=ts.cell u ((s+1)%ts.height u) c)
    (h : ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval ts u s pub=0) :
    ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval tr t r pub=0 := by
  intro e he
  rw [eval_transport e (List.all_eq_true.1 groups_noClock e he) tr ts t u r s pub hc hn]
  exact h e he
end ZkFormal.NearV3.Candidates.ProcRowTransport
