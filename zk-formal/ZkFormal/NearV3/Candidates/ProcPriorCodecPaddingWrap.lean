import ZkFormal.NearV3.Candidates.ProcPriorCodecPadding
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecPaddingWrap
open ZkFormal.Air ZkFormal.Algebra Lean.Grind

/-- A conservative zero test for the final padding row; next-row cells remain
unknown so the result applies to the cyclic successor, including active rows. -/
def zeroLast : Expr→Bool
  | .const n => n==0
  | .col _ nx => !nx
  | .pub _ => true
  | .isFirst => true
  | .isLast => false
  | .isTransition => true
  | .add a b => zeroLast a && zeroLast b
  | .mul a b => zeroLast a || zeroLast b
  | .neg a => zeroLast a

theorem zeroLast_sound (e : Expr) (h : zeroLast e=true) (nxt : Nat→Fp) :
    e.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)=0 := by
  induction e with
  | const n => simp [zeroLast] at h; subst n; rfl
  | col c nx => cases nx <;> simp_all [zeroLast,Expr.evalWith,ProcPriorCells.env]
  | pub i => rfl
  | isFirst => rfl
  | isLast => cases h
  | isTransition => rfl
  | add a b ia ib =>
    have hh : zeroLast a=true ∧ zeroLast b=true := by simpa [zeroLast] using h
    change a.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)+b.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)=0
    rw [ia hh.1,ib hh.2]; rfl
  | mul a b ia ib =>
    have hh : zeroLast a=true ∨ zeroLast b=true := by simpa [zeroLast] using h
    rcases hh with ha|hb
    · change a.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)*b.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)=0
      rw [ia ha,Semiring.zero_mul]
    · change a.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)*b.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)=0
      rw [ib hb,Semiring.mul_zero]
  | neg a ia =>
    change -a.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)=0
    rw [ia h]; rfl

theorem final_constraints (nxt : Nat→Fp) :
    ∀e∈ProcPriorCodecActual.constraints,
      e.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)=0 := by
  have hz : ∀e∈ProcPriorCodecActual.constraints,zeroLast e=true := by decide +kernel
  exact fun e he=>zeroLast_sound e (hz e he) nxt

theorem final_multiplicities (nxt : Nat→Fp) :
    ∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,
      e.evalWith (ProcPriorCells.env (fun _=>0) nxt 0 1 0)=0 := by
  have hz : ∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,zeroLast e=true := by decide +kernel
  exact fun i hi e he=>zeroLast_sound e (hz i hi e he) nxt
end ZkFormal.NearV3.Candidates.ProcPriorCodecPaddingWrap
