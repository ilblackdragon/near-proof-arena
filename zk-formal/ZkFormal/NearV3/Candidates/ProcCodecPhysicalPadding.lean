import ZkFormal.NearV3.Candidates.ProcPriorCodecPaddingWrap
import ZkFormal.NearV3.Assembly.SchedulerCodecTraceDigests
namespace ZkFormal.NearV3.Candidates.ProcCodecPhysicalPadding
open ZkFormal.NearV3.Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Complete

def cells (rows : Array (Array Nat)) (r : Nat) : Nat→Fp :=
  fun c=>Fp.ofNat (natCell rows codecPad r c)

theorem padding_cells (rows : Array (Array Nat)) (r : Nat) (hr : rows.size≤r) :
    cells rows r=(fun _=>0) := by
  funext c
  unfold cells natCell
  rw [natRow_ge _ _ hr]
  simp [codecPad,gd_zrow]
  rfl

theorem without_public (e : Expr) (h : e.pubBound=0) (env : Env Fp) (p : Nat→Fp) :
    e.evalWith {env with pub:=p}=e.evalWith env := by
  induction e with
  | const n => rfl
  | col c nx => rfl
  | pub i => simp [Expr.pubBound] at h
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl
  | add a b ia ib =>
    have hh : a.pubBound=0 ∧ b.pubBound=0 := by simpa [Expr.pubBound] using h
    simp only [Expr.evalWith,ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : a.pubBound=0 ∧ b.pubBound=0 := by simpa [Expr.pubBound] using h
    simp only [Expr.evalWith,ia hh.1,ib hh.2]
  | neg a ia => exact congrArg env.neg (ia h)

theorem physical_eval (rows : Array (Array Nat)) (t r : Nat) (hr : r<2^22)
    (pub : List Fp) (e : Expr) (he : e.pubBound=0) :
    e.eval (SchedHeight.trace rows codecPad) t r pub=
      e.evalWith (ProcPriorCells.env (cells rows r) (cells rows ((r+1)%(2^22)))
        (if r=0 then 1 else 0) (if r+1=2^22 then 1 else 0) (if r+1<2^22 then 1 else 0)) := by
  unfold Expr.eval
  have henv : rowEnv (SchedHeight.trace rows codecPad) t r pub=
      {ProcPriorCells.env (cells rows r) (cells rows ((r+1)%(2^22)))
        (if r=0 then 1 else 0) (if r+1=2^22 then 1 else 0) (if r+1<2^22 then 1 else 0)
        with pub:=fun i=>pub.getD i 0} := by
    by_cases hl : r+1=2^22
    · have ht : ¬r+1<2^22 := by omega
      simp only [rowEnv,SchedHeight.trace,Trace.height,ProcPriorCells.env,cells,hl,ht,Nat.lt_irrefl,ite_true,ite_false]
      congr 1
      funext c nx
      cases nx <;> rfl
    · have ht : r+1<2^22 := by omega
      simp only [rowEnv,SchedHeight.trace,Trace.height,ProcPriorCells.env,cells,hl,ht,Nat.lt_irrefl,ite_true,ite_false]
      congr 1
      funext c nx
      cases nx <;> rfl
  rw [henv]
  exact without_public e he _ _

/-- All physical padding rows at common log22 satisfy the corrected equations
and multiplicity bits, including the last row's cyclic edge to the active prefix. -/
theorem local_padding (rows : Array (Array Nat)) (hne : 0<rows.size)
    (r : Nat) (hr : rows.size≤r) (hlt : r<2^22) :
    let env := ProcPriorCells.env (cells rows r) (cells rows ((r+1)%(2^22)))
      (if r=0 then 1 else 0) (if r+1=2^22 then 1 else 0) (if r+1<2^22 then 1 else 0)
    (∀e∈ProcPriorCodecActual.constraints,e.evalWith env=0) ∧
      (∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,e.evalWith env=0) := by
  have hr0 : r≠0 := by omega
  dsimp only
  rw [padding_cells rows r hr]
  simp only [if_neg hr0]
  by_cases he : r+1=2^22
  · have ht : ¬r+1<2^22 := by omega
    simp only [if_pos he,if_neg ht]
    exact ⟨ProcPriorCodecPaddingWrap.final_constraints _,ProcPriorCodecPaddingWrap.final_multiplicities _⟩
  · have ht : r+1<2^22 := by omega
    rw [Nat.mod_eq_of_lt ht,padding_cells rows (r+1) (by omega)]
    simp only [if_neg he,if_pos ht]
    exact ⟨ProcPriorCodecPadding.zero_constraints,ProcPriorCodecPadding.zero_multiplicities⟩
/-- Actual AIR evaluation, for arbitrary public inputs, on every padded row. -/
theorem physical_local (rows : Array (Array Nat)) (hne : 0<rows.size)
    (t r : Nat) (hr : rows.size≤r) (hlt : r<2^22) (pub : List Fp) :
    (∀e∈ProcPriorCodecActual.table.constraints,e.eval (SchedHeight.trace rows codecPad) t r pub=0) ∧
      (∀i∈ProcPriorCodecActual.table.interactions,∀e∈i.mult,
        e.eval (SchedHeight.trace rows codecPad) t r pub=0 ∨
        e.eval (SchedHeight.trace rows codecPad) t r pub=1) := by
  have hc : ∀e∈ProcPriorCodecActual.constraints,e.pubBound=0 := by decide +kernel
  have hm : ∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,e.pubBound=0 := by decide +kernel
  have hl := local_padding rows hne r hr hlt
  constructor
  · intro e he
    rw [physical_eval rows t r hlt pub e (hc e he)]
    exact hl.1 e he
  · intro i hi e he
    left
    rw [physical_eval rows t r hlt pub e (hm i hi e he)]
    exact hl.2 i hi e he
/-- Reduce full physical table legality to generated active rows. All padding
obligations, including the cyclic successor, are discharged here. -/
theorem of_active (rows : Array (Array Nat)) (hne : 0<rows.size) (hcap : rows.size≤2^22)
    (t : Nat) (pub : List Fp)
    (hc : ∀r,r<rows.size→∀e∈ProcPriorCodecActual.table.constraints,
      e.eval (SchedHeight.trace rows codecPad) t r pub=0)
    (hb : ∀r,r<rows.size→∀i∈ProcPriorCodecActual.table.interactions,∀e∈i.mult,
      e.eval (SchedHeight.trace rows codecPad) t r pub=0 ∨
      e.eval (SchedHeight.trace rows codecPad) t r pub=1) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace rows codecPad) t pub := by
  have _ := hcap
  refine ⟨by change 1≤22; decide,by change 22≤22; decide,?_,?_⟩
  · intro r hr e he
    by_cases h : r<rows.size
    · exact hc r h e he
    · exact (physical_local rows hne t r (by omega) hr pub).1 e he
  · intro r hr i hi e he
    by_cases h : r<rows.size
    · exact hb r h i hi e he
    · exact (physical_local rows hne t r (by omega) hr pub).2 i hi e he
end ZkFormal.NearV3.Candidates.ProcCodecPhysicalPadding
