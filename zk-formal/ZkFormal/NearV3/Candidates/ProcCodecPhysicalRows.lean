import ZkFormal.NearV3.Candidates.ProcCodecPhysicalPadding
namespace ZkFormal.NearV3.Candidates.ProcCodecPhysicalRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ProcCodecPhysicalPadding

theorem active_cells (rows : Array (Array Nat)) (r : Nat) (hr : r<rows.size) :
    cells rows r=(fun c=>Fp.ofNat rows[r]![c]!) := by
  funext c
  unfold cells natCell
  rw [natRow_lt _ _ hr]
  rw [show rows[r]! =rows[r]'hr by simp [hr]]
  rfl

/-- Local helper-row equations evaluate identically on adjacent active physical
rows; only the genuine first-row indicator remains variable. -/
theorem adjacent_eval (rows : Array (Array Nat)) (hcap : rows.size≤2^22)
    (t r : Nat) (hr : r+1<rows.size) (pub : List Fp) (e : Expr) (he : e.pubBound=0) :
    e.eval (SchedHeight.trace rows codecPad) t r pub=
      e.evalWith (ProcPriorCells.env
        (fun c=>Fp.ofNat rows[r]![c]!) (fun c=>Fp.ofNat rows[r+1]![c]!)
        (if r=0 then 1 else 0) 0 1) := by
  have ht : r+1<2^22 := by omega
  rw [physical_eval rows t r (by omega) pub e he,Nat.mod_eq_of_lt ht,
    active_cells rows r (by omega),active_cells rows (r+1) hr]
  simp [show r+1≠2^22 by omega,ht]

/-- The final generated row is followed by zero padding, with no cyclic
shortcut. A strict capacity bound ensures the successor physically exists. -/
theorem last_active_eval (rows : Array (Array Nat)) (hne : 0<rows.size)
    (hcap : rows.size<2^22) (t : Nat) (pub : List Fp) (e : Expr) (he : e.pubBound=0) :
    e.eval (SchedHeight.trace rows codecPad) t (rows.size-1) pub=
      e.evalWith (ProcPriorCells.env
        (fun c=>Fp.ofNat rows[rows.size-1]![c]!) (fun _=>0)
        (if rows.size-1=0 then 1 else 0) 0 1) := by
  have hi : rows.size-1+1=rows.size := by omega
  rw [physical_eval rows t (rows.size-1) (by omega) pub e he,hi,
    Nat.mod_eq_of_lt hcap,active_cells rows (rows.size-1) (by omega),
    padding_cells rows rows.size (Nat.le_refl _)]
  simp [show rows.size≠2^22 by omega,hcap]
def rowEnvAt (rows : Array (Array Nat)) (r : Nat) : Env Fp :=
  ProcPriorCells.env (fun c=>Fp.ofNat rows[r]![c]!)
    (if r+1<rows.size then fun c=>Fp.ofNat rows[r+1]![c]! else fun _=>0)
    (if r=0 then 1 else 0) 0 1

theorem generated_eval (rows : Array (Array Nat)) (hcap : rows.size<2^22)
    (t r : Nat) (hr : r<rows.size) (pub : List Fp) (e : Expr) (he : e.pubBound=0) :
    e.eval (SchedHeight.trace rows codecPad) t r pub=e.evalWith (rowEnvAt rows r) := by
  by_cases hn : r+1<rows.size
  · simpa only [rowEnvAt,if_pos hn] using adjacent_eval rows (by omega) t r hn pub e he
  · have hlast : r=rows.size-1 := by omega
    subst r
    simpa only [rowEnvAt,if_neg hn] using last_active_eval rows (by omega) hcap t pub e he

/-- Concrete row-pair equations suffice for full physical Codec TableLocal.
Padding, public-input independence and the active-to-padding boundary are derived. -/
theorem table_of_rows (rows : Array (Array Nat)) (hne : 0<rows.size)
    (hcap : rows.size<2^22) (t : Nat) (pub : List Fp)
    (hc : ∀r,r<rows.size→∀e∈ProcPriorCodecActual.constraints,e.evalWith (rowEnvAt rows r)=0)
    (hb : ∀r,r<rows.size→∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,
      e.evalWith (rowEnvAt rows r)=0 ∨ e.evalWith (rowEnvAt rows r)=1) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace rows codecPad) t pub := by
  have hp : ∀e∈ProcPriorCodecActual.constraints,e.pubBound=0 := by decide +kernel
  have hm : ∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,e.pubBound=0 := by decide +kernel
  apply ProcCodecPhysicalPadding.of_active rows hne (by omega) t pub
  · intro r hr e he
    rw [generated_eval rows hcap t r hr pub e (hp e he)]
    exact hc r hr e he
  · intro r hr i hi e he
    rw [generated_eval rows hcap t r hr pub e (hm i hi e he)]
    exact hb r hr i hi e he
end ZkFormal.NearV3.Candidates.ProcCodecPhysicalRows
