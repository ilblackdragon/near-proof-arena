import ZkFormal.NearV3.Qv.Extract.WalkIndex

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable
open Candidates.ValueTable (tau count)

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub) (q : WalkChain tr tt)
include hL

theorem WalkChain.indexed_order (i : Nat) (hidx : i+1<q.segs.length) :
    (tr.cell tt q.segs[i].1 main=1 → tr.cell tt q.segs[i].1 lastMain=0 →
      tr.cell tt q.segs[i+1].1 main=1 ∧ tr.cell tt q.segs[i+1].1 slot=tr.cell tt q.segs[i].1 slot+1 ∧
      tr.cell tt q.segs[i+1].1 lo=1-tr.cell tt q.segs[i].1 lo*(1-tr.cell tt q.segs[i].1 hi) ∧
      tr.cell tt q.segs[i+1].1 hi=tr.cell tt q.segs[i].1 lo+tr.cell tt q.segs[i].1 hi-tr.cell tt q.segs[i].1 lo*tr.cell tt q.segs[i].1 hi ∧
      tr.cell tt q.segs[i+1].1 count=tr.cell tt q.segs[i].1 count) ∧
    (tr.cell tt q.segs[i].1 lastMain=1 → tr.cell tt q.segs[i+1].1 main=0 ∧ tr.cell tt q.segs[i+1].1 tau=1) ∧
    (tr.cell tt q.segs[i].1 main=0 → tr.cell tt q.segs[i+1].1 main=0 ∧ tr.cell tt q.segs[i+1].1 tau=tr.cell tt q.segs[i].1 tau+1) := by
  have hp : q.segs[i]∈q.segs := List.getElem_mem (by omega)
  have hn : q.segs[i+1]∈q.segs := List.getElem_mem hidx
  have hpb := seg_le_end q.segs 0 q.consecutive _ hp
  have hnb := seg_le_end q.segs 0 q.consecutive _ hn
  exact adjacent_order hL (by have := q.fits; omega) (by have := q.fits; omega)
    (q.valid _ hp) (q.valid _ hn) (consec_get q.segs 0 q.consecutive i hidx)

/-- Once implicit requests start, no later walk can re-enter the main phase. -/
theorem WalkChain.implicit_suffix (i j : Nat) (hi : i<q.segs.length) (hj : j<q.segs.length)
    (hij : i≤j) (hm : tr.cell tt q.segs[i].1 main=0) : tr.cell tt q.segs[j].1 main=0 := by
  induction j with
  | zero =>
    have he : i=0 := by omega
    subst i
    exact hm
  | succ j ih =>
    by_cases he : i=j+1
    · subst i; exact hm
    · have hprev := ih (by omega) (by omega)
      exact ((WalkChain.indexed_order hL q j hj).2.2 hprev).1

/-- On the implicit suffix the field counter equals its initial value plus the
actual request-index distance; the distance is physically bounded. -/
theorem WalkChain.implicit_counter (i j : Nat) (hi : i<q.segs.length) (hj : j<q.segs.length)
    (hij : i≤j) (hm : tr.cell tt q.segs[i].1 main=0) :
    tr.cell tt q.segs[j].1 tau=tr.cell tt q.segs[i].1 tau+((j-i:Nat):Fp) := by
  induction j with
  | zero =>
    have he : i=0 := by omega
    subst i
    simp only [Nat.sub_self,Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.add_zero]
  | succ j ih =>
    by_cases he : i=j+1
    · subst i
      simp only [Nat.sub_self,Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.add_zero]
    · have hprev := ih (by omega) (by omega)
      have hmain := WalkChain.implicit_suffix hL q i j hi (by omega) (by omega) hm
      have hstep := ((WalkChain.indexed_order hL q j hj).2.2 hmain).2
      rw [hstep,hprev,show j+1-i=(j-i)+1 by omega,natCast_add]
      grind

/-- The first implicit request starts at one; all subsequent counters decode
as ordinary naturals without a supplied no-wrap assumption. -/
theorem WalkChain.implicit_counter_nat (i j : Nat) (hi : i<q.segs.length) (hj : j<q.segs.length)
    (hij : i≤j) (hm : tr.cell tt q.segs[i].1 main=0) (ht : tr.cell tt q.segs[i].1 tau=1) :
    cv tr tt q.segs[j].1 tau=1+(j-i) := by
  have hh := WalkChain.implicit_counter hL q i j hi hj hij hm
  have he : tr.cell tt q.segs[j].1 tau=((1+(j-i):Nat):Fp) := by
    rw [natCast_add]
    rw [ht] at hh
    simpa only [Lean.Grind.Semiring.natCast_one] using hh
  have hb := q.length_le_height
  have hc := height_le hL
  have hp : 1+(j-i)<P := by unfold P; omega
  simp only [cv,he,toNat_natCast,Nat.mod_eq_of_lt hp]

end ZkFormal.NearV3.Qv.Extract
