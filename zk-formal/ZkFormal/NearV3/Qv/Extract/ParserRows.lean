import ZkFormal.NearV3.Qv.Extract.CounterAggregate
import ZkFormal.NearV3.Qv.Candidates.CombinedParser
import ZkFormal.NearV3.Qv.Candidates.CombinedBoundary

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem first_mode_zero : tr.cell tt 0 Candidates.ValueTable.len=0 := by
  have hr := height_pos hL
  have ha := flag_walk hL hr (x:=wf) (by simp) (walk_start hL hr)
  have hh := walk_read_mode hL hr ha
  obtain ⟨hm,ht,hs,hl,hhi⟩ := order_start hL
  rw [hm,hl,hhi] at hh
  grind

/-- Parser constraints are recovered even at the cyclic physical boundary:
row zero is a delayed walk with overlaid parser length zero. -/
theorem parser_constraints {r : Nat} (hr : r<tr.height tt) (hw : tr.cell tt r walk=0) :
    ∀ e∈Candidates.ValueTable.constraints, e.eval tr tt r pub=0 := by
  have hn : tr.cell tt ((r+1)%tr.height tt) walk=0 ∨
      tr.cell tt ((r+1)%tr.height tt) Candidates.ValueTable.len=0 := by
    by_cases he : r+1=tr.height tt
    · right
      rw [he,Nat.mod_self]
      exact first_mode_zero hL
    · left
      have hb : r+1<tr.height tt := by omega
      rw [Nat.mod_eq_of_lt hb]
      exact walk_pad hL hb hw
  intro e he
  have hh := con hL hr (parser_constraint_mem he)
  rw [parser_row_preserved_or_zero tr tt r pub (fun next => by
    cases next
    · exact Or.inl hw
    · exact hn) e] at hh
  exact hh

theorem parser_traffic {r : Nat} (hr : r<tr.height tt) (hw : tr.cell tt r walk=0)
    (bus : Nat) (sd : Bool) :
    rowTraffic interactions tr tt r pub bus sd=
      rowTraffic Candidates.ValueTable.interactions tr tt r pub bus sd := by
  have hz := parser_flags_zero tr tt r pub hw (fun e he => con hL hr he)
  exact parser_row_traffic tr tt r pub hw (hz _ (by simp)) (hz _ (by simp))
    (hz _ (by simp)) (hz _ (by simp)) (hz _ (by simp)) bus sd

end ZkFormal.NearV3.Qv.Extract
