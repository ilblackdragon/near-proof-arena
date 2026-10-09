import ZkFormal.NearV3.Candidates.ProcConcatGeometry
import ZkFormal.NearV3.Candidates.ProcBits
namespace ZkFormal.NearV3.Candidates.ProcConcatRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcConcatGeometry ProcBits

theorem flags (rs : List Run) (r : Nat) : Flags (atRow rs r) ∧ GateBits (atRow rs r) := by
  unfold atRow
  split
  · rename_i h
    have hv := List.getElem_mem h
    obtain ⟨R,_,hm⟩ := List.mem_flatMap.1 hv
    exact ⟨records_flags R _ hm,records_bits R _ hm⟩
  · split
    · unfold tail
      split
      · exact ⟨padding_flags,padding_bits⟩
      · rename_i R _
        exact ⟨tail_flags R,tail_bits R⟩
    · exact ⟨padding_flags,padding_bits⟩

theorem active (rs : List Run) (r : Nat) :
    (atRow rs r).act=if r<(rows rs).length then 1 else 0 := by
  unfold atRow
  split
  · rename_i h
    have hv := List.getElem_mem h
    obtain ⟨R,_,hm⟩ := List.mem_flatMap.1 hv
    exact (ProcNativeRows.active_records R _ hm).1
  · split
    · unfold tail
      split <;> rfl
    · rfl

theorem shape (rs : List Run) (r : Nat) :
    (atRow rs r).act=(atRow rs r).kK+(atRow rs r).kH+(atRow rs r).kE := by
  unfold atRow
  split
  · rename_i h
    have hv := List.getElem_mem h
    obtain ⟨R,_,hm⟩ := List.mem_flatMap.1 hv
    exact (ProcNativeRows.active_records R _ hm).2
  · split
    · unfold tail
      split <;> rfl
    · rfl

theorem first (rs : List Run) :
    atRow rs 0=match rs with | []=>padPV | R::_=>keyV R 0 := by
  cases rs with
  | nil => simp [atRow,rows,tail]
  | cons R rest =>
    have h := block_lookup (R::rest) [] rest R rfl 0 (by have := row_length R; omega)
    simpa [start,rows,ProcNativeRows.first] using h

theorem trace_bits (rs : List Run) (t r : Nat) (pub : List Fp) :
    ∀i∈Proc.interactions,∀b∈i.mult,b.eval (trace rs) t r pub=0 ∨ b.eval (trace rs) t r pub=1 :=
  native_bits (atRow rs r) (flags rs r).2 (trace rs) t r pub (fun _=>rfl)
end ZkFormal.NearV3.Candidates.ProcConcatRows
