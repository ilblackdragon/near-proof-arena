import ZkFormal.NearV3.Candidates.ProcBits
import ZkFormal.NearV3.Candidates.SchedHeight
namespace ZkFormal.NearV3.Candidates.ProcHeightBits
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

def pad (R : Run) (r : Nat) : Array Nat :=
  if r=(Gen.Proc.rows R).size then Gen.Proc.tailRow R else (zrow Proc.width).set! Proc.ikc Gen.Proc.ikcPad

def trace (R : Run) : Trace Fp := SchedHeight.trace (Gen.Proc.rows R) (pad R)

theorem row_record (R : Run) (r : Nat) :
    ∃ V, ProcBits.GateBits V ∧ ProcBits.Flags V ∧ ∀ c, natCell (Gen.Proc.rows R) (pad R) r c = V.cell c := by
  by_cases hr : r<(Gen.Proc.rows R).size
  · have hrel := proc_rows_rel R
    have hlen : r<(procVs R).length := by
      rw [←hrel.length,Array.length_toList]; exact hr
    refine ⟨(procVs R)[r],ProcBits.records_bits R _ (List.getElem_mem hlen), ProcBits.records_flags R _ (List.getElem_mem hlen),?_⟩
    intro c
    have h := (hrel.get r (by simpa using hr) hlen).cell c
    simpa [natCell,natRow_lt _ _ hr] using h
  · by_cases he : r=(Gen.Proc.rows R).size
    · refine ⟨tailV R,ProcBits.tail_bits R,ProcBits.tail_flags R,?_⟩
      intro c
      rw [natCell,natRow_ge _ _ (by omega),pad,if_pos he]
      exact (tail_rel R).cell c
    · refine ⟨padPV,ProcBits.padding_bits,ProcBits.padding_flags,?_⟩
      intro c
      rw [natCell,natRow_ge _ _ (by omega),pad,if_neg he]
      exact pad_rel.cell c

theorem trace_bits (R : Run) (t r : Nat) (pub : List Fp) :
    ∀ i ∈ Proc.interactions, ∀ b ∈ i.mult,
      b.eval (trace R) t r pub=0 ∨ b.eval (trace R) t r pub=1 := by
  obtain ⟨V,hv,hflags,hc⟩ := row_record R r
  apply ProcBits.native_bits V hv
  intro c
  change Fp.ofNat (natCell (Gen.Proc.rows R) (pad R) r c)=_
  rw [hc]
/-- Boolean constraints hold on every generated active row and both native padding forms. -/
theorem trace_bool (R : Run) (t r : Nat) (pub : List Fp) :
    ∀ c ∈ Proc.boolCols, (ZkFormal.Chacha.Table.boolC c).eval (trace R) t r pub=0 := by
  obtain ⟨V,hv,hflags,hc⟩ := row_record R r
  intro c hcol
  have hb := hflags c hcol
  change Fp.ofNat (natCell (Gen.Proc.rows R) (pad R) r c) *
    (Fp.ofNat (natCell (Gen.Proc.rows R) (pad R) r c) + -(1 : Fp)) = 0
  rw [hc]
  have h := ofNat_bit hb
  rcases h with h | h <;> rw [h] <;> grind

end ZkFormal.NearV3.Candidates.ProcHeightBits
