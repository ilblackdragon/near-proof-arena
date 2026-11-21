import StateM5a.TmplIf
import StateM5a.ChipStub

/-!
# StateM5a.TmplDeploy — the templates' deployed extra tables meet the premises

The proofs run `m5tSeg D` with the cached execution-side tape (`SREQ`/`HB`) and the native chip
(`ChipStub.chipStub` on `IF384`), and `m5tIF D` with the chip alone; `ChipStub.holds_of_holdsX` turns
the prover's precheck into `Holds` of exactly these AIRs.  The bus premises of `TmplSeg.m5tSeg_ws`,
`TmplWsx.seg_rin_rout` and `TmplIf.m5tIF_roots` hold for them (`hx` is not vacuous).
-/

namespace StateM5a.TmplDeploy

open ZkFormal.Air StateM5a.Tape

/-! ## The deployment's extra tables meet the premises (non-vacuity of `hx`) -/

/-- The segment proof's extra tables (the cached execution-side tape on `SREQ`/`HB`, the native
chip's stub on `IF384`) use none of `WM`, `PT`, `RCH`, `RNG`. -/
theorem seg_extra_ok {host : List (Nat × Bool × List Nat)} (hh : ∀ e ∈ host, e.1 = B_SREQ ∨ e.1 = B_HB) :
    ∀ T ∈ [tapeTable host, ChipStub.chipStub], ∀ i ∈ T.interactions,
      i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG := by
  intro T hT i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · simp only [tapeTable, List.mem_map] at hi
    obtain ⟨e, he, rfl⟩ := hi
    rcases hh e he with h | h <;> simp only [h] <;> decide
  · simp only [ChipStub.chipStub_ix, List.mem_singleton] at hi
    subst hi; decide

/-- The IF proof's only extra table is the chip stub: no `RCH`. -/
theorem if_extra_ok : ∀ T ∈ [ChipStub.chipStub], ∀ i ∈ T.interactions, i.bus ≠ B_RCH := by
  intro T hT i hi
  simp only [List.mem_singleton] at hT
  subst hT
  simp only [ChipStub.chipStub_ix, List.mem_singleton] at hi
  subst hi; decide

end StateM5a.TmplDeploy
