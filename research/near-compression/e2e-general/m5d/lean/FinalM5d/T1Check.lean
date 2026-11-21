import FinalM5d.T1Data
import FinalM5d.Tail

/-!
# FinalM5d.T1Check — non-vacuity on T1

T1's actual FIN-row values (the proved trace's statement window, `FinIn`, computed roots and body
length, `T1Data.lean`, generated from the Lean checker's run) satisfy `RowOK` (kernel `decide`);
the window is T1's public `chunk_inner`; the outputs `outputsOf` built from them are the checker's
(`tailNew`'s state root, gas used, gas limit, balance burnt, roots, length); hence the spec decoder
accepts T1's `chunk_inner` and `headerOk` holds — the premise of `row_headerOk` is satisfiable and
met by the chunk the template proves.
-/

namespace FinalM5d.T1

open NearSpec NearSpecV3 NearSpecV3.E2E FinalM5d.Link

def fn (l : List Nat) : Nat → Nat := fun k => l.getD k 0

theorem t1_rowOK : RowOK (fn hb) (fn fi) (fn ro) (fn rs) (fn rsh) n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The window is T1's public chunk inner. -/
theorem t1_window : win (fn hb) = chunkInner.map UInt8.ofNat := by decide +kernel

/-- The template's outputs are the checker's. -/
theorem t1_outputs :
    (outputsOf (fn fi) (fn ro) (fn rs) (fn rsh) n).stateRoot = stateRoot.map UInt8.ofNat ∧
    (outputsOf (fn fi) (fn ro) (fn rs) (fn rsh) n).gasUsed = gasUsed ∧
    (outputsOf (fn fi) (fn ro) (fn rs) (fn rsh) n).gasLimit = gasLimit ∧
    (outputsOf (fn fi) (fn ro) (fn rs) (fn rsh) n).balanceBurnt = balanceBurnt := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Non-vacuity**: T1's public chunk inner decodes, and `headerOk` holds against the outputs the
template computes on T1. -/
theorem t1_headerOk :
    decodeChunkInner (chunkInner.map UInt8.ofNat) = .ok (hdrOf (fn hb)) ∧
      headerOk (hdrOf (fn hb)) (outputsOf (fn fi) (fn ro) (fn rs) (fn rsh) n) = true := by
  rw [← t1_window]; exact row_headerOk t1_rowOK

end FinalM5d.T1
