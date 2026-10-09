import ReexecV3D3.Logged.Runtime.API
import ReexecV3D3.Logged.D3LSpec

/-!
# Read-logging checkers: the API

One run of `checkD3Reads cb wb` (resp. `checkD2Reads`) gives `checkD3 cb wb` (resp. `checkD2`) and
the exact list of recorded-storage keys it read. Keys are tagged: `(0, h)` is a node or value of
the merged main store (`base_state ++ code blobs`, incl. contract code and every trie node / value
the WASM storage host functions read), `(k + 1, h)` one of implicit transition `k`'s `base_state`.

* `checkD3Reads_eq`: the pair is `(checkD3 cb wb, reads)`.
* `checkD3_congr`: any store that answers those keys like the witness gives the same verdict and
  the same reads.
* `reads_restrict_eq` / `reads_fixed`: the witness store restricted to the read keys gives the same
  verdict and reads exactly the same keys (fixed point).
-/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3

/-! ## D3 -/

theorem checkD3Reads_eq (cb wb : Bytes) :
    checkD3Reads cb wb = (checkD3 cb wb, SM.reads (storesOf wb) (checkD3L cb wb)) := by
  unfold checkD3Reads
  rw [SM.runR_eq]
  show (SM.run (storesOf wb) (checkD3L cb wb), _) = _
  rw [checkD3L_eq]; rfl

theorem checkD3Reads_fst (cb wb : Bytes) : (checkD3Reads cb wb).1 = checkD3 cb wb := by
  rw [checkD3Reads_eq]

theorem d3Reads_eq (cb wb : Bytes) : d3Reads cb wb = SM.reads (storesOf wb) (checkD3L cb wb) := by
  unfold d3Reads; rw [checkD3Reads_eq]

/-- **Stores agreeing on the reads give the same result** (and the same reads). -/
theorem checkD3_congr (cb wb : Bytes) (g : Nat × Bytes → Option Bytes)
    (h : ∀ k ∈ d3Reads cb wb, g k = storesOf wb k) :
    SM.run g (checkD3L cb wb) = checkD3 cb wb ∧ SM.reads g (checkD3L cb wb) = d3Reads cb wb := by
  rw [d3Reads_eq] at h ⊢
  have := SM.run_congr (storesOf wb) g (checkD3L cb wb) h
  rw [checkD3L_eq] at this
  exact this

/-- The witness store restricted to the read keys gives the same verdict. -/
theorem reads_restrict_eq (cb wb : Bytes) :
    SM.run (SM.restrict (storesOf wb) (d3Reads cb wb)) (checkD3L cb wb) = checkD3 cb wb := by
  rw [d3Reads_eq, SM.run_restrict, checkD3L_eq]

/-- **Fixed point**: the run on the restricted store reads exactly the same keys. -/
theorem reads_fixed (cb wb : Bytes) :
    SM.reads (SM.restrict (storesOf wb) (d3Reads cb wb)) (checkD3L cb wb) = d3Reads cb wb := by
  rw [d3Reads_eq, SM.reads_restrict]

/-! ## D2 -/

theorem checkD2Reads_eq (cb wb : Bytes) :
    checkD2Reads cb wb = (checkD2 cb wb, SM.reads (storesOf wb) (checkD2L cb wb)) := by
  unfold checkD2Reads
  rw [SM.runR_eq]
  show (SM.run (storesOf wb) (checkD2L cb wb), _) = _
  rw [checkD2L_eq]; rfl

theorem d2Reads_eq (cb wb : Bytes) : d2Reads cb wb = SM.reads (storesOf wb) (checkD2L cb wb) := by
  unfold d2Reads; rw [checkD2Reads_eq]

theorem checkD2_congr (cb wb : Bytes) (g : Nat × Bytes → Option Bytes)
    (h : ∀ k ∈ d2Reads cb wb, g k = storesOf wb k) :
    SM.run g (checkD2L cb wb) = checkD2 cb wb ∧ SM.reads g (checkD2L cb wb) = d2Reads cb wb := by
  rw [d2Reads_eq] at h ⊢
  have := SM.run_congr (storesOf wb) g (checkD2L cb wb) h
  rw [checkD2L_eq] at this
  exact this

theorem reads_restrict_eq_d2 (cb wb : Bytes) :
    SM.run (SM.restrict (storesOf wb) (d2Reads cb wb)) (checkD2L cb wb) = checkD2 cb wb := by
  rw [d2Reads_eq, SM.run_restrict, checkD2L_eq]

theorem reads_fixed_d2 (cb wb : Bytes) :
    SM.reads (SM.restrict (storesOf wb) (d2Reads cb wb)) (checkD2L cb wb) = d2Reads cb wb := by
  rw [d2Reads_eq, SM.reads_restrict]

end ReexecV3D3.Logged
