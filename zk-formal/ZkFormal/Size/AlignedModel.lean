import ZkFormal.Size.PadHeader
import ZkFormal.Size.V3Synth

namespace ZkFormal.Size
open ZkFormal.Stark ZkFormal.Air ZkFormal.Prover.SizeBound ZkFormal.V2.SizeSched

/-- Shape accounting for aligned honest headers. -/
def sizeOfAligned (prm : Params) (ts : List TShape) : Nat :=
  let nq := prm.numChunks * prm.posPerChunk
  let N := prm.maxLogLde
  prefixS prm ts +
    (4 * rowsS prm ts (·.w) + 64 * dsum nq N) +
    (4 * rowsS prm ts (fun t => 8 * t.aux) + 64 * dsum nq N) +
    (4 * rowsS prm ts (fun t => 8 * t.quot) + 64 * dsum nq N) +
    friAlignedMax prm

theorem sizeMaxAligned_eq_model (A : Air) (prm : Params) :
    sizeMaxAligned A prm = sizeOfAligned prm (A.tables.map (shapeOf prm.auxGroup)) := by
  unfold sizeMaxAligned sizeOfAligned rowsS rowsMax
  rw [prefixMax_eq]
  simp only [List.map_map]
  rfl

namespace V3
/-- Diagnostic model only: add the required second SHA instance. Queue-value
parser shapes and honest padding are not yet included in this model. -/
def twoShaS (g : Nat) : List TShape := shapeOf g shaT :: v3S g

/-- Proposed static caps aligned relative to log 22, with arity log 3.
This does not modify any actual AIR table. -/
def padShape22 (t : TShape) : TShape :=
  { t with maxLog := padLog22 t.maxLog }

def paddedTwoShaS (g : Nat) : List TShape := (twoShaS g).map padShape22

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Conditional FRI bound, evaluated by the kernel. -/
theorem friAligned_g2 : friAlignedMax (V2.G.pg 2) = 1061952 := by decide +kernel

/-- The corrected one-SHA synthetic model saves 1,624,192 bytes under alignment. -/
theorem aligned_oneSha_g2 : sizeOfAligned (V2.G.pg 2) (v3S 2) = 5523231 := by decide +kernel

/-- Two SHA instances, before increasing static caps for padding. -/
theorem aligned_twoSha_g2 : sizeOfAligned (V2.G.pg 2) (twoShaS 2) = 6125856 := by decide +kernel

/-- Includes the larger proposed static caps, but still omits qvV3. -/
theorem aligned_padded_twoSha_g2 :
    sizeOfAligned (V2.G.pg 2) (paddedTwoShaS 2) = 6164160 := by decide +kernel

/-- Diagnostic remaining budget after the full maximum hint: 929,431 bytes.
This is not a final prover certificate; missing tables must fit this budget. -/
theorem padded_twoSha_hint_margin :
    sizeOfAligned (V2.G.pg 2) (paddedTwoShaS 2) + 1295017 + 929431 = 8388608 := by
  rw [aligned_padded_twoSha_g2]

/-- Each proposed cap is large enough and aligns with the largest cap. This
checks the shapes only, not a trace generator or the final assembled AIR. -/
theorem padded_caps : ((twoShaS 2).all fun t =>
    decide (t.maxLog ≤ (padShape22 t).maxLog ∧ (padShape22 t).maxLog ≤ 22 ∧
      3 ∣ 22 - (padShape22 t).maxLog)) = true := by decide +kernel

end V3
end ZkFormal.Size
