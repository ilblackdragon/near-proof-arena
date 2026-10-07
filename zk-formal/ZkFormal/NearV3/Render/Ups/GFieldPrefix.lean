import ZkFormal.NearV3.Render.Ups.GFields
import ZkFormal.NearV3.Render.Ups.FieldWindows

/-! The first 26 update-field constraints: framing, index advances and field widths.
Field-kind succession and window-role constraints remain separate obligations. -/
namespace ZkFormal.NearV3.Render.UpsGen

theorem cFields_prefix_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H (UpsV3.cFields.take 26) := by
  change GroupOk insts H (cFieldFrame ++ cFieldAdvance ++ cFieldLengths)
  exact groupOk_append (groupOk_append (cFieldFrame_ok ok hf hH)
    (cFieldAdvance_ok ok hf hH)) (cFieldLengths_ok ok hf hH)

end ZkFormal.NearV3.Render.UpsGen
