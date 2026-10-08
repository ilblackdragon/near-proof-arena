import ZkFormal.NearV3.Assembly.RcptTokenWindows
import NearSpecV3.RuntimeD0

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1

/-- Native burn arithmetic, including the actual checked accumulator bound. -/
theorem applyReceipt_tokens (ctx : Ctx) (st out : Acc) (r : Receipt)
    (h : applyReceipt ctx st r = some out) :
    out.tokensBurnt = st.tokensBurnt + Params.G * min r.gasPrice ctx.blockGasPrice ∧
    out.tokensBurnt < Params.two128 ∧
    Params.G * min r.gasPrice ctx.blockGasPrice < Params.two128 := by
  unfold applyReceipt at h
  dsimp only at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  all_goals grind

/-- A token window taken from successful native execution has exact endpoints;
its addition does not wrap modulo the 128-bit serialization width. -/
theorem applyReceipt_token_window (ctx : Ctx) (st out : Acc) (r : Receipt)
    (h : applyReceipt ctx st r = some out) :
    let x : TokenInput := ⟨st.tokensBurnt, Params.G * min r.gasPrice ctx.blockGasPrice⟩
    x.oldBytes = u128 st.tokensBurnt ∧ x.newBytes = u128 out.tokensBurnt ∧
      x.before + x.burnt < Params.two128 := by
  obtain ⟨he, hb, _⟩ := applyReceipt_tokens ctx st out r h
  dsimp [TokenInput.oldBytes, TokenInput.newBytes]
  rw [←he]
  exact ⟨rfl,rfl,hb⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
