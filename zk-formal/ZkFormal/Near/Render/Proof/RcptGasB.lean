import ZkFormal.Near.Render.Proof.RcptGasF
import ZkFormal.Near.Render.Proof.RcptFam

/-!
# ZkFormal.Near.Render.Proof.RcptGasB — the receipt data of a `Good` batch satisfies `GasOk`

From `Receipt.wf` (`gas_price < 2^128`) and `RcptOk` (no overflow of `burnt`,
the surplus and the tokens).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

namespace RcptP

open RcptGen

theorem two128_eq : Params.two128 = 256 ^ 16 := by decide

theorem gp_dep_lt {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r < NN e) :
    (e.rc r).gasPrice < 256 ^ 16 ∧ (e.rc r).deposit < 256 ^ 16 := by
  have h := rc_slice hg hr
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← two128_eq]; exact ⟨h.1.1.1.2, h.1.1.2⟩

theorem gasOk {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r < NN e) (hB : c.blockGasPrice < 256 ^ 16) :
    GasOk (Df c e r) (BG c) c.blockGasPrice := by
  have ok := hg.rcpt_ok r hr
  have o1 := ok.burnt_lt; have o2 := ok.surplus_lt; have o3 := ok.tok_lt
  rw [two128_eq] at o1 o2 o3
  have hgp := (gp_dep_lt hg hr).1
  rw [Df_eq hr]
  refine ⟨fun i => rfl, hB, hgp, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · exact o1
  · exact o2
  · exact o3
  · simp only [rdOf, hasRefund, mkInfo_e, mkInfo_c, Ext.refundOf]
    by_cases hs : surplusOf c.blockGasPrice (e.rc r) = 0 <;> simp [hs]

end RcptP

end ZkFormal.Near.Render
