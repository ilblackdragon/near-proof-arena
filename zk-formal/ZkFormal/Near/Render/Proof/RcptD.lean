import ZkFormal.Near.Render.Proof.RcptStr

/-!
# ZkFormal.Near.Render.Proof.RcptD — the receipt data of a `Good` batch

Per receipt `d = Df c e r`: key tag `kt ≤ 1`, key / id lengths, a refund only
with `gas_price ≥ block_gas_price`; between receipts: the running offsets
`o`, `o2`, the refund count and the tokens chain (`d_{r+1}.o = oEnd d_r`, …).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

section
variable {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r < NN e)
include hg hr

theorem d_kt : (Df c e r).kt ≤ 1 := by
  rw [Df_eq hr]; exact pk_tag (rc_slice hg hr)

theorem d_pk : (Df c e r).pk.length = 32 + 32 * (Df c e r).kt := by
  have h := rc_slice hg hr
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true] at h
  have hpk := h.1.1.1.1.1.2
  rw [Df_eq hr]
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hpk
  simp only [rdOf, toNats, List.length_map, mkInfo_e]
  rcases hpk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem d_id : (Df c e r).id.length = 32 := by
  have h := rc_slice hg hr
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true, beq_iff_eq] at h
  rw [Df_eq hr]; simp only [rdOf, toNats, List.length_map, mkInfo_e]; exact h.1.1.1.1.2

theorem enc_len : (toNats (e.rc r).encode).length =
    123 + (Df c e r).pred.length + (Df c e r).recv.length + (Df c e r).signer.length + 32 * (Df c e r).kt := by
  have hpk := d_pk hg hr
  have hid := d_id hg hr
  rw [Df_eq hr] at hpk hid ⊢
  simp only [rdOf, toNats, List.length_map, mkInfo_e] at hpk hid ⊢
  simp only [Receipt.encode, borshBytes, PublicKey.encode, List.length_append, List.length_singleton, u8, u32,
    u128, leN_length, hpk, hid]
  omega

theorem refund_len (hh : hasRefund (mkInfo c e) r = true) :
    (toNats (gasRefundReceipt (e.rc r) c.blockHeight (surplusOf c.blockGasPrice (e.rc r))).encode).length =
      129 + 2 * (Df c e r).signer.length + 32 * (Df c e r).kt := by
  have hpk := d_pk hg hr
  rw [Df_eq hr] at hpk ⊢
  simp only [rdOf, toNats, List.length_map, mkInfo_e] at hpk ⊢
  simp only [gasRefundReceipt, Receipt.encode, borshBytes, PublicKey.encode, List.length_append,
    List.length_singleton, u8, u32, u128, leN_length, hpk, receiptIdFrom, ArenaCore.sha256_length,
    AccountId.system, List.length_cons, List.length_nil]
  omega

theorem d_ge : (Df c e r).hr = true → (Df c e r).ge = true := by
  rw [Df_eq hr]
  simp only [rdOf, hasRefund, mkInfo_e, mkInfo_c, Ext.refundOf, decide_eq_true_eq, ne_eq]
  intro h
  by_cases hs : surplusOf c.blockGasPrice (e.rc r) = 0
  · simp [hs] at h
  · simp only [surplusOf, burnPrice] at hs
    have : ¬ (e.rc r).gasPrice ≤ c.blockGasPrice := by
      intro hle; apply hs; rw [Nat.min_eq_left hle, Nat.sub_self, Nat.mul_zero]
    have h2 : c.blockGasPrice ≤ (e.rc r).gasPrice := by omega
    exact decide_eq_true h2

end

theorem d_zero {c : Claim} {e : Ext} (hn : 0 < NN e) :
    (Df c e 0).o = 12 ∧ (Df c e 0).o2 = 4 ∧ (Df c e 0).rcnt = 0 ∧ (Df c e 0).tok0 = 0 ∧ (Df c e 0).r = 0 := by
  rw [Df_eq hn]; simp [rdOf, Ext.tokAt]

section
variable {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r + 1 < NN e)
include hg hr

theorem d_succ :
    (Df c e (r + 1)).o = oEndOf (Df c e r) ∧ (Df c e (r + 1)).o2 = o2EndOf (Df c e r) ∧
    (Df c e (r + 1)).rcnt = (Df c e r).rcnt + b2n (Df c e r).hr ∧
    (Df c e (r + 1)).tok0 = (Df c e r).tok0 + (Df c e r).burnt := by
  have he := enc_len hg (show r < NN e by omega)
  have hrf := refund_len hg (show r < NN e by omega)
  rw [Df_eq hr, Df_eq (show r < NN e by omega)]
  rw [Df_eq (show r < NN e by omega)] at he hrf
  simp only [rdOf, List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, oEndOf, o2EndOf, mkInfo_e, mkInfo_c, Ext.tokAt] at he hrf ⊢
  refine ⟨by omega, ?_, by omega, by first | trivial | rfl | simp⟩
  by_cases hh : hasRefund (mkInfo c e) r = true
  · simp only [hh, if_true, hrf hh]; omega
  · simp only [hh, Bool.false_eq_true, if_false]; omega

end

end RcptP

end ZkFormal.Near.Render
