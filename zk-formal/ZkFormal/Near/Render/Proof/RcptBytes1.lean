import ZkFormal.Near.Render.Proof.ShaFit4
import ZkFormal.Near.Render.Proof.BusBytes

/-!
# ZkFormal.Near.Render.Proof.RcptBytes1 — the rcpt view's byte strings

For receipt `r` of a `Good` batch, the view `x = rcptViewOf (rdOf I r)` has
`x.enc = toNats (rc r).encode` (`enc_eq`), the refund encoding
(`encRefund_eq`), `x.peo = peoBytes I r` (`peo_eq`), `x.leaf = leafBytes I r`
(`leaf_eq`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

theorem toNats_append (a b : Bytes) : toNats (a ++ b) = toNats a ++ toNats b := by
  simp [toNats]

theorem toNats_u32_small {x : Nat} (h : x < 256) : toNats (u32 x) = u32r x := by
  simp [toNats, u32, u32r, leN, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]

theorem ofNats_toNats (b : Bytes) : ofNats (toNats b) = b := by
  simp [ofNats, toNats, List.map_map, Function.comp_def]

theorem toNats_borsh {s : Bytes} (h : s.length ≤ 64) : toNats (borshBytes s) = RcptV.borshN (toNats s) := by
  simp only [borshBytes, toNats_append, RcptV.borshN, toNats_u32_small (show s.length < 256 by omega)]
  simp [toNats]

theorem tailN_eq : toNats (u32 0 ++ u32 0 ++ u32 1 ++ [3]) = tailN := by decide

theorem pk_tag {r : Receipt} (h : r.inSlice = true) : r.signerPk.tag ≤ 1 := by
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hpk⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hpk
  rcases hpk with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

theorem toNats_pk {k : PublicKey} (h : k.tag ≤ 1) : toNats k.encode = [k.tag] ++ toNats k.data := by
  simp only [PublicKey.encode, u8, toNats_append]
  simp [toNats, leN, Nat.mod_eq_of_lt (show k.tag < 256 by omega)]

theorem mkInfo_c {c : Claim} {e : Ext} : (mkInfo c e).c = c := rfl

section
variable {c : Claim} {e : Ext} (hg : Good c e) {r : Nat} (hr : r < e.rs.length)
include hg hr

theorem rc_inSlice : (e.rc r).inSlice = true := by
  have hm : e.rc r ∈ e.rs := by
    simp only [Ext.rc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
    exact List.getElem_mem _
  exact List.all_eq_true.1 hg.inSlice _ hm

theorem enc_eq : (rcptViewOf (rdOf (mkInfo c e) r)).enc = toNats (e.rc r).encode := by
  have hl := rc_lens hg hr
  have ht := pk_tag (rc_inSlice hg hr)
  simp only [RcptV.enc, rcptViewOf, rdOf, mkInfo_e, Receipt.encode, toNats_append,
    toNats_borsh hl.p, toNats_borsh hl.v, toNats_borsh hl.s, toNats_pk ht, ← tailN_eq, leBytes, u128]
  simp [toNats, List.append_assoc]

theorem encRefund_eq (hh : hasRefund (mkInfo c e) r = true) :
    (rcptViewOf (rdOf (mkInfo c e) r)).encRefund =
      toNats (gasRefundReceipt (e.rc r) c.blockHeight (surplusOf c.blockGasPrice (e.rc r))).encode := by
  have hl := rc_lens hg hr
  have ht := pk_tag (rc_inSlice hg hr)
  have hsys : toNats (borshBytes AccountId.system) = [6, 0, 0, 0] ++ systemN := by decide
  simp only [RcptV.encRefund, rcptViewOf, rdOf, mkInfo_e, gasRefundReceipt, Receipt.encode,
    toNats_append, hsys, toNats_borsh hl.s, toNats_pk ht, ← tailN_eq, leBytes, u128, ridBytes, shaN,
    receiptIdFrom, hh, ite_true, mkInfo_c]
  have hrid : ofNats (toNats (e.rc r).receiptId ++ toNats (leN 8 c.blockHeight) ++ toNats (leN 8 0)) =
      (e.rc r).receiptId ++ u64 c.blockHeight ++ u64 0 := by
    rw [← toNats_append, ← toNats_append, ofNats_toNats]; rfl
  have h16 : List.replicate 16 0 = toNats (leN 16 0) := by decide
  rw [hrid, h16]
  simp only [List.append_assoc]
  rfl

theorem peo_eq : (rcptViewOf (rdOf (mkInfo c e) r)).peo = peoBytes (mkInfo c e) r := by
  have hl := rc_lens hg hr
  have hG : toNats (u64 Params.G) = G_LEn := by decide
  have h2 : toNats ([2] ++ u32 0) = [2, 0, 0, 0, 0] := by decide
  by_cases hs : surplusOf c.blockGasPrice (e.rc r) = 0
  · have hrf : e.refundOf c r = [] := by simp [Ext.refundOf, hs]
    have hh : hasRefund (mkInfo c e) r = false := by simp [hasRefund, mkInfo_e, mkInfo_c, hrf]
    simp only [RcptV.peo, rcptViewOf, rdOf, hh, peoBytes, mkInfo_e, mkInfo_c, Ext.outcomeOf, hrf,
      Outcome.partialEncode, toNats_append, toNats_borsh hl.v, ← hG, Bool.false_eq_true, ite_false,
      List.map_nil, List.length_nil, toNats_u32_small (show 0 < 256 by decide), leBytes, u128]
    rw [← h2, toNats_append]
    simp [concatAll, toNats]
    decide
  · have hrf : e.refundOf c r = [gasRefundReceipt (e.rc r) c.blockHeight (surplusOf c.blockGasPrice (e.rc r))] := by
      simp [Ext.refundOf, hs]
    have hh : hasRefund (mkInfo c e) r = true := by simp [hasRefund, mkInfo_e, mkInfo_c, hrf]
    have hrid : ofNats (toNats (e.rc r).receiptId ++ toNats (leN 8 c.blockHeight) ++ toNats (leN 8 0)) =
        (e.rc r).receiptId ++ u64 c.blockHeight ++ u64 0 := by
      rw [← toNats_append, ← toNats_append, ofNats_toNats]; rfl
    simp only [RcptV.peo, rcptViewOf, rdOf, hh, peoBytes, mkInfo_e, mkInfo_c, Ext.outcomeOf, hrf,
      Outcome.partialEncode, toNats_append, toNats_borsh hl.v, ← hG, ite_true, ridBytes, shaN, leBytes,
      List.map_cons, List.map_nil, List.length_singleton, toNats_u32_small (show 1 < 256 by decide), u128,
      hrid, gasRefundReceipt, receiptIdFrom]
    rw [← h2, toNats_append]
    simp [concatAll, toNats]

omit hg hr in
theorem leaf_eq : (rcptViewOf (rdOf (mkInfo c e) r)).leaf = leafBytes (mkInfo c e) r := by
  have h4 : leBytes 4 2 = [2, 0, 0, 0] := by decide
  simp only [RcptV.leaf, rcptViewOf, rdOf, leafBytes, h4, mkInfo_e]

end

end ZkFormal.Near.Render
