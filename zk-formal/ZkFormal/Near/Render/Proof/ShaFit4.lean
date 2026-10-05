import ZkFormal.Near.Render.Proof.ShaFit3

/-!
# ZkFormal.Near.Render.Proof.ShaFit4 — `ShaLocalStmt`, `ShaTrafficStmt`

The rcpt messages (`RC`, `RF`: `≤ 12 + 400·256` bytes; `PEO ≤ 133`,
`LEAF = 68`, `RID = 48` bytes per receipt) and the total:

| messages | SHA rows |
|---|---|
| node (`NPRE`, `NPOST`) | `≤ (5·3·10^6 + 144·256)/4 = 3 759 216` |
| acct (`VPRE`, `VPOST`) | `≤ 70·256 = 17 920` |
| mrk (`MRK`) | `≤ 13 600` |
| rcpt | `≤ 27 238 + 27 237 + 105·256 = 81 355` |

in all `≤ 3 872 091 ≤ 2^22`, so `Sha.MsgsOk` holds (`msgsOk`) and L5's
completeness gives `shaLocal : ShaLocalStmt`, `shaTraffic_ok : ShaTrafficStmt`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-! ## Receipt encodings -/

structure RLens (r : Receipt) : Prop where
  p : r.predecessorId.length ≤ 64
  v : r.receiverId.length ≤ 64
  s : r.signerId.length ≤ 64
  pk : r.signerPk.data.length ≤ 64
  id : r.receiptId.length = 32

theorem valid_le {s : Bytes} (h : AccountId.valid s = true) : s.length ≤ 64 := by
  simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem rlens_of {r : Receipt} (h : r.inSlice = true) : RLens r := by
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨vp, vv⟩, vs⟩, hpk⟩, hid⟩, -⟩, -⟩, -⟩, -⟩ := h
  refine ⟨valid_le vp, valid_le vv, valid_le vs, ?_, by simpa using hid⟩
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hpk
  rcases hpk with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

theorem encode_len {r : Receipt} (h : RLens r) : r.encode.length ≤ 400 := by
  have := h.p; have := h.v; have := h.s; have := h.pk; have := h.id
  simp only [Receipt.encode, borshBytes, PublicKey.encode, List.length_append, List.length_singleton,
    u8, u32, u128, leN_length]
  omega

theorem refund_lens {p : Receipt} (h : RLens p) (ht s : Nat) : RLens (gasRefundReceipt p ht s) :=
  ⟨by simp [gasRefundReceipt, AccountId.system], h.s, h.s, h.pk,
   by simp [gasRefundReceipt, receiptIdFrom, ArenaCore.sha256_length]⟩

theorem encodeReceipts_len (rs : List Receipt) (h : ∀ r ∈ rs, RLens r) :
    (encodeReceipts rs).length ≤ 4 + 400 * rs.length := by
  have : ((rs.map Receipt.encode).map List.length).sum ≤ 400 * rs.length := by
    rw [List.map_map]
    exact sum_map_le_mul _ 400 rs (fun r hr => encode_len (h r hr))
  simp only [encodeReceipts, List.length_append, u32, leN_length, concatAll_len]
  omega

section
variable {c : Claim} {e : Ext} (hg : Good c e)
include hg

theorem rc_lens {r : Nat} (hr : r < e.rs.length) : RLens (e.rc r) := by
  apply rlens_of
  have hm : e.rc r ∈ e.rs := by
    simp only [Ext.rc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
    exact List.getElem_mem _
  exact List.all_eq_true.1 hg.inSlice _ hm

theorem refunds_lens : ∀ x ∈ e.refunds c, RLens x := by
  intro x hx
  simp only [Ext.refunds, List.mem_flatMap, List.mem_range] at hx
  obtain ⟨r, hr, hx⟩ := hx
  simp only [Ext.refundOf] at hx
  split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx
    subst hx; exact refund_lens (rc_lens hg hr) _ _

omit hg in
theorem refunds_len : (e.refunds c).length ≤ e.rs.length := by
  simp only [Ext.refunds, List.length_flatMap]
  have := sum_map_le_mul (fun r => (e.refundOf c r).length) 1 (List.range e.rs.length) (fun r _ => by
    simp only [Ext.refundOf]; split <;> simp)
  simpa [Function.comp_def] using this

theorem peo_len {r : Nat} (hr : r < e.rs.length) : (peoBytes (mkInfo c e) r).length ≤ 133 := by
  have hl := rc_lens hg hr
  have hp : (mkInfo c e).e = e := rfl
  have hc : (mkInfo c e).c = c := rfl
  simp only [peoBytes, hp, hc, toNats, List.length_map, Outcome.partialEncode, Ext.outcomeOf,
    borshBytes, List.length_append, u32, u64, u128, leN_length, List.length_singleton, concatAll_len]
  have : (((e.refundOf c r).map Receipt.receiptId).map List.length).sum ≤ 32 := by
    simp only [Ext.refundOf]; split <;> simp [gasRefundReceipt, receiptIdFrom, ArenaCore.sha256_length]
  have := hl.v
  omega

theorem leaf_len {r : Nat} (hr : r < e.rs.length) : (leafBytes (mkInfo c e) r).length = 68 := by
  have := (rc_lens hg hr).id
  simp [leafBytes, leBytes, toNats, leN_length, MrkGen.shaN_length, this, mkInfo]

theorem rid_len {r : Nat} (hr : r < e.rs.length) : (ridBytes (mkInfo c e) r).length = 48 := by
  have := (rc_lens hg hr).id
  simp [ridBytes, leBytes, toNats, leN_length, this, mkInfo]

theorem rc_len : (rcBytes (mkInfo c e)).length ≤ 12 + 400 * 256 := by
  have := encodeReceipts_len e.rs (fun x hx => rlens_of (List.all_eq_true.1 hg.inSlice x hx))
  have h2 := hg.len; have h3 := hg.n_le
  simp only [Params.maxBatch] at h3
  simp only [rcBytes, toNats, List.length_map, List.length_append, u64, leN_length]
  have : (mkInfo c e).e = e := rfl
  rw [this]
  have := Nat.mul_le_mul_left 400 (show e.rs.length ≤ 256 by omega)
  omega

theorem rf_len : (rfBytes (mkInfo c e)).length ≤ 4 + 400 * 256 := by
  have := encodeReceipts_len (e.refunds c) (refunds_lens hg)
  have := refunds_len (c := c) (e := e)
  have h2 := hg.len; have h3 := hg.n_le
  simp only [Params.maxBatch] at h3
  simp only [rfBytes, toNats, List.length_map]
  have : (mkInfo c e).e = e := rfl
  have hc : (mkInfo c e).c = c := rfl
  rw [this, hc]
  have := Nat.mul_le_mul_left 400 (show (e.refunds c).length ≤ 256 by omega)
  omega

theorem rcpt_rows : rowsL (rcptMsgs (mkInfo c e)) ≤ 27238 + 27237 + 105 * 256 := by
  have hn : (mkInfo c e).nRcpt = e.rs.length := rfl
  have h2 := hg.len; have h3 := hg.n_le
  simp only [Params.maxBatch] at h3
  simp only [rcptMsgs, rowsL_append]
  have a1 := rowsOf_le (rcBytes (mkInfo c e)).length
  have a2 := rowsOf_le (rfBytes (mkInfo c e)).length
  have b1 := rc_len hg
  have b2 := rf_len hg
  have hper : rowsL ((List.range (mkInfo c e).nRcpt).flatMap fun r =>
      [(⟨msgId K_PEO r, peoBytes (mkInfo c e) r⟩ : Msg), ⟨msgId K_LEAF r, leafBytes (mkInfo c e) r⟩] ++
      (if hasRefund (mkInfo c e) r then [(⟨msgId K_RID r, ridBytes (mkInfo c e) r⟩ : Msg)] else [])) ≤
      105 * (mkInfo c e).nRcpt := by
    simp only [rowsL, sum_map_flatMap]
    have := Nat.mul_comm 105 (mkInfo c e).nRcpt
    refine Nat.le_trans (sum_map_le_mul _ 105 _ ?_) (by simp [this])
    intro r hr
    have hr' : r < e.rs.length := List.mem_range.1 hr
    have p1 := rowsOf_mono (peo_len hg hr')
    have p2 := leaf_len hg hr'
    have p3 := rid_len hg hr'
    have q1 : rowsOf 133 = 52 := by decide
    have q2 : rowsOf 68 = 35 := by decide
    have q3 : rowsOf 48 = 18 := by decide
    split <;> simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, p2, p3] <;> omega
  have := Nat.mul_le_mul_left 105 (show (mkInfo c e).nRcpt ≤ 256 by omega)
  simp only [rowsL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hper ⊢
  omega

theorem rcpt_msgsB : MsgsB (rcptMsgs (mkInfo c e)) := by
  have b1 := rc_len hg
  have b2 := rf_len hg
  apply msgsB_append
  · intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨toNats_lt _, by dsimp only; omega⟩
    · exact ⟨toNats_lt _, by dsimp only; omega⟩
  · apply msgsB_flatMap
    intro r hr
    have hr' : r < e.rs.length := List.mem_range.1 hr
    have p1 := peo_len hg hr'
    have p2 := leaf_len hg hr'
    have p3 := rid_len hg hr'
    apply msgsB_append
    · intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨toNats_lt _, by dsimp only; omega⟩
      · refine ⟨fun x hx => ?_, by simp only [p2]; decide⟩
        simp only [leafBytes, leBytes, List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact toNats_lt _ x hx
        · exact toNats_lt _ x hx
        · exact MrkGen.shaN_lt _ x hx
    · split
      · intro m hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        subst hm
        refine ⟨fun x hx => ?_, by simp only [p3]; decide⟩
        simp only [ridBytes, leBytes, List.mem_append] at hx
        rcases hx with (hx | hx) | hx <;> exact toNats_lt _ x hx
      · intro m hm; cases hm

/-! ## All messages -/

omit hg in
theorem msgs_eq : (bundle c e).msgs =
    nodeMsgs (mkInfo c e) ++ acctMsgs (mkInfo c e) ++ mrkMsgs (mkInfo c e) ++ rcptMsgs (mkInfo c e) := rfl

/-- **The SHA messages of a `Good`, `Small` batch are supported.** -/
theorem msgsOk (hs : Small e) : Sha.MsgsOk (shaMsgsOf c e) := by
  have hB : MsgsB (bundle c e).msgs := by
    rw [msgs_eq]
    exact msgsB_append (msgsB_append (msgsB_append (node_msgsB hg) (acct_msgsB hg))
      (mrk_msgsB _)) (rcpt_msgsB hg)
  refine ⟨?_, ?_, ?_⟩
  · intro M hM x hx
    simp only [shaMsgsOf, shaMsgs, List.mem_map] at hM
    obtain ⟨m, hm, rfl⟩ := hM
    exact (hB m hm).1 x hx
  · intro M hM
    simp only [shaMsgsOf, shaMsgs, List.mem_map] at hM
    obtain ⟨m, hm, rfl⟩ := hM
    exact (hB m hm).2
  · rw [shaMsgsOf, shaMsgs_rows, msgs_eq, rowsL_append, rowsL_append, rowsL_append]
    have h1 := node_rows (c := c) hg
    have h2 := acct_rows hg hs
    have h3 := mrk_rows (mkInfo c e) (by
      have := hg.len; have := hg.n_le; simp only [Params.maxBatch] at *
      show e.rs.length ≤ 256; omega)
    have h4 := rcpt_rows hg
    have h5 := hg.size
    have h6 := hs.dead
    simp only [Params.maxWitnessBytes, Params.maxBatch, Sha.Table.maxLog] at *
    omega

end

/-- **`ShaLocalStmt`.** -/
theorem shaLocal : ShaLocalStmt := fun c e hg hs => shaLocal_of_ok c e (msgsOk hg hs)

/-- **`ShaTrafficStmt`.** -/
theorem shaTraffic_ok : ShaTrafficStmt := fun c e hg hs => shaTraffic_of_ok c e (msgsOk hg hs)

end ZkFormal.Near.Render
