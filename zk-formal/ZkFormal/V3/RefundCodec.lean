import ZkFormal.V3.EncodeWitness
import NearSpecV3.PrepD0

/-!
# The hint body codec: refund receipts

`NearSpecV3.prepBody` parses the hint body `B = u32 0 ‖ encodeReceipts refunds` with
`decodeBody` / `pRefund`. Here:

* `pRefund_encode`: `pRefund` inverts `Receipt.encode` on refund-shaped receipts
  (`refundShape r = r.wf && r.predecessorId == AccountId.system`), for any trailing bytes;
* `decodeBody_bodyOf`: `decodeBody (bodyOf rs) = .ok rs` for refund-shaped `rs`
  (fewer than 2³² of them);
* the refund invariant: every refund the D0 main application produces is refund-shaped
  (`applyReceipt_refunds_shape`, `applyReceipts_refunds_shape`,
  `applyNewChunk_refunds_shape`), at most one per receipt (`applyNewChunk_outgoing_length`);
  hence `decodeBody_outgoing`: prep's refund list is exactly `out.outgoing` (= `acc.refunds`);
* `pReceipt_wf`: receipts decoded from the witness are `wf`.
-/

namespace ZkFormal.V3

open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0

/-- What `pRefund` accepts (exactly): a well-formed receipt from `system`. -/
def refundShape (r : Receipt) : Bool := r.wf && r.predecessorId == AccountId.system

/-! ## Codec -/

theorem pRefund_encode (r : Receipt) (h : refundShape r = true) (rest : Bytes) :
    pRefund (r.encode ++ rest) = .ok (r, rest) := by
  obtain ⟨pred, recv, rid, signer, pk, gp, dep⟩ := r
  simp only [refundShape, Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  subst h8
  have hk : pk.tag ≠ 2 := by
    simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h4; omega
  have e0 : ([0] : Bytes) = u8 0 := rfl
  have e3 : ([3] : Bytes) = u8 3 := rfl
  simp only [Receipt.encode, e0, e3, List.append_assoc]
  simp only [pRefund, pAccountId_ok _ _ _ h1, bind, Except.bind,
    Bool.false_eq_true, ↓reduceIte, pAccountId_ok _ _ _ h2,
    pHash_ok _ _ _ h5, pU8_ok _ _ _ (by decide : (0:Nat) < 256), bne_self_eq_false,
    pAccountId_ok _ _ _ h3, pPublicKey_ok _ _ _ (pkWf3_of_wf _ h4),
    pU128_ok _ _ _ h6, pU32_ok _ _ _ (by decide : (0:Nat) < 4294967296),
    pU32_ok _ _ _ (by decide : (1:Nat) < 4294967296),
    pU8_ok _ _ _ (by decide : (3:Nat) < 256), pU128_ok _ _ _ h7,
    beq_iff_eq, hk, pure, Except.pure]

theorem decodeBody_bodyOf (rs : List Receipt) (h : ∀ r ∈ rs, refundShape r = true)
    (hn : rs.length < 4294967296) : decodeBody (bodyOf rs) = .ok rs := by
  have hv := pVec_ok "refunds" pRefund Receipt.encode rs [] hn
    (fun r hr rest => pRefund_encode r (h r hr) rest)
  simp only [encList, List.append_nil] at hv
  simp only [decodeBody, bodyOf, encodeReceipts, pU32_ok _ _ _ (by decide : (0:Nat) < 4294967296),
    bind, Except.bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hv, List.isEmpty_nil,
    Bool.not_true, pure, Except.pure]

/-! ## The refund invariant of the D0 runtime -/

theorem gasRefundReceipt_shape (parent : Receipt) (height refund : Nat) (hp : parent.wf = true)
    (hr : refund < Params.two128) : refundShape (gasRefundReceipt parent height refund) = true := by
  have hsys : AccountId.valid AccountId.system = true := by decide
  have h0 : 0 < Params.two128 := by decide
  simp only [Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  simp only [refundShape, Receipt.wf, gasRefundReceipt, receiptIdFrom, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, ArenaCore.sha256_length, hp, hr, hsys, h0, and_true]

theorem applyReceipt_refunds_shape {ctx : Ctx} {st st' : Acc} {r : Receipt}
    (h : applyReceipt ctx st r = some st') (hr : r.wf = true) :
    ∃ l : List Receipt, st'.refunds = st.refunds ++ l ∧ l.length ≤ 1 ∧
      ∀ x ∈ l, refundShape x = true := by
  unfold applyReceipt at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hle
  split at h
  · cases h
  rename_i hb
  split at h
  · cases h
  split at h
  · cases h
  cases h
  refine ⟨_, rfl, ?_, ?_⟩
  · split <;> simp
  · intro x hx
    split at hx
    · simp at hx
    · simp only [List.mem_singleton] at hx
      subst hx
      apply gasRefundReceipt_shape _ _ _ hr
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hb
      exact Nat.lt_of_not_le hb.2

theorem applySystemReceipt_refunds {st st' : Acc} {r : Receipt}
    (h : applySystemReceipt st r = .ok st') : st'.refunds = st.refunds := by
  unfold applySystemReceipt at h
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h
  repeat' (first | (cases h; done) | split at h)
  all_goals (cases h; rfl)

theorem applyReceipts_refunds_shape (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (acc : Acc) (ls : List Limit) (out : Acc × List Limit),
      applyReceipts ctx i (acc, ls) rs = .ok out → (∀ r ∈ rs, r.wf = true) →
      (∀ x ∈ acc.refunds, refundShape x = true) →
      (∀ x ∈ out.1.refunds, refundShape x = true) ∧
        out.1.refunds.length ≤ acc.refunds.length + rs.length
  | [], i, acc, ls, out, h, _, hacc => by
    simp only [applyReceipts, Except.ok.injEq] at h
    subst h
    exact ⟨hacc, by simp⟩
  | r :: rs, i, acc, ls, out, h, hw, hacc => by
    have hwr : r.wf = true := hw r List.mem_cons_self
    have hws : ∀ r ∈ rs, r.wf = true := fun r' hr' => hw r' (List.mem_cons_of_mem _ hr')
    simp only [applyReceipts] at h
    split at h
    · cases h
    split at h
    · obtain ⟨acc', h1, h⟩ := bind_ok' h
      have e := applySystemReceipt_refunds h1
      have ih := applyReceipts_refunds_shape ctx rs (i + 1) acc' ls out h hws (by rw [e]; exact hacc)
      rw [e] at ih
      exact ⟨ih.1, by simp only [List.length_cons] at *; omega⟩
    · split at h
      · split at h <;> cases h
      · rename_i acc' ha
        obtain ⟨ls', -, h⟩ := bind_ok' h
        obtain ⟨l, el, hl1, hl⟩ := applyReceipt_refunds_shape ha hwr
        have hacc' : ∀ x ∈ acc'.refunds, refundShape x = true := by
          intro x hx
          rw [el, List.mem_append] at hx
          rcases hx with hx | hx
          · exact hacc x hx
          · exact hl x hx
        have ih := applyReceipts_refunds_shape ctx rs (i + 1) acc' ls' out h hws hacc'
        refine ⟨ih.1, ?_⟩
        have := ih.2
        rw [el, List.length_append] at this
        simp only [List.length_cons]
        omega

theorem applyNewChunk_outgoing (prims : Prims) (ctx : ApplyCtx) (t : PTrie) (rs : List Receipt)
    (out : MainOut) (h : applyNewChunk prims ctx t rs = .ok out) :
    ∃ t0 ls out', applyReceipts ctx 0 (⟨t0, [], [], 0, 0⟩, ls) rs = .ok out' ∧
      out.outgoing = out'.1.refunds := by
  unfold applyNewChunk at h
  obtain ⟨_, -, h⟩ := bind_ok' h
  obtain ⟨_, -, h⟩ := bind_ok' h
  obtain ⟨⟨t1, so⟩, -, h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_ok' h
  obtain ⟨_, -, h⟩ := bind_ok' h
  obtain ⟨_, -, h⟩ := bind_ok' h
  obtain ⟨⟨acc, ls⟩, ha, h⟩ := bind_ok' h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_ok' h
  obtain ⟨_, -, h⟩ := bind_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨_, _, _, ha, rfl⟩

theorem applyNewChunk_refunds_shape (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (rs : List Receipt) (out : MainOut) (h : applyNewChunk prims ctx t rs = .ok out)
    (hw : ∀ r ∈ rs, r.wf = true) : ∀ x ∈ out.outgoing, refundShape x = true := by
  obtain ⟨t0, ls, out', ha, e⟩ := applyNewChunk_outgoing prims ctx t rs out h
  rw [e]
  exact (applyReceipts_refunds_shape ctx rs 0 _ ls out' ha hw (by simp)).1

theorem applyNewChunk_outgoing_length (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (rs : List Receipt) (out : MainOut) (h : applyNewChunk prims ctx t rs = .ok out)
    (hw : ∀ r ∈ rs, r.wf = true) : out.outgoing.length ≤ rs.length := by
  obtain ⟨t0, ls, out', ha, e⟩ := applyNewChunk_outgoing prims ctx t rs out h
  rw [e]
  have := (applyReceipts_refunds_shape ctx rs 0 _ ls out' ha hw (by simp)).2
  simpa using this

/-- **Prep's refund list is `out.outgoing`.** -/
theorem decodeBody_outgoing (prims : Prims) (ctx : ApplyCtx) (t : PTrie) (rs : List Receipt)
    (out : MainOut) (h : applyNewChunk prims ctx t rs = .ok out) (hw : ∀ r ∈ rs, r.wf = true)
    (hn : rs.length < 4294967296) : decodeBody (bodyOf out.outgoing) = .ok out.outgoing :=
  decodeBody_bodyOf _ (applyNewChunk_refunds_shape prims ctx t rs out h hw)
    (Nat.lt_of_le_of_lt (applyNewChunk_outgoing_length prims ctx t rs out h hw) hn)

/-! ## Receipts decoded from the witness are well-formed -/

theorem pU128_lt {w : String} {bs r : Bytes} {v : Nat} (h : pU128 w bs = .ok (v, r)) :
    v < Params.two128 := by
  have := (lift_readLE_inv (n := 16) h).2
  simpa [Params.two128] using this

theorem pHash_len {w : String} {bs v r : Bytes} (h : pHash w bs = .ok (v, r)) : v.length = 32 := by
  unfold pHash lift at h
  split at h
  · rename_i r0 hr
    cases h
    exact takeN_length_of hr
  · cases h
where
  takeN_length_of : ∀ {n : Nat} {bs v r : Bytes}, takeN n bs = some (v, r) → v.length = n
    | 0, _, _, _, h => by simp only [takeN, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
    | _ + 1, [], _, _, h => by simp [takeN] at h
    | n + 1, b :: bs, v, r, h => by
      simp only [takeN, Option.map_eq_some_iff] at h
      obtain ⟨⟨v', r'⟩, h', he⟩ := h
      simp only [Prod.mk.injEq] at he
      rw [← he.1, List.length_cons, takeN_length_of h']

theorem pAccountId_valid {w : String} {bs v r : Bytes} (h : pAccountId w bs = .ok (v, r)) :
    AccountId.valid v = true := by
  unfold pAccountId at h
  obtain ⟨⟨a, b⟩, -, h⟩ := bind_ok' h
  dsimp only at h
  split at h
  · rename_i hv; cases h; exact hv
  · cases h

theorem takeAcc_len : ∀ (n : Nat) (acc bs v r : List UInt8),
    takeAcc n acc bs = some (v, r) → v.length = acc.length + n
  | 0, acc, bs, v, r, h => by
    simp only [takeAcc, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, revAppend_eq]; simp
  | _ + 1, _, [], _, _, h => by simp [takeAcc] at h
  | n + 1, acc, b :: bs, v, r, h => by
    simp only [takeAcc] at h
    rw [takeAcc_len n _ _ _ _ h, List.length_cons]; omega

theorem pTake_len {n : Nat} {w : String} {bs v r : Bytes} (h : pTake n w bs = .ok (v, r)) :
    v.length = n := by
  unfold pTake lift at h
  split at h
  · rename_i r0 hr
    cases h
    have := takeAcc_len n [] bs _ _ hr
    simpa using this
  · cases h

theorem pPublicKey_wf {w : String} {bs r : Bytes} {k : PublicKey}
    (h : pPublicKey w bs = .ok (k, r)) (h2 : k.tag ≠ 2) : k.wf = true := by
  unfold pPublicKey at h
  obtain ⟨⟨t, b⟩, -, h⟩ := bind_ok' h
  dsimp only at h
  split at h
  all_goals simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
    Except.pure] at h
  all_goals (try split at h)
  all_goals (try (cases h; done))
  all_goals (rename_i v hv; obtain ⟨d, b'⟩ := v; cases h)
  all_goals first
    | exact absurd rfl h2
    | simp only [PublicKey.wf, pTake_len hv, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]; decide

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : ite c a b = a := by
  simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : ite c a b = b := by
  simp [h]

/-- Receipts decoded by the witness decoder are well-formed. -/
theorem pReceipt_wf {bs rest : Bytes} {r : Receipt} (h : pReceipt bs = .ok (r, rest)) :
    r.wf = true := by
  unfold pReceipt at h
  obtain ⟨⟨pred, b1⟩, h1, h⟩ := bind_ok' h
  obtain ⟨⟨recv, b2⟩, h2, h⟩ := bind_ok' h
  obtain ⟨⟨rid, b3⟩, h3, h⟩ := bind_ok' h
  obtain ⟨⟨tag, b4⟩, -, h⟩ := bind_ok' h
  dsimp only at h
  by_cases c1 : (tag != 0) = true
  · rw [ite_pos' c1] at h; cases h
  rw [ite_neg' c1] at h
  obtain ⟨⟨signer, b5⟩, h5, h⟩ := bind_ok' h
  obtain ⟨⟨pk, b6⟩, h6, h⟩ := bind_ok' h
  dsimp only at h
  by_cases c2 : (pk.tag == 2) = true
  · rw [ite_pos' c2] at h; cases h
  rw [ite_neg' c2] at h
  obtain ⟨⟨gp, b7⟩, h7, h⟩ := bind_ok' h
  obtain ⟨⟨nout, b8⟩, -, h⟩ := bind_ok' h
  dsimp only at h
  by_cases c3 : (nout != 0) = true
  · rw [ite_pos' c3] at h; cases h
  rw [ite_neg' c3] at h
  obtain ⟨⟨nin, b9⟩, -, h⟩ := bind_ok' h
  dsimp only at h
  by_cases c4 : (nin != 0) = true
  · rw [ite_pos' c4] at h; cases h
  rw [ite_neg' c4] at h
  obtain ⟨⟨nact, b10⟩, -, h⟩ := bind_ok' h
  dsimp only at h
  by_cases c5 : (nact != 1) = true
  · rw [ite_pos' c5] at h; cases h
  rw [ite_neg' c5] at h
  obtain ⟨⟨atag, b11⟩, -, h⟩ := bind_ok' h
  dsimp only at h
  by_cases c6 : (atag != 3) = true
  · rw [ite_pos' c6] at h; cases h
  rw [ite_neg' c6] at h
  obtain ⟨⟨dep, b12⟩, h12, h⟩ := bind_ok' h
  dsimp only at h
  by_cases c7 : (!AccountId.isNamed recv) = true
  · rw [ite_pos' c7] at h; cases h
  rw [ite_neg' c7] at h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hk : pk.tag ≠ 2 := fun e => c2 (by rw [e]; rfl)
  simp only [Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨pAccountId_valid h1, pAccountId_valid h2⟩, pAccountId_valid h5⟩,
    pPublicKey_wf h6 hk⟩, pHash_len h3⟩, pU128_lt h7⟩, pU128_lt h12⟩

end ZkFormal.V3
