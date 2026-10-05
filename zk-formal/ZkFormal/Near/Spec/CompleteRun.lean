import ZkFormal.Near.Spec.CompleteSize
import ZkFormal.Near.Spec.CompleteAcct

/-!
# ZkFormal.Near.Spec.CompleteRun — a successful `runBatch` in flat form

`RunInv c w r st` relates the accumulator after the first `r` receipts to the
records `extOf c w`: outcomes, refunds, gas and tokens are the flat ones, the
pruned current trie has the records of the pruned witness trie, and its
revealed values are the flat `valsAt r` (slots already written) or `vals0`
(slots not yet written).  `step` advances it by one receipt and yields
`RcptOk` and the receipt's walk; `run_inv` iterates it over the batch.
-/

namespace ZkFormal.Near.Prune

open NearSpec NearSpec.TransferV1

/-- What a successful `applyReceipt` did. -/
theorem applyReceipt_some {ctx : Ctx} {st st' : Acc} {r : Receipt}
    (h : applyReceipt ctx st r = some st') :
    ∃ raw a t', st.trie.get (accountKeyPath r.receiverId) = some raw ∧
      Account.decode raw = some a ∧
      a.amount + r.deposit < Params.u128Max ∧
      a.amount + r.deposit + a.locked < Params.two128 ∧
      (Params.storageAmountPerByte * a.storageUsage ≤ a.amount + r.deposit + a.locked ∨
        a.storageUsage ≤ Params.zeroBalanceStorageLimit) ∧
      Params.G * min r.gasPrice ctx.blockGasPrice < Params.two128 ∧
      Params.G * (r.gasPrice - min r.gasPrice ctx.blockGasPrice) < Params.two128 ∧
      st.tokensBurnt + Params.G * min r.gasPrice ctx.blockGasPrice < Params.two128 ∧
      st.trie.set (accountKeyPath r.receiverId) (Account.encode { a with amount := a.amount + r.deposit })
        = some t' ∧
      st' = { trie := t'
              outcomes := st.outcomes ++
                [{ id := r.receiptId,
                   receiptIds := (if Params.G * (r.gasPrice - min r.gasPrice ctx.blockGasPrice) = 0
                     then [] else [gasRefundReceipt r ctx.blockHeight
                       (Params.G * (r.gasPrice - min r.gasPrice ctx.blockGasPrice))]).map
                     Receipt.receiptId,
                   gasBurnt := Params.G, tokensBurnt := Params.G * min r.gasPrice ctx.blockGasPrice,
                   executorId := r.receiverId }]
              refunds := st.refunds ++
                (if Params.G * (r.gasPrice - min r.gasPrice ctx.blockGasPrice) = 0 then []
                 else [gasRefundReceipt r ctx.blockHeight
                   (Params.G * (r.gasPrice - min r.gasPrice ctx.blockGasPrice))])
              gasBurnt := st.gasBurnt + Params.G
              tokensBurnt := st.tokensBurnt + Params.G * min r.gasPrice ctx.blockGasPrice } := by
  cases hg : st.trie.get (accountKeyPath r.receiverId) with
  | none => simp [applyReceipt, hg] at h
  | some raw =>
    cases hd : Account.decode raw with
    | none => simp [applyReceipt, hg, hd] at h
    | some a =>
      simp only [applyReceipt, hg, hd] at h
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
      split at h
      · cases h
      rename_i h0 h1 h2 h3 h4 _ t' hs
      refine ⟨raw, a, t', by first | rfl | assumption, by first | rfl | assumption, by omega, by omega, ?_, ?_, ?_, by omega, hs, ?_⟩
      · simp at h2; omega
      · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h3; omega
      · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h3; omega
      · exact (Option.some.inj h).symm

section
variable (c : Claim) (w : Witness)

/-- The run invariant after the first `r` receipts. -/
structure RunInv (r : Nat) (st : Acc) : Prop where
  outcomes : st.outcomes = (List.range r).map ((extOf c w).outcomeOf c)
  refunds : st.refunds = (List.range r).flatMap ((extOf c w).refundOf c)
  gas : st.gasBurnt = r * Params.G
  tok : st.tokensBurnt = (extOf c w).tokAt c r
  same : Same (prunedOf w) (prune (keysOf w) st.trie)
  mask : ∀ (i : Nat) (v : Bytes), (vl (prune (keysOf w) st.trie))[i]? = some (some v) →
    ∃ v0, (vl (prunedOf w))[i]? = some (some v0)
  prev : ∀ (i : Nat) (v : Bytes), (vl (prune (keysOf w) st.trie))[i]? = some (some v) →
    (∃ r', r' < r ∧ (extOf c w).slot r' = i) →
    v = (extOf c w).valsAt r i ∧ (extOf c w).amtAt i r < Params.u128Max ∧
      (Account.decode ((extOf c w).vals0 i)).isSome = true
  fresh : ∀ (i : Nat) (v : Bytes), (vl (prune (keysOf w) st.trie))[i]? = some (some v) →
    (∀ r', r' < r → (extOf c w).slot r' ≠ i) → v = (extOf c w).vals0 i

theorem rc_extOf {r : Nat} (hr : r < w.receipts.length) : (extOf c w).rc r = w.receipts[r] := by
  simp [Ext.rc, extOf, List.getD_eq_getElem?_getD, hr]

theorem key_mem {r : Nat} (hr : r < w.receipts.length) :
    accountKeyPath ((extOf c w).rc r).receiverId ∈ keysOf w := by
  rw [rc_extOf c w hr]
  simp only [keysOf, List.mem_map]
  exact ⟨w.receipts[r], List.getElem_mem hr, rfl⟩

theorem inv_zero : RunInv c w 0 ⟨w.trie, [], [], 0, 0⟩ where
  outcomes := rfl
  refunds := rfl
  gas := by simp
  tok := rfl
  same := Same.refl _
  mask := fun i v h => ⟨v, h⟩
  prev := fun _ _ _ ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)
  fresh := fun i v h _ => by
    show v = valsOfList (vl (prunedOf w)) i
    simp only [valsOfList]; rw [show (vl (prunedOf w))[i]? = some (some v) from h]

/-- The slot a receipt's account value has in a decodable form. -/
theorem slot_acct {r : Nat} {st : Acc} (hinv : RunInv c w r st) {raw : Bytes} {a : Account}
    (hvl : (vl (prune (keysOf w) st.trie))[(extOf c w).slot r]? = some (some raw))
    (hd : Account.decode raw = some a) :
    a = { (extOf c w).acc0 ((extOf c w).slot r) with
          amount := (extOf c w).amtAt ((extOf c w).slot r) r } ∧
      (Account.decode ((extOf c w).vals0 ((extOf c w).slot r))).isSome = true := by
  by_cases hp : ∃ r', r' < r ∧ (extOf c w).slot r' = (extOf c w).slot r
  · obtain ⟨hv, hamt, hdec⟩ := hinv.prev _ raw hvl hp
    obtain ⟨A0, hA0⟩ := Option.isSome_iff_exists.1 hdec
    have hacc : (extOf c w).acc0 ((extOf c w).slot r) = A0 := by simp [Ext.acc0, hA0]
    obtain ⟨-, -, hl, hch, hsu⟩ := decode_some hA0
    rw [hv] at hd
    simp only [Ext.valsAt] at hd
    rw [hacc, decode_encode { A0 with amount := _ } hamt hl hch hsu] at hd
    exact ⟨by rw [hacc]; exact (Option.some.inj hd).symm, hdec⟩
  · have hf : ∀ r', r' < r → (extOf c w).slot r' ≠ (extOf c w).slot r :=
      fun r' h1 h2 => hp ⟨r', h1, h2⟩
    have hv := hinv.fresh _ raw hvl hf
    rw [hv] at hd
    have hacc : (extOf c w).acc0 ((extOf c w).slot r) = a := by simp [Ext.acc0, hd]
    refine ⟨?_, by simp [hd]⟩
    rw [amtAt_fresh _ _ r hf, hacc]

/-- One receipt. -/
theorem step {r : Nat} (hr : r < w.receipts.length) {st st' : Acc} (hinv : RunInv c w r st)
    (happ : applyReceipt c.ctx st ((extOf c w).rc r) = some st') :
    RcptOk c (extOf c w) r ∧
      WalkTo (extOf c w).ns (accountKeyPath ((extOf c w).rc r).receiverId) ((extOf c w).slot r) ∧
      (Account.decode ((extOf c w).vals0 ((extOf c w).slot r))).isSome = true ∧
      RunInv c w (r + 1) st' := by
  obtain ⟨raw, a, t', hg, hd, c1, c2, c3, c4, c5, c6, hs, rfl⟩ := applyReceipt_some happ
  have hmem := key_mem c w hr
  have hslot : slotIdx (prune (keysOf w) st.trie) (accountKeyPath ((extOf c w).rc r).receiverId) =
      (extOf c w).slot r := hinv.same.slot _
  have hq : (prune (keysOf w) st.trie).get (accountKeyPath ((extOf c w).rc r).receiverId) = some raw :=
    (prune_get _ _ _ hmem).trans hg
  have hvl := get_vl _ _ _ hq
  rw [hslot] at hvl
  have hwalk := walkTo_recs _ _ _ (accountKeyPath_lt _) hq
  rw [hslot, hinv.same.recs 0] at hwalk
  obtain ⟨rfl, hdec⟩ := slot_acct c w hinv hvl hd
  have hq' := prune_set _ _ _ _ _ hmem hs
  obtain ⟨hS', -, hvl'⟩ := set_same _ _ _ _ hq'
  rw [hslot] at hvl'
  refine ⟨⟨c1, c2, c3, c4, c5, by rw [← hinv.tok]; exact c6⟩, hwalk, hdec, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, hinv.same.trans hS', ?_, ?_, ?_⟩
  · simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, hinv.outcomes]; rfl
  · simp only [List.range_succ, List.flatMap_append, hinv.refunds, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rfl
  · simp only [hinv.gas, Nat.succ_mul]
  · simp only [hinv.tok]; rfl
  · intro i v h
    rw [hvl', List.getElem?_set] at h
    split at h
    · rename_i hi; subst hi; exact hinv.mask _ raw hvl
    · exact hinv.mask i v h
  · intro i v h hp
    rw [hvl', List.getElem?_set] at h
    split at h
    · rename_i hi; subst hi
      split at h
      · simp only [Option.some.injEq] at h; subst h
        refine ⟨?_, ?_, hdec⟩
        · simp only [Ext.valsAt, amtAt_succ_self]
        · rw [amtAt_succ_self]; exact c1
      · cases h
    · rename_i hi
      have hp' : ∃ r', r' < r ∧ (extOf c w).slot r' = i := by
        obtain ⟨r', h1, h2⟩ := hp
        refine ⟨r', ?_, h2⟩
        rcases Nat.lt_or_ge r' r with h3 | h3
        · exact h3
        · exact absurd (show r' = r by omega ▸ h2) hi
      obtain ⟨hv, hamt, hdec'⟩ := hinv.prev i v h hp'
      refine ⟨?_, ?_, hdec'⟩
      · rw [hv]; simp only [Ext.valsAt, amtAt_succ_other _ _ _ hi]
      · rw [amtAt_succ_other _ _ _ hi]; exact hamt
  · intro i v h hf
    rw [hvl', List.getElem?_set] at h
    split at h
    · rename_i hi; exact absurd hi (hf r (Nat.lt_succ_self r))
    · exact hinv.fresh i v h (fun r' h1 => hf r' (by omega))

/-- What a receipt contributes to `Good`. -/
def RcptFacts (r : Nat) : Prop :=
  RcptOk c (extOf c w) r ∧
    WalkTo (extOf c w).ns (accountKeyPath ((extOf c w).rc r).receiverId) ((extOf c w).slot r) ∧
    (Account.decode ((extOf c w).vals0 ((extOf c w).slot r))).isSome = true

theorem run_inv : ∀ (m r : Nat) (st fin : Acc), r + m = w.receipts.length → RunInv c w r st →
    applyAll c.ctx st (w.receipts.drop r) = some fin →
    (∀ r', r ≤ r' → r' < w.receipts.length → RcptFacts c w r') ∧ RunInv c w w.receipts.length fin
  | 0, r, st, fin, hm, hinv, h => by
    have hr : r = w.receipts.length := by omega
    subst hr
    rw [List.drop_length] at h
    simp only [applyAll, Option.some.injEq] at h; subst h
    exact ⟨fun r' h1 h2 => absurd h2 (by omega), hinv⟩
  | m + 1, r, st, fin, hm, hinv, h => by
    have hr : r < w.receipts.length := by omega
    rw [List.drop_eq_getElem_cons hr] at h
    simp only [applyAll] at h
    cases ha : applyReceipt c.ctx st w.receipts[r] with
    | none => simp [ha] at h
    | some st' =>
      simp only [ha] at h
      have ha' : applyReceipt c.ctx st ((extOf c w).rc r) = some st' := by
        rw [rc_extOf c w hr]; exact ha
      obtain ⟨hok, hwalk, hdec, hinv'⟩ := step c w hr hinv ha'
      obtain ⟨hall, hfin⟩ := run_inv m (r + 1) st' fin (by omega) hinv' h
      refine ⟨fun r' h1 h2 => ?_, hfin⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact ⟨hok, hwalk, hdec⟩
      · exact hall r' h1 h2

end

end ZkFormal.Near.Prune
