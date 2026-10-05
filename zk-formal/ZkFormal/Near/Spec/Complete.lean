import ZkFormal.Near.Spec.CompleteRun
import ZkFormal.Near.Statements

/-!
# ZkFormal.Near.Spec.Complete — `good_complete : GoodCompleteStmt`

Every witness of `NearRelation` has a relational spec: `Good c (extOf c w)`.
The trie part comes from `Spec/CompleteTrie`, `Spec/CompleteWalk`,
`Spec/CompleteSize` (pruning keeps the hash, does not grow the revealed size,
records form a tree, successful `get`s are walks), the run part from
`Spec/CompleteRun` (`run_inv`).
-/

namespace ZkFormal.Near

open NearSpec NearSpec.TransferV1 Prune

theorem keysOf_short {w : Witness} (hin : w.receipts.all Receipt.inSlice = true) :
    ∀ key ∈ keysOf w, key.length < 512 := by
  intro key hk
  simp only [keysOf, List.mem_map] at hk
  obtain ⟨x, hx, rfl⟩ := hk
  have := inSlice_receiver_length (List.all_eq_true.1 hin x hx)
  rw [accountKeyPath_length]; omega

/-- Every revealed value of the pruned witness trie is the slot of a receipt. -/
theorem touched_slot (c : Claim) (w : Witness) {i : Nat} {v : Bytes}
    (h : (vl (prunedOf w))[i]? = some (some v)) :
    ∃ r, r < w.receipts.length ∧ (extOf c w).slot r = i := by
  obtain ⟨key, hk, hs⟩ := vl_prune _ _ i v h
  simp only [keysOf, List.mem_map] at hk
  obtain ⟨x, hx, rfl⟩ := hk
  obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 hx
  refine ⟨r, hr, ?_⟩
  show slotIdx (prunedOf w) (accountKeyPath ((extOf c w).rc r).receiverId) = i
  rw [rc_extOf c w hr]; exact hs

theorem walkTo_pos {ns : List NodeRec} {key : List Nat} {k : Nat} (h : WalkTo ns key k) :
    0 < ns.length := by
  obtain ⟨_, _, hs⟩ := h
  cases hs <;> exact Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_of_getElem? (by assumption))

/-- **Completeness of the relational spec.** -/
theorem good_complete : GoodCompleteStmt := by
  intro c w hrel
  obtain ⟨hstat, hrc, hpre, hout⟩ := hrel
  obtain ⟨_, hpv, hchain, hlen, hn1, hn2, hgas, hin, hnd, htwf, hrev⟩ := hstat
  cases hrun : runBatch c.ctx w.trie w.receipts with
  | none => rw [hrun] at hout; cases hout
  | some fin =>
  rw [hrun] at hout
  simp only [Option.map_some, Option.some.injEq, Outputs.ofAcc, Outputs.ofClaim,
    Outputs.mk.injEq] at hout
  obtain ⟨hpost, hor, hrfc, hrfcm, hgasb, htok⟩ := hout
  obtain ⟨hall, hfin⟩ := run_inv c w w.receipts.length 0 _ fin (by simp) (inv_zero c w)
    (by simpa [runBatch] using hrun)
  have hn : 0 < w.receipts.length := by omega
  have hpos : 0 < cnt (prunedOf w) := by
    have := walkTo_pos (hall 0 (Nat.le_refl _) hn).2.1
    simpa [extOf, recs_length] using this
  -- values of touched slots
  have hval : ∀ (i : Nat) (v : Bytes), (vl (prunedOf w))[i]? = some (some v) →
      (extOf c w).vals0 i = v ∧ (Account.decode ((extOf c w).vals0 i)).isSome = true := by
    intro i v h
    refine ⟨by show valsOfList _ i = v; simp only [valsOfList, h], ?_⟩
    obtain ⟨r, hr, rfl⟩ := touched_slot c w h
    exact (hall r (Nat.zero_le _) hr).2.2
  have hlen72 : ∀ (i : Nat) (v : Bytes), (vl (prunedOf w))[i]? = some (some v) → 72 ≤ v.length := by
    intro i v h
    obtain ⟨h1, h2⟩ := hval i v h
    obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1 h2
    have := (decode_some hA).1
    rw [h1] at this; omega
  refine
    { pv := hpv, chain := hchain, n_pos := hn1, n_le := hn2, gas_limit := hgas, gas_total := ?_,
      len := hlen, inSlice := hin, nodup := hnd, rcCommit := hrc,
      shape := treeShape_recs _ hpos,
      nodes_wf := prune_recs_wf _ _ 0 htwf (keysOf_short hin),
      vals_len := ?_, vals_v1 := ?_, preRoot := ?_, size := ?_,
      walks := fun r hr => (hall r (Nat.zero_le _) hr).2.1,
      rcpt_ok := fun r hr => (hall r (Nat.zero_le _) hr).1,
      postRoot := ?_, outRoot := ?_, refundCount := ?_, rfCommit := ?_, tokens := ?_ }
  · rw [← hgasb, hfin.gas, hlen]
  · intro k nr hk ht
    obtain ⟨v, hv⟩ := recs_touched _ 0 k nr hk ht
    obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1 (hval k v hv).2
    exact (decode_some hA).1
  · intro k nr hk ht
    obtain ⟨v, hv⟩ := recs_touched _ 0 k nr hk ht
    exact (hval k v hv).2
  · show (trieOf (recs (prunedOf w) 0) (valsOfList (vl (prunedOf w)))).hashOf = c.preStateRoot
    rw [trieOf_recs _ _ hpos (fun i v h => by simp only [valsOfList, h]), prunedOf, prune_hashOf, hpre]
  · show revealedOf (recs (prunedOf w) 0) ≤ Params.maxWitnessBytes
    have h1 := revealedOf_recs (prunedOf w) 0 (prune_wf _ _ htwf) hlen72
    have h2 := prune_revealed (keysOf w) w.trie
    simp only [prunedOf] at h1 ⊢
    omega
  · show (trieOf (recs (prunedOf w) 0) ((extOf c w).valsAt w.receipts.length)).hashOf = c.slicePostRoot
    rw [← hfin.same.recs 0, trieOf_recs _ _ (by rw [hfin.same.cnt]; exact hpos), prune_hashOf, hpost]
    intro i v h
    obtain ⟨v0, h0⟩ := hfin.mask i v h
    obtain ⟨r, hr, hs⟩ := touched_slot c w h0
    exact ((hfin.prev i v h ⟨r, hr, hs⟩).1).symm
  · show outcomeRoot ((List.range w.receipts.length).map ((extOf c w).outcomeOf c)) = c.outcomeRoot
    rw [← hfin.outcomes, hor]
  · show ((List.range w.receipts.length).flatMap ((extOf c w).refundOf c)).length = c.refundCount
    rw [← hfin.refunds, hrfc]
  · show refundsCommitment ((List.range w.receipts.length).flatMap ((extOf c w).refundOf c)) =
      c.refundsCommitment
    rw [← hfin.refunds, hrfcm]
  · show (extOf c w).tokAt c w.receipts.length = c.tokensBurntTotal
    rw [← hfin.tok, htok]

end ZkFormal.Near
