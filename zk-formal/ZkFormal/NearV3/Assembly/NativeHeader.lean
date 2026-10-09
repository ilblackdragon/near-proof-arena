import ZkFormal.NearV3.Assembly.NativeMain

set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

/-- Actual endorsed-header comparisons, before choosing a preparation hint. -/
structure NativeHeaderV3 (k : WalkD0) (m : MainExecutionV3) (last : Bytes) : Prop where
  stateRoot : k.H.prevStateRoot = last
  outcomeRoot : k.H.prevOutcomeRoot = NearSpec.outcomeRoot m.result.outcomes
  proposals : k.H.proposals.isEmpty = true
  gasLimit : k.H.gasLimit = k.slotB2.gasLimit
  gasUsed : k.H.prevGasUsed = m.result.gasUsed
  tokensBurnt : k.H.prevBalanceBurnt = m.result.tokensBurnt
  outgoingRoot : k.H.prevOutgoingReceiptsRoot = outgoingReceiptsRoot k.L m.result.outgoing
  congestion : k.H.congestion = { k.slotB2.congestion with
    allowedShard := k.L.shardIds.getD ((m.block.hdr.height + k.idx) % k.L.numShards) k.H.shardId }
  bandwidthRequests : k.H.bwRequests.isEmpty = true
  split : k.H.proposedSplit.isNone = true
  txRoot : k.H.txRoot = zeroHash32
  encoded : encodedMerkleRoot k.c.rsDataParts k.c.rsTotalParts
    (u32 0 ++ encodeReceipts m.result.outgoing) = some (k.H.encodedMerkleRoot,k.H.encodedLength)

private theorem mapError_id {α : Type} (x : Except String α) : x.mapError id = x := by
  cases x <;> rfl

set_option maxHeartbeats 4000000 in
theorem checkD0_native_header {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0 cb wb = .ok ()) :
    ∃ m : MainExecutionV3, ∃ last : Bytes, m.NativeValid k w ∧
      forIn (k.implicitBlks.zip w.implicit) m.result.trie.hashOf (checkedImplicitStep k) = .ok last ∧
      w.implicit.length = k.implicitBlks.length ∧ k.implicitBlks.length ≤ 31 ∧ NativeHeaderV3 k m last := by
  unfold walkD0 at hk
  repeat' (first
    | (have hh := hk; clear hk; obtain ⟨_, _, hk⟩ := bind_ok hh; clear hh)
    | (split at hk)
    | (dsimp only at hk))
  all_goals try (cases hk; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hk
    subst hk
    unfold decodeW at hw
    obtain ⟨⟨raw, codes⟩, hfile, hw⟩ := bind_ok hw
    unfold checkD0 at h
    repeat' (first
      | (have hh := h; clear h; obtain ⟨_, _, h⟩ := bind_ok hh; clear hh)
      | (split at h)
      | (dsimp only at h))
    all_goals try (cases h; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals
      simp_all only [Except.mapError, Except.ok.injEq, Prod.mk.injEq, pure, Except.pure, Option.some.injEq]
      have hv := checkedSourceLoop_result _ _ _ _ (by assumption)
      -- Name the values returned by the frozen checker binds; congruence aligns
      -- its walk indices with the independently decoded WalkD0.
      expose_names
      have hb2 : w_6 = w_36 := by grind only
      have hslot : w_8 = w_44 := by
        rw [hb2, heq_5] at heq_3
        simp only [Option.bind_some, heq_8, Option.some.injEq] at heq_3
        grind only
      refine ⟨⟨w_37, w_43, w_52,
        partialTrie w_13.main.values w_44.prevStateRoot (mainKeys w_45.1 w_52), w_54⟩, w_57, ?_, ?_, ?_, ?_, ?_⟩
      · constructor
        · grind only
        · grind only
        · refine ⟨v, ?_, ?_⟩
          · grind only
          · have hh : (bufferedShards v).mapError id = .ok w_52 := by assumption
            simpa only [mapError_id] using hh
        · simp only [appliedReceipts_eq_flatMap]
          grind only
        · grind only [check_ok]
        · simp only [MainExecutionV3.ctx, appliedReceipts_eq_flatMap]
          grind only
        · grind only [check_ok]
        · grind only [check_ok]
      · unfold checkedImplicitStep
        simpa only [hb2, hslot, pure, Except.pure] using left_54
      · grind only [check_ok]
      · have hseg : w_9.blocks.length ≤ 32 := by
          have hh := check_ok (by assumption : check (decide (w_9.blocks.length ≤ 32)) _ = .ok _)
          simpa only [decide_eq_true_eq] using hh
        have hlen := Sched.mapM_length decodeBlk w_9.blocks w_4 (by assumption)
        have hi := (List.getElem?_eq_some_iff.mp heq_5).1
        simp only [List.length_reverse, List.length_take]
        omega

      · constructor
        all_goals dsimp only
        all_goals grind only [check_ok]

theorem MainExecutionV3.NativeValid.unique {k : WalkD0} {w : StateWitness}
    {m n : MainExecutionV3} (hm : m.NativeValid k w) (hn : n.NativeValid k w) : m = n := by
  cases m
  cases n
  cases hm
  cases hn
  rename_i hmblock hmprev hmbuf hmpre hmroot hmrun hmpost hmsize
    hnblock hnprev hnbuf hnpre hnroot hnrun hnpost hnsize
  obtain ⟨vm,hvm,hpm⟩ := hmbuf
  obtain ⟨vn,hvn,hpn⟩ := hnbuf
  dsimp only [MainExecutionV3.ctx] at *
  grind only

end ZkFormal.NearV3.Assembly
