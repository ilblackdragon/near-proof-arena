import ZkFormal.NearV3.Assembly.NativeClaim
import ZkFormal.NearV3.Assembly.PreparedSourcesComplete
import ZkFormal.NearV3.Assembly.SchedulerPublicComplete

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched Rcpt.Candidates

set_option maxHeartbeats 4000000 in
theorem prepClaim_exists {cb : Bytes} {k : WalkD0} {m : MainExecutionV3} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hm : m.NativeValid k w) (hg : ClaimGuardsV3 k)
    (ha1 : k.slotB2.gasLimit ≤ maxGasLimitD0)
    (ha8 : k.blks.all (fun b => b.slots.all fun (_,ci) => decide (ci.bwRequests.map (·.toShard)).Nodup) = true)
    (ht : k.slotB2.txRoot = zeroHash32)
    (hc : (k.slotB2.congestion.delayedGas == 0 && k.slotB2.congestion.bufferedGas == 0 &&
      k.slotB2.congestion.receiptBytes == 0) = true)
    (hs : ∃ lists, preparedSourceLists k.sourceBlks = .ok lists) :
    ∃ pc, prepClaim cb = .ok pc := by
  obtain ⟨lists,hs⟩ := hs
  have hb := hm.block
  have hp := hm.previous
  have hgen := hg.genesis m.block hb
  obtain ⟨sched,hsch⟩ := schedPub_mapM_exists
    (blockCtx k.L k.H.shardId k.slotB2.gasLimit m.block m.previous.hdr.nextGasPrice ::
      k.implicitBlks.map (fun b => blockCtx k.L k.H.shardId k.slotB2.gasLimit b b.hdr.nextGasPrice))
    (by intro ctx hctx; simp only [List.mem_cons,List.mem_map] at hctx
        rcases hctx with rfl | ⟨b,_,rfl⟩ <;> exact hg.layout.1)
  rcases hg with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,_,h18,h19,h20⟩
  unfold walkD0 at hk
  repeat' (first
    | (have hh := hk; clear hk; obtain ⟨_, _, hk⟩ := bind_ok hh; clear hh)
    | (split at hk)
    | (dsimp only at hk))
  all_goals try (cases hk; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure,Except.pure,Except.ok.injEq] at hk
    subst hk
    simp_all only [pure,Except.pure,Except.ok.injEq]
    expose_names
    have hslot : m.block.slots[w_5]? = some p := by
      simpa only [hb,Option.bind_some] using heq_3

    unfold preparedSourceLists slotSources at hs
    simp only [pure,Except.pure,bind,Except.bind] at hs hsch
    unfold prepClaim
    simp only [*, Except.mapError,check,bind,Except.bind,pure,Except.pure,
      beq_self_eq_true,decide_eq_true_eq,decide_true,Bool.true_and,↓reduceIte]
    split
    · rename_i i hf
      have hi : i = w_6 := by grind only
      subst i
      have hgen' : (!m.block.isGenesis) = true := genesis _ rfl
      simp only [*,check,bind,Except.bind,pure,Except.pure,↓reduceIte]
      split
      · rename_i j hf2
        have hj : j = i_2 := by grind only
        subst j
        simp only [*,check,bind,Except.bind,pure,Except.pure,decide_true,Bool.true_and,beq_self_eq_true,↓reduceIte]
        split
        · exfalso; grind only
        · rename_i out hout
          have he : out = lists := by grind only
          subst out
          split
          · exfalso; grind only
          · exact ⟨_,rfl⟩
      · exfalso; grind only
    · exfalso; grind only

theorem checkD0a_prepClaim_exists {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w)
    (h : checkD0a B cb wb = .ok ()) : ∃ pc, prepClaim cb = .ok pc := by
  have hr := (relD0a_iff B cb wb).mpr h
  have ha1 : k.slotB2.gasLimit ≤ maxGasLimitD0 := by
    simpa only [a1,hk,decide_eq_true_eq] using hr.2.1
  have ha8 : k.blks.all (fun b => b.slots.all fun (_,ci) =>
      decide (ci.bwRequests.map (·.toShard)).Nodup) = true := by
    simpa only [a8,hk] using hr.2.2.2.2.2.1
  unfold checkD0a at h
  obtain ⟨u,hu,_⟩ := ReexecV3D0.bind_ok' h
  cases u
  obtain ⟨m,last,hm,_⟩ := checkD0_native_steps hk hw hu
  obtain ⟨hg,ht,hc⟩ := checkD0_claim_guards hk hw hu
  exact prepClaim_exists hk hm hg ha1 ha8 ht hc (checkD0_prepared_sources hk hw hu)

end ZkFormal.NearV3.Assembly
