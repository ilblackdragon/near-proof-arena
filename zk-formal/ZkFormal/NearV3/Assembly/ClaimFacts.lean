import ZkFormal.NearV3.Sched.Pub.Prep

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

/-- Claim/chain guards checked by the native validator before source proofs. -/
structure ClaimGuardsV3 (k : WalkD0) : Prop where
  protocol : k.c.protocolVersion == 86
  epochs : k.c.epochs.length == 1
  epoch : let ep := k.c.epochs.headD ⟨[], 0, 0, [], []⟩
    ep.epochId == k.c.epochId && ep.protocolVersion == k.c.protocolVersion
  layout : 1 ≤ k.L.numShards ∧ k.L.numShards ≤ 64
  rs : rsGenesisParamsOk k.c.rsDataParts k.c.rsTotalParts
  segment : k.c.blocks.length ≤ 32
  txFlags : k.c.txValid.isEmpty
  epochStartLength : k.c.epochStartAfter.length == k.c.blocks.length
  epochStarts : k.c.epochStartAfter.all (· == 0)
  updates : k.c.applyFacts.all fun f => f.validatorUpdate.isNone && f.splitGate.isNone
  nonempty : !k.blks.isEmpty
  blockEpochs : k.blks.all fun b => b.hdr.epochId == k.c.epochId
  firstHash : (k.blks.map (·.hdr.hash)).headD [] == k.H.prevBlockHash
  chain : (k.blks.zip ((k.blks.map (·.hdr.hash)).drop 1)).all fun (b, h) => b.hdr.prevHash == h
  slots : k.blks.all fun b => b.slots.length == k.L.numShards
  heights : k.blks.all fun b => b.slots.all fun (sl, _) => sl.heightIncluded ≤ b.hdr.height
  genesis : ∀ b, k.blks[k.b2i]? = some b → !b.isGenesis
  genesisExtra : k.c.genesisChunkExtra.isNone
  stop : k.stop + 1 == k.blks.length
  applyCount : k.c.applyFacts.length == 1 + k.implicitBlks.length

private theorem mapError_ok_iff {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
theorem prepClaim_guards {cb : Bytes} {pc : PrepC} {k : WalkD0}
    (hp : prepClaim cb = .ok pc) (hw : walkD0 cb = .ok k) : ClaimGuardsV3 k := by
  unfold prepClaim at hp
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok hp; clear hp; have hp := hn; clear hn)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    simp_all only [mapError_ok_iff, pure, Except.pure, Except.ok.injEq]
    unfold walkD0 at hw
    simp only [*, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hw
    repeat' (first
      | (have hh := hw; clear hw; obtain ⟨_, _, hw⟩ := bind_ok hh; clear hh)
      | (split at hw)
      | (dsimp only at hw))
    all_goals try (cases hw; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at hw
      subst hw
      constructor <;> grind only [check_ok]

theorem prepD0_guards {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint = .ok p) (hw : walkD0 cb = .ok k) : ClaimGuardsV3 k := by
  obtain ⟨pc, hc, _⟩ := bind_ok hp
  exact prepClaim_guards hc hw

end ZkFormal.NearV3.Assembly
