import ZkFormal.NearV3.D1.Prep.Spec

/-!
# `ZkFormal.NearV3.D1.F1.ClaimGuards` — the claim-level checks of `checkD1` (`F1`)

Lane `v3-d1-phase2`, item F1.  D0a's `prepClaim_guards`
(`ZkFormal/NearV3/Assembly/ClaimFacts.lean`) for `prepClaimD1`, producing **`ClaimGuardsD1`**
(D0a's `ClaimGuardsV3` without its D0-only `txFlags` field, which `checkD1` also drops).

`prepD1 cb h = .ok p` yields `prepClaimD1 cb = .ok ⟨pc, txValid, txRoot⟩`
(`D1.Prep.Spec.prepD1_spec`, the `PrepD1Run.Ok.claim` field), and `walkD0 cb = .ok k` computes
the same values; every claim-level check of `prepClaimD1` is then a field of `ClaimGuardsD1`:

* **`prepClaimD1_guards`**: the `prepClaimD1` form;
* **`claimGuards_of_prepD1`**: the `prepD1` form used by `F1.CheckD1`.

Unlike D0a's proof the split hypotheses of `blks.findIdx? isNew` must not be `simp_all`ed
over the destructed claim context: they carry the `isNew` matcher application, and descending
into it generates `ZkFormal.NearV3.D1.prepClaimD1.match_7.congr_eq_*` — declarations outside
this module's namespace.  So the hypotheses that need normalising are named with
`expose_names` and simplified one by one, and the `walkD0` body is then closed by rewriting it
with those named equations.
-/

namespace ZkFormal.NearV3.D1.F1

open NearSpec NearSpecV3 ZkFormal.NearV3.D1

/-- **The claim-level checks of `checkD1`** (D0a's `ClaimGuardsV3`, minus the D0-only
`txFlags`; `checkD1` also drops `c.txValid.isEmpty`). -/
structure ClaimGuardsD1 (k : WalkD0) : Prop where
  protocol : k.c.protocolVersion == 86
  epochs : k.c.epochs.length == 1
  epoch : let ep := k.c.epochs.headD ⟨[], 0, 0, [], []⟩
    ep.epochId == k.c.epochId && ep.protocolVersion == k.c.protocolVersion
  layout : 1 ≤ k.L.numShards ∧ k.L.numShards ≤ 64
  rs : rsGenesisParamsOk k.c.rsDataParts k.c.rsTotalParts
  segment : k.c.blocks.length ≤ 32
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

open ZkFormal.NearV3.Sched

private theorem mapError_ok_iff {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
/-- `prepClaimD1`'s checks hold of the walk `walkD0` computes (the D1 twin of
`ZkFormal.NearV3.Assembly.prepClaim_guards`). -/
theorem prepClaimD1_guards {cb : Bytes} {pc : PrepC} {tv tr : Bytes} {k : WalkD0}
    (hp : prepClaimD1 cb = .ok ⟨pc, tv, tr⟩) (hw : walkD0 cb = .ok k) :
    ClaimGuardsD1 k := by
  unfold prepClaimD1 at hp
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok hp; clear hp; have hp := hn; clear hn)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    -- name the destructed values, then normalise the `mapError` / `pure` wrappers of the few
    -- hypotheses the walk side needs (never the `isNew` split hypotheses)
    expose_names
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    simp only [ZkFormal.NearV3.D1.PrepCD1.mk.injEq] at hp
    obtain ⟨hpc, -, -⟩ := hp
    subst hpc
    simp only [mapError_ok_iff, pure, Except.pure,
      Except.ok.injEq] at hs_1 hs_2 hs_20 hs_22 hs_23 hs_26 hs_29 hs_30
    subst hs_20
    subst hs_22
    subst hs_23
    subst hs_26
    subst hs_29
    subst hs_30
    -- the walk computes its fields from those same decoded values
    unfold walkD0 at hw
    simp only [hs_1, hs_2, hs_6, hs_13, heq, bind, Except.bind, pure, Except.pure] at hw
    split at hw
    · rename_i i_3 hi3
      obtain rfl : i_3 = i_1 := Option.some.inj (hi3.symm.trans heq_1)
      split at hw
      · rename_i j hj
        obtain rfl : j = i_2 := Option.some.inj (hj.symm.trans heq_3)
        simp only [heq_2, Option.bind_some, heq_5] at hw
        simp only [Except.ok.injEq] at hw
        subst hw
        constructor <;> grind only [check_ok]
      · rename_i hj
        exact absurd (hj.symm.trans heq_3) (by simp)
    · rename_i hi3
      exact absurd (hi3.symm.trans heq_1) (by simp)

/-- **`prepD1`'s claim-level checks hold of the walk.**  A successful `prepD1 cb h = .ok p`
gives `prepClaimD1 cb = .ok ⟨p.pc, p.txValid, p.txRoot⟩` (`prepD1_spec`), and `walkD0` computes
its claim fields from the same decoded values. -/
theorem claimGuards_of_prepD1 {cb : NearSpec.Bytes} {h : ZkFormal.NearV3.D1.HintD1}
    {p : ZkFormal.NearV3.D1.Public.PrepD1} {k : NearSpecV3.WalkD0}
    (hp : ZkFormal.NearV3.D1.prepD1 cb h = .ok p) (hw : NearSpecV3.walkD0 cb = .ok k) :
    ClaimGuardsD1 k := by
  obtain ⟨w, hwok, -⟩ := ZkFormal.NearV3.D1.prepD1_spec hp
  obtain ⟨pc, tv, tr, hclaim⟩ :
      ∃ (pc : NearSpecV3.PrepC) (tv tr : NearSpec.Bytes),
        ZkFormal.NearV3.D1.prepClaimD1 cb = .ok ⟨pc, tv, tr⟩ :=
    ⟨w.pc, w.txValid, w.txRoot, hwok.claim⟩
  exact prepClaimD1_guards hclaim hw
