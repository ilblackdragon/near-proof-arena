import ReexecV3D3.Obligations

set_option maxHeartbeats 1000000

/-!
# `ReexecV3D3.ArtifactSound` — the D3 soundness theorem stated against the deployed artifact

`Obligations.lean` proves the admission statement for `Model.verifier` as an
`ArenaCore.OracleVerifier`.  This module re-states that soundness in the shape the
D3 goal asks for — **"the installed verifier accepted ⇒ `D3.RelD3`"** — and records
the definitional identities the chain rests on as named, kernel-checked lemmas.

## The chain, end to end

1. `build-recipe/build.sh` installs `out/verify`, compiled from
   `Model.verifier.run` (`Model.lean:22-23`), whose body is `check`.
2. `deployed_eq` proves `Model.verifier.deployed pub cb pb = check cb pb` by `rfl`
   — the binary and the proved function are **the same function**, not two
   functions asserted equal.  That is what makes this an artifact proof and not a
   shadow proof.
3. `check_sound` (`Obligations.lean:31-37`) proves acceptance implies
   `∃ c, WfClaim.decode cb = some c ∧ WfClaim.RelTier .d3a c pb ∧
   Read.check c.encode pb = true`.
4. `WfClaim.RelTier .d3a c w` **is** `NearSpecV3.D3.RelD3 c.1.encode w` by
   definition: `RelTier` is a plain `match` whose `.d3a` branch is `D3.RelD3`
   (`ChallengeChunkV3.lean:56-63`), and `WfClaim.RelTier` is the same on
   `c.1.encode` (`:79`).  So step 3's third conjunct *is* the D3 chunk relation.
5. `rel_mono` (`:68-77`) carries the tier relation to the unified chunk statement.

## What is and is not claimed

The verifier is deterministic witness re-execution (`Model.lean:6-11`), not a
succinct proof system: `Read.check` runs `Logged.checkD3Reads` — the whole
`checkD3`, including `Wasm.prepare` and the D3 execution — and then requires byte
equality with the re-encoding of its recorded-store read set.  So **the
preparation stage is genuinely executed on the verifier side**, and acceptance is a
statement about a real run rather than a lookup in a table.  Succinctness is the
open item; soundness and binding are not.
-/

namespace ReexecV3D3

open ArenaCore NearSpecV3

/-! ## §1. The definitional identities the chain rests on -/

/-- `RelTier .d3a` unfolds to `D3.RelD3`.  The tier table is a plain `match`
(`ChallengeChunkV3.lean:56-63`), so this is definitional — no proof work, but it is
the step a reader must not have to guess. -/
theorem relTier_d3a_eq (cb w : ArenaCore.Bytes) :
    NearSpecV3.RelTier .d3a cb w = D3.RelD3 cb w := rfl

/-- The same identity on decoded claims. -/
theorem wfClaim_relTier_d3a_eq (c : WfClaim) (w : List UInt8) :
    WfClaim.RelTier .d3a c w = D3.RelD3 c.1.encode w := rfl

/-! ## §2. Acceptance implies the D3 chunk relation, on the deployed artifact -/

/-- **Artifact soundness for D3 — the honest statement.**

Acceptance implies there is a well-formed claim `c` that the *accepted bytes decode to*, and whose
canonical encoding satisfies the D3 chunk relation with the witness.  The relation is stated on
`c.1.encode`, not on `cb`, and deliberately so: `check` runs
`Read.check (WfClaim.decode cb).encode pb`, and `WfClaim.decode cb = some c` does **not** imply
`c.encode = cb` — the relation is about the decoded chunk, which is the object nearcore validates.
`Read.check_sound` closes it: acceptance gives `D3.checkD3 c.1.encode pb = .ok ()`, which *is*
`D3.RelD3 c.1.encode pb` (`D3/FunctionCall.lean:400-403`).

The previous `check_sound` in `Obligations.lean` states exactly this conjunction; this module only
gives it the `RelD3` name the D3 goal asks for. -/
theorem artifact_sound_decoded {cb pb : ArenaCore.Bytes}
    (h : Model.verifier.deployed [] cb pb = true) :
    ∃ c : WfClaim, WfClaim.decode cb = some c ∧ D3.RelD3 c.1.encode pb := by
  have hc : check cb pb = true := by rw [← deployed_eq]; exact h
  obtain ⟨c, hc', hrel, _⟩ := check_sound hc
  exact ⟨c, hc', hrel⟩

/-- **Artifact soundness on canonical claims.**  When the accepted claim bytes are already the
canonical encoding of the chunk they decode to — the case the honest prover produces and the case
`Read.check_normal` certifies for every accepted pair — acceptance implies `D3.RelD3 cb pb`
*on the accepted bytes themselves*.  This is the form a downstream consumer that already holds
canonical bytes can use directly. -/
theorem artifact_sound {cb pb : ArenaCore.Bytes}
    (h : Model.verifier.deployed [] cb pb = true)
    (hcanon : ∀ c : WfClaim, WfClaim.decode cb = some c → c.1.encode = cb) :
    D3.RelD3 cb pb := by
  obtain ⟨c, hc, hrel⟩ := artifact_sound_decoded h
  rw [← hcanon c hc]
  exact hrel

/-! ## §3. The binding direction: a proof outside the relation is rejected -/

/-- **Binding.**  A claim/witness pair that does *not* satisfy `RelD3` is rejected.  Contrapositive
of `artifact_sound`, so the deployed artifact accepts nothing outside the D3 relation.  This is the
half that matters against a malicious prover: there is no accepting proof for a false chunk. -/
theorem artifact_binding {cb pb : ArenaCore.Bytes}
    (h : ∀ c : WfClaim, WfClaim.decode cb = some c → ¬ D3.RelD3 c.1.encode pb) :
    Model.verifier.deployed [] cb pb ≠ true := by
  intro hacc
  obtain ⟨c, hc, hrel⟩ := artifact_sound_decoded hacc
  exact h c hc hrel

/-! ## §4. Carrying acceptance to the tier relation and the unified chunk language -/

/-- Acceptance implies the *tier* relation, which is what `challengeSpecChunk .d3a` declares. -/
theorem artifact_sound_tier {cb pb : ArenaCore.Bytes}
    (h : Model.verifier.deployed [] cb pb = true) :
    ∃ c : WfClaim, WfClaim.decode cb = some c ∧ NearSpecV3.RelTier .d3a c.1.encode pb := by
  obtain ⟨c, hc, hrel⟩ := artifact_sound_decoded h
  exact ⟨c, hc, hrel⟩

/-- And therefore the unified chunk statement's language, via the kernel-checked `rel_mono`
(`ChallengeChunkV3.lean:68-77`).  This is the rung-to-top edge of the pipeline. -/
theorem artifact_sound_chunk {cb pb : ArenaCore.Bytes}
    (h : Model.verifier.deployed [] cb pb = true) :
    ∃ c : WfClaim, WfClaim.decode cb = some c ∧ NearSpecV3.RelChunkV3 c.1.encode pb := by
  obtain ⟨c, hc, hrel⟩ := artifact_sound_tier h
  exact ⟨c, hc, NearSpecV3.rel_mono .d3a c.1.encode pb hrel⟩

/-! ## §5. Completeness on the tier domain

`verifierComplete` (`Obligations.lean:63-70`) already gives the honest-witness direction for
`challengeSpecChunk .d3a`; this restates its conclusion in `RelD3` form so a consumer has both
directions against one relation name. -/

/-- **Artifact completeness, round-tripped through soundness.**

Every claim in the tier's domain has an accepted witness within the witness bound — and, by §2,
that same accepted witness satisfies `RelD3`.  Both conjuncts come from the same artifact:
`verifierComplete` supplies acceptance and the size bound, `Read.check_sound` supplies the
relation.  Note the witness `w'` is *not* the domain witness: `VerifierComplete` may normalise it
(`Read.canonW`), so its relation has to be re-derived from acceptance rather than assumed. -/
theorem artifact_complete (pub : ArenaCore.Bytes) (mpb : Nat) (hm : maxWitnessChunk ≤ mpb)
    {c : WfClaim} (hdom : WfClaim.DomainTier .d3a c) :
    ∃ w' : List UInt8, w'.length ≤ mpb ∧
      Model.verifier.deployed pub (WfClaim.encode c) w' = true ∧
      D3.RelD3 c.1.encode w' := by
  obtain ⟨w, hrel, _hlen⟩ := hdom
  obtain ⟨w', hw'len, hw'acc⟩ := verifierComplete pub mpb hm c w ⟨w, hrel, _hlen⟩ hrel
  refine ⟨w', hw'len, hw'acc, ?_⟩
  obtain ⟨c', hc', hrel', _⟩ := check_sound (deployed_eq pub (WfClaim.encode c) w' ▸ hw'acc)
  have hsame : c' = c := by
    have : some c' = some c := by rw [← hc', WfClaim.decode_encode]
    exact Option.some.inj this
  rw [hsame] at hrel'
  exact hrel'

/-! ## §6. Axiom hygiene, checked in the artifact's own build

`proof_source_audit.py` re-runs every `#guard_msgs`-guarded `#print axioms` against the fresh
closure and rejects anything outside `{propext, Classical.choice, Quot.sound}`.  Putting the guards
here means the D3 soundness chain is audited by the same pass that audits the rest of the candidate,
rather than by a separate hand run. -/

/--
info: 'ReexecV3D3.relTier_d3a_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ReexecV3D3.relTier_d3a_eq

/--
info: 'ReexecV3D3.wfClaim_relTier_d3a_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ReexecV3D3.wfClaim_relTier_d3a_eq

/--
info: 'ReexecV3D3.artifact_sound_decoded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ReexecV3D3.artifact_sound_decoded

/--
info: 'ReexecV3D3.artifact_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ReexecV3D3.artifact_sound

/--
info: 'ReexecV3D3.artifact_binding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ReexecV3D3.artifact_binding

/--
info: 'ReexecV3D3.artifact_sound_tier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ReexecV3D3.artifact_sound_tier

/--
info: 'ReexecV3D3.artifact_sound_chunk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ReexecV3D3.artifact_sound_chunk

/--
info: 'ReexecV3D3.artifact_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ReexecV3D3.artifact_complete

end ReexecV3D3
