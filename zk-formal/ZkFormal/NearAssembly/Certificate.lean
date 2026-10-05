import ZkFormal.Assembly.Admission
import NearSpec.Challenge

/-!
# ZkFormal.NearAssembly.Certificate — M5 skeleton: admission on the NEAR challenge

`near_admission`: the judge's `AdmissionStatement` for the NEAR challenge
(`NearSpec.TransferV1.challengeParamsWith …`, native-lean route, model
`nearModel A` = claim guard ∘ L4's verifier for the NEAR AIR `A`), from

* `NearPending` — the same protocol-level obligations as the toy (prover model:
  L7-bcs / L7-iop; L3's `RbrFacts` for `A`; `QueryOk` for the chunk count, R-L7-1);
* `L6Facts A honestTrace` — lane L6's deliverables, in the shapes of
  `ZkFormal.Near.{nearAir_sound, nearAir_complete, honestTrace_fits}` (lane/zk-L6),
  plus the AIR-level numerics (`W_eq`-based size bound at every admissible header,
  `NVu`).

Once L6 lands, the candidate package states
`theorem certificate : ArenaExpectedInst.expectedType := near_admission … Near.nearAir …`
with `Candidate.Model.verifier := nearModel Near.nearAir`.

**Trusted-tree pinning.** The fast SHA (`ArenaCore.sha256Fast`, `@[csimp]`) is in
formal-core since `9f1adc7`, which is newer than the `ArenaCore @ 4f5c19df` pinned by
`chl_3be9…`/`chl_fefb…`; the verify-time budget needs it, so admission happens on a
new challenge that pins the new tree (draft:
`challenges/drafts/near-transfer-receipt-v1-4.draft.json`, unsigned).
-/

namespace ZkFormal.NearAssembly

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Prover ZkFormal.Assembly NearSpec NearSpec.TransferV1

/-- The deployed verifier model for the NEAR AIR `A`. -/
def nearModel (A : Air) : OracleVerifier :=
  (guardTree (claimOk challengeSpec) (verifier Fp Fp8 A Params.default)).toVerifier

/-- Lane L6's deliverables for the AIR `A` (shapes of `Near.nearAir_sound`,
`Near.nearAir_complete`, `Near.honestTrace_fits` + static checks) and its numerics. -/
structure L6Facts (A : Air) (honestTrace : WfClaim → Witness → Trace Fp) : Prop where
  sound : ∀ (c : WfClaim) (tr : Trace Fp), Holds A (Udr.pubOf Fp c.encode) tr → ∃ w, NearRelation c.1 w
  complete : ∀ (c : WfClaim) (w : Witness), NearRelation c.1 w →
    Holds A (Udr.pubOf Fp c.encode) (honestTrace c w)
  fits : ∀ (c : WfClaim) (w : Witness), NearRelation c.1 w →
    headerOk A Params.default (trHdr A (honestTrace c w)) = true
  nonempty : A.tables ≠ []
  size : ∀ hdr, headerOk A Params.default hdr = true → sizeBound (Vd A) hdr ≤ 8388608
  nvu : NVu A Params.default ≤ 2 ^ 30

/-- Protocol-level obligations (identical in shape to `Toy.ToyPending`). -/
structure NearPending (A : Air) : Prop where
  bcs : BcsCompleteStmt
  size : SizeStmt
  proverQ : ProverQStmt
  proverChunk : ProverChunkStmt
  npIop : NpIopCompleteStmt
  npProverQ : NpProverQStmt
  rbr : Udr.RbrFacts (Vd A) (Udr.AirLang Fp A) Fp8.all (2 ^ 36) (Udr.agreeUdr 4)
  query : QueryOk Params.default.numChunks g2_5

/-- **M5 skeleton: admission on the NEAR challenge.** -/
theorem near_admission (A : Air) (honestTrace : WfClaim → Witness → Trace Fp)
    (hp : NearPending A) (h6 : L6Facts A honestTrace)
    (pid model : String) (tb : Nat) (allowed : List String) (fuel rfuel : Nat)
    (pub : ArenaCore.Bytes) (pd bd : ArenaCore.Digest) (tid : String)
    (hmodel : model = "random_oracle") (htb : tb ≤ 128)
    (hallowed : "random-oracle-fiat-shamir-sha256" ∈ allowed) (hpub : ArenaCore.sha256 pub = pd) :
    AdmissionStatement
      (challengeParamsWith (profileOf pid model tb allowed 40 64) fuel 8388608 rfuel)
      { publicDigest := pd, impl := .nativeTrusted bd tid (nearModel A) } := by
  obtain ⟨D, hR⟩ := hp.rbr
  refine np_admission hp.bcs hp.size hp.proverQ hp.proverChunk hp.npIop hp.npProverQ _ _ pub hpub
    A h6.nonempty rfl honestTrace (fun c tr h => h6.sound c tr h)
    (fun c w _ hr => ⟨h6.complete c w hr, h6.fits c w hr⟩)
    h6.size (Nat.le_refl _) ?_ ?_ htb rfl rfl 5 g2_5
    (fun hdr h => queryLog_ge_of_headerOk A Params.default hdr h6.nonempty h)
    g2_5_dom hp.query D hR h6.nvu
  · show secModelOf model = _
    rw [hmodel]; rfl
  · show AssumptionId.sha256RandomOracle ∈ allowed.flatMap assumptionOf
    exact List.mem_flatMap.2 ⟨_, hallowed, by simp [assumptionOf]⟩

end ZkFormal.NearAssembly
