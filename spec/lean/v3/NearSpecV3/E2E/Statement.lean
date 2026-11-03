import NearSpecV3.E2E.Machine
import NearSpecV3.ClaimV3Props

/-!
# E2E-M11: the public statement, the four obligations and `e2e_sound`

**Statement (D-2).** The public statement is the endorsed chunk (`chunk_inner`, with `epoch_id`,
`protocol_version`, `chain_id`) and the trusted section C. Section B (block headers and slots,
authenticated by `chunk_inner.prev_block_hash`) is private, as is the witness. `assemble` rebuilds
the claim bytes; `E2EStmt s := ∃ secB w, Tier.rel .allFeatures (assemble s.ci secB s.secC) w`.

`e2e_statement_iff` restates it through `CM` (obligation 3, `cm_iff`, proved in `Machine.lean`)
in the form the final verifier checks: a run from `init` to a configuration whose outputs pass
`FinalOutPub`, the comparison with the **public** chunk header (`final_header_public`: on a
well-formed claim, the header `CM` compares with is the decoded public `chunk_inner`).

**Obligations.** The proof system is a parameter (`SegSystem`, `WrapCheck`, `FinalVerify`); the
three open obligations are `Prop`s over it, and none mentions `Tier.rel` or `checkSuccessor`:

1. `NvFaithfulE2E` + `WrapFinalFaithful` — acceptance yields a chain of satisfied segment instances
   with matching boundaries whose root boundaries pass the wrap checks, and the wrap's final check
   means an accepting `CM` configuration (instance: `ZkFormal.PQ.NvFaithful` + `NodeOK` + QROM);
2. `SegSound` — per template, accepted rows imply a `CM` step range `Steps (abs B) (abs B')`;
3. (proved) `cm_iff`;
4. `WitnessExtraction` — a wrap-accepted first boundary abstracts to `init (assemble ci secB secC) w`.

`e2e_sound` derives the statement from them. `Bad` (hash collision or Fiat–Shamir failure) is a
parameter carried as a disjunct.

**Non-vacuity.** `reexec` is a concrete proof system (re-execution segments: a "trace" is a step
count, `Holds` is `StepsN`) for which obligations 1, 2 and 4 are proved directly from `CM.step`,
with no reference to the checker; `e2e_sound` then yields `Tier.rel` only through `cm_iff`. Its
verifier is not trivially accepting (`reexec_rejects_zero_steps`), and every true statement has an
accepting proof (`reexec_complete`). The real-chunk instance is `E2E/RealChunk.lean` (on demand).
-/

namespace NearSpecV3.E2E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Successor

/-! ## The public statement -/

/-- Section C: the trusted chain/epoch facts (claim-v3 §2, T4–T14). Public. -/
structure SecC where
  rsDataParts : Nat
  rsTotalParts : Nat
  epochs : List EpochRec
  epochStartAfter : Bytes
  applyFacts : List ApplyFacts
  txValid : Bytes
  genesisChunkExtra : Option Bytes

/-- Section A with the trusted header values (T1–T3). Public. -/
structure ChunkPub where
  protocolVersion : Nat
  chainId : Bytes
  epochId : Bytes
  chunkInner : Bytes

/-- **The public statement (D-2).** -/
structure PublicStmt where
  ci : ChunkPub
  secC : SecC

/-- The claim of a public statement and a private section B. -/
def assembleClaim (ci : ChunkPub) (secB : List BlockRec) (secC : SecC) : Claim :=
  { protocolVersion := ci.protocolVersion, chainId := ci.chainId, epochId := ci.epochId,
    chunkInner := ci.chunkInner, blocks := secB, rsDataParts := secC.rsDataParts,
    rsTotalParts := secC.rsTotalParts, epochs := secC.epochs,
    epochStartAfter := secC.epochStartAfter, applyFacts := secC.applyFacts,
    txValid := secC.txValid, genesisChunkExtra := secC.genesisChunkExtra }

/-- `assemble chunk_inner secB secC`: the claim bytes. -/
def assemble (ci : ChunkPub) (secB : List BlockRec) (secC : SecC) : Bytes :=
  (assembleClaim ci secB secC).encode

/-- **The E2E statement** (owner decisions D-1, D-2). -/
def E2EStmt (s : PublicStmt) : Prop :=
  ∃ secB w, Tier.rel .allFeatures (assemble s.ci secB s.secC) w

/-- The public final check: `FinalOut(B_N)` equals the header outputs of the **public**
`chunk_inner`. -/
def FinalOutPub (s : PublicStmt) : Conf → Prop
  | .done H o => decodeChunkInner s.ci.chunkInner = .ok H ∧ headerOk H o = true
  | .doneG => True
  | _ => False

/-- The statement through `CM` (obligation 3). -/
theorem e2e_stmt_iff_cm (s : PublicStmt) :
    E2EStmt s ↔ ∃ secB w, CMAccepts (assemble s.ci secB s.secC) w := by
  unfold E2EStmt
  simp only [cm_iff]

theorem decodeClaimE_encode (c : Claim) (h : c.wf = true) : decodeClaimE c.encode = .ok c := by
  have := decodeClaim_encode c h
  unfold decodeClaim at this
  split at this
  · cases this; assumption
  · cases this

/-- **On a well-formed claim, `CM` compares with the public `chunk_inner`.** -/
theorem final_header_public (s : PublicStmt) (secB : List BlockRec) (w : Bytes)
    (hwf : (assembleClaim s.ci secB s.secC).wf = true) {H : ChunkInner} {o : Outputs}
    (h : Steps (.init (assemble s.ci secB s.secC) w) (.done H o)) :
    decodeChunkInner s.ci.chunkInner = .ok H := by
  obtain ⟨c, hc, hH⟩ := cm_done_header h
  rw [assemble, decodeClaimE_encode _ hwf] at hc
  cases hc
  exact hH

/-- Only a genesis-containing segment ends in the atomic `doneG`. -/
theorem steps_init_doneG {cb wb : Bytes} (h : Steps (.init cb wb) .doneG) :
    segmentHasGenesis cb = true := by
  cases hg' : segmentHasGenesis cb
  case true => rfl
  exfalso
  cases h with
  | step hs hrest =>
    rw [step_init_nongen hg'] at hs
    rcases hI : intakeK afDriver true cb wb pure with e | I <;> rw [hI] at hs <;>
      simp [Except.map] at hs
    subst hs
    rcases steps_eng_inv hrest with ⟨c', hc'⟩ | ⟨out, hf⟩
    · cases hc'
    · rcases steps_fin_inv hf with hc | ⟨o', hc⟩ <;> cases hc

/-- `FinalOutPub` is acceptance plus the public header. -/
theorem finalOutPub_accepting (s : PublicStmt) (cf : Conf) (h : FinalOutPub s cf) :
    cf.accepting = true := by
  cases cf <;> simp_all [FinalOutPub, Conf.accepting]

/-- **`e2e_statement_iff`: the statement in the form the final verifier's public inputs check.**
For a well-formed assembled claim (lengths and digest widths, `Claim.wf`; checked by `INTAKE`
on the private section B), the E2E statement holds iff some section B and witness give a `CM` run
from `init` to a configuration passing `FinalOutPub` — the comparison with the header outputs of
the **public** `chunk_inner`. -/
theorem e2e_statement_iff (s : PublicStmt) :
    (∃ secB w, (assembleClaim s.ci secB s.secC).wf = true ∧
        Tier.rel .allFeatures (assemble s.ci secB s.secC) w) ↔
      ∃ secB w, (assembleClaim s.ci secB s.secC).wf = true ∧
        ∃ cf, Steps (.init (assemble s.ci secB s.secC) w) cf ∧ FinalOutPub s cf := by
  constructor
  · rintro ⟨secB, w, hwf, hrel⟩
    obtain ⟨cf, hs, ha⟩ := (cm_iff _ _).1 hrel
    refine ⟨secB, w, hwf, cf, hs, ?_⟩
    cases cf with
    | done H o => exact ⟨final_header_public s secB w hwf hs, ha⟩
    | doneG => trivial
    | _ => simp [Conf.accepting] at ha
  · rintro ⟨secB, w, hwf, cf, hs, hf⟩
    exact ⟨secB, w, hwf, (cm_iff _ _).2 ⟨cf, hs, finalOutPub_accepting s cf hf⟩⟩

/-! ## The proof system as a parameter, and the obligations -/

/-- A segment proof system: templates, circuit boundaries `B` (plan §3.2), an abstraction of
boundaries into `CM` configurations, and the per-template trace predicate (`Holds SegAir_k`). -/
structure SegSystem where
  Template : Type
  Bnd : Type
  Trace : Type
  abs : Bnd → Option Conf
  Holds : Template → Bnd → Bnd → Trace → Prop

/-- Boundaries of a list of segment instances match. -/
def BndChained {B : Type} : B → List (B × B) → B → Prop
  | a, [], b => a = b
  | a, s :: rest, b => a = s.1 ∧ BndChained s.2 rest b

/-- A flattened accepted aggregation tree: the leaves in order and the root's boundaries. -/
structure SegChain (S : SegSystem) where
  segs : List (S.Template × S.Bnd × S.Bnd × S.Trace)
  b0 : S.Bnd
  bN : S.Bnd

def SegChain.Valid {S : SegSystem} (ch : SegChain S) : Prop :=
  (∀ x ∈ ch.segs, S.Holds x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
    BndChained ch.b0 (ch.segs.map fun x => (x.2.1, x.2.2.1)) ch.bN

/-- The wrap's checks on the root boundaries, over public inputs only (plan §3.4). -/
structure WrapCheck (S : SegSystem) where
  /-- `B_0 = Init(claimDigest)`. -/
  InitOK : PublicStmt → S.Bnd → Prop
  /-- `B_N.phase = done` and `FinalOut(B_N) = header outputs`. -/
  FinalOK : PublicStmt → S.Bnd → Prop

/-- **Obligation 1a (NV/wrap faithfulness).** An accepted final proof yields a valid chain of
segment instances whose root boundaries pass the wrap checks, or `Bad`. -/
def NvFaithfulE2E (S : SegSystem) (W : WrapCheck S) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop) : Prop :=
  ∀ s π, FinalVerify s π = true →
    Bad ∨ ∃ ch : SegChain S, ch.Valid ∧ W.InitOK s ch.b0 ∧ W.FinalOK s ch.bN

/-- **Obligation 1b.** The wrap's final check means an accepting configuration with the public
header. -/
def WrapFinalFaithful (S : SegSystem) (W : WrapCheck S) : Prop :=
  ∀ s b, W.FinalOK s b → ∃ cf, S.abs b = some cf ∧ cf.accepting = true

/-- **Obligation 2 (segment soundness, per template).** Accepted rows imply a `CM` step range. -/
def SegSound (S : SegSystem) (Bad : Prop) : Prop :=
  ∀ k b b' tr, S.Holds k b b' tr →
    Bad ∨ ∃ c c', S.abs b = some c ∧ S.abs b' = some c' ∧ Steps c c'

/-- **Obligation 4 (witness extraction).** The first boundary the wrap accepts abstracts to the
initial configuration of an assembled claim (the statement plus some section B) and some witness:
`INTAKE`'s authenticated nodes and code blobs determine `w`. -/
def WitnessExtraction (S : SegSystem) (W : WrapCheck S) (Bad : Prop) : Prop :=
  ∀ s b, W.InitOK s b → Bad ∨ ∃ secB w, S.abs b = some (.init (assemble s.ci secB s.secC) w)

theorem steps_of_bndChain (S : SegSystem) :
    ∀ (segs : List (S.Template × S.Bnd × S.Bnd × S.Trace)) (b0 bN : S.Bnd) (c0 cN : Conf),
      (∀ x ∈ segs, ∃ c c', S.abs x.2.1 = some c ∧ S.abs x.2.2.1 = some c' ∧ Steps c c') →
      BndChained b0 (segs.map fun x => (x.2.1, x.2.2.1)) bN →
      S.abs b0 = some c0 → S.abs bN = some cN → Steps c0 cN
  | [], b0, bN, c0, cN, _, h, h0, hN => by
    cases h; rw [h0] at hN; cases hN; exact .refl _
  | x :: rest, b0, bN, c0, cN, hs, ⟨h1, h2⟩, h0, hN => by
    obtain ⟨c, c', hc, hc', hst⟩ := hs x (by simp)
    subst h1
    rw [h0] at hc; cases hc
    exact hst.trans (steps_of_bndChain S rest x.2.2.1 bN c' cN
      (fun y hy => hs y (by simp [hy])) h2 hc' hN)

/-- **`e2e_sound`: the composition, checked.** Obligations 1, 2 and 4 as hypotheses, obligation 3
(`cm_iff`) proved: an accepted final proof establishes the E2E statement, or `Bad`. -/
theorem e2e_sound (S : SegSystem) (W : WrapCheck S) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (ob1 : NvFaithfulE2E S W FinalVerify Bad) (ob1b : WrapFinalFaithful S W)
    (ob2 : SegSound S Bad) (ob4 : WitnessExtraction S W Bad)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ Bad := by
  classical
  rcases ob1 s π hv with hb | ⟨ch, ⟨hholds, hchain⟩, hinit, hfin⟩
  · exact .inr hb
  rcases ob4 s ch.b0 hinit with hb | ⟨secB, w, h0⟩
  · exact .inr hb
  by_cases hbad : Bad
  · exact .inr hbad
  have hsegs : ∀ x ∈ ch.segs, ∃ c c', S.abs x.2.1 = some c ∧ S.abs x.2.2.1 = some c' ∧ Steps c c' :=
    fun x hx => (ob2 _ _ _ _ (hholds x hx)).resolve_left hbad
  obtain ⟨cf, hN, hacc⟩ := ob1b s ch.bN hfin
  have hrun := steps_of_bndChain S ch.segs ch.b0 ch.bN _ cf hsegs hchain h0 hN
  exact .inl ((e2e_stmt_iff_cm s).2 ⟨secB, w, cf, hrun, hacc⟩)

/-! ## Non-vacuity: a concrete proof system satisfying obligations 1, 2, 4 -/

/-- `n` steps of `CM` from a configuration. -/
def runN : Nat → Conf → Except String Conf
  | 0, c => .ok c
  | n + 1, c => CM.step c >>= runN n

theorem stepsN_of_runN : ∀ (n : Nat) (a b : Conf), runN n a = .ok b → StepsN n a b
  | 0, a, b, h => by cases h; exact .refl _
  | n + 1, a, b, h => by
    simp only [runN] at h
    rcases hs : CM.step a with e | a' <;> rw [hs] at h
    · cases h
    · exact .step hs (stepsN_of_runN n a' b h)

theorem runN_of_stepsN {n : Nat} {a b : Conf} (h : StepsN n a b) : runN n a = .ok b := by
  induction h with
  | refl => rfl
  | step hs _ ih => simp only [runN, hs]; exact ih

/-- The re-execution system: a boundary is a `CM` configuration, a trace is a step count. -/
def reexec : SegSystem where
  Template := Unit
  Bnd := Conf
  Trace := Nat
  abs := some
  Holds := fun _ b b' n => StepsN n b b'

def reexecWrap : WrapCheck reexec where
  InitOK := fun s b => ∃ secB w, b = .init (assemble s.ci secB s.secC) w
  FinalOK := fun _ b => b.accepting = true

/-- A re-execution proof: section B, witness and step count. -/
abbrev ReexecProof := List BlockRec × Bytes × Nat

def reexecVerify (s : PublicStmt) (π : ReexecProof) : Bool :=
  match runN π.2.2 (.init (assemble s.ci π.1 s.secC) π.2.1) with
  | .ok cf => cf.accepting
  | .error _ => false

theorem reexec_ob1 : NvFaithfulE2E reexec reexecWrap reexecVerify False := by
  intro s ⟨secB, w, n⟩ hv
  right
  unfold reexecVerify at hv
  rcases hr : runN n (.init (assemble s.ci secB s.secC) w) with e | cf <;> rw [hr] at hv
  · cases hv
  · refine ⟨⟨[((), .init (assemble s.ci secB s.secC) w, cf, n)], .init (assemble s.ci secB s.secC) w, cf⟩,
      ⟨?_, ⟨rfl, rfl⟩⟩, ⟨secB, w, rfl⟩, hv⟩
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact stepsN_of_runN n _ _ hr

theorem reexec_ob1b : WrapFinalFaithful reexec reexecWrap := fun _ b h => ⟨b, rfl, h⟩

theorem reexec_ob2 : SegSound reexec False := fun _ b b' n h =>
  .inr ⟨b, b', rfl, rfl, (steps_iff_stepsN).2 ⟨n, h⟩⟩

theorem reexec_ob4 : WitnessExtraction reexec reexecWrap False := by
  rintro s b ⟨secB, w, rfl⟩
  exact .inr ⟨secB, w, rfl⟩

/-- `e2e_sound` instantiated: obligations proved from `CM.step` alone. -/
theorem reexec_sound (s : PublicStmt) (π : ReexecProof) (hv : reexecVerify s π = true) :
    E2EStmt s :=
  (e2e_sound reexec reexecWrap reexecVerify False reexec_ob1 reexec_ob1b reexec_ob2 reexec_ob4
    s π hv).resolve_right id

/-- The verifier is not trivially accepting: zero steps never accept (`init` is not final). -/
theorem reexec_rejects_zero_steps (s : PublicStmt) (secB : List BlockRec) (w : Bytes) :
    reexecVerify s (secB, w, 0) = false := rfl

/-- Completeness of the re-execution system: every true statement has an accepting proof. -/
theorem reexec_complete (s : PublicStmt) (h : E2EStmt s) : ∃ π, reexecVerify s π = true := by
  obtain ⟨secB, w, cf, hs, ha⟩ := (e2e_stmt_iff_cm s).1 h
  obtain ⟨n, hn⟩ := steps_iff_stepsN.1 hs
  refine ⟨(secB, w, n), ?_⟩
  simp only [reexecVerify, runN_of_stepsN hn]
  exact ha

#print axioms e2e_stmt_iff_cm
#print axioms e2e_statement_iff
#print axioms e2e_sound
#print axioms reexec_sound
#print axioms reexec_complete

end NearSpecV3.E2E
