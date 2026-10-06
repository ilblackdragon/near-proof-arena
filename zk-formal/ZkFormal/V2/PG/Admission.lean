import ZkFormal.V2.PG.V2Prover
import ZkFormal.V2.G.RomFull
import ZkFormal.V2.Admission
import ZkFormal.V3.Hint
import ZkFormal.Assembly.Admission

/-!
# ZkFormal.V2.PG.Admission — `admission_v2` at `auxGroup = g ∈ {1,2,3}` (P2 copy of `V2.Admission`)

P2: the statement and proof of `V2.admission_v2` with `dp = pg g` (`AuxG` instance) in place
of `dp`, `NpOkPg` in place of `NpOkP`, `stark_romSound_fullPg` and the generalised
honest prover (`Prover.Np.G`).  `admission_v2_pg g` instantiates it at any `1 ≤ g`
(`NpOkPg` then forces `g ≤ 3`).

`admission_v2` is the v2 analogue of `Assembly.np_admission`, for the v3 pipeline
(`V3-D0-DESIGN.md` §2.1):

```
verify(pub, cb, pb):
  guard:  claimOk cb                         -- canonical claim (R-L7-2)
  split:  split pb = some (h, π)             -- hint ‖ STARK proof
  prep:   prep cb h = some cb'               -- native preprocessing
  stark:  verifierP Fp Fp8 AP default on (cb', π)
```

| conjunct | from |
|---|---|
| `FORMAL_SEMANTIC_SOUNDNESS` | `hsound`: `prep (enc c) h = some cb' ∧ HoldsP AP (pubOf cb') tr → ∃ w, Rel c w` |
| `FORMAL_SEMANTIC_COMPLETENESS` | `hcomp`: a hint and a trace for every in-domain true claim |
| `VerifierComplete`, `ProverComplete` | `npIopCompleteP` (L7, v2), `bcs_complete32`, `size32`, `hjoin` (proof = `join h π` fits) |
| `CryptoSound` (ROM) | `stark_romSound_fullP` ∘ `V3.romSound_hint` ∘ `romSound_guard` |

The backend object is the pair `(hint, trace)`.  The honest prover is
`join h π`: `h = hintOf c w`, and `π` is v1's honest prover for the prepared statement
`cb' = prep (enc c) h`.
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Prover ZkFormal.Assembly ZkFormal.V2

/-- **The deployed v2 verifier with hints**: claim guard, hint split, native
preprocessing, then the compiled v2 STARK verifier on the prepared statement. -/
def npVerifierP (S : ChallengeSpec) (AP : AirP) (split : Bytes → Option (Bytes × Bytes))
    (prep : Bytes → Bytes → Option Bytes) : TreeVerifier :=
  guardTree (claimOk S) (V3.hintTree split prep (verifierP Fp Fp8 AP dp))

/-- Good honest v2 IOP provers for a trace. -/
def NpGoodP (AP : AirP) (cb : Bytes) (tr : Trace Fp) (pr : IopProver Fp Fp8) : Prop :=
  pr.hdr = trHdr AP.toAir tr ∧ ProverWf (VdP AP) pr cb ∧ IopComplete (VdP AP) pr cb

open Classical in
noncomputable def npIopP (AP : AirP) (cb : Bytes) (tr : Trace Fp) : IopProver Fp Fp8 :=
  if h : ∃ pr, NpGoodP AP cb tr pr then Classical.choose h else ⟨[], fun _ => []⟩

theorem npIopP_spec (AP : AirP) (cb : Bytes) (tr : Trace Fp) :
    NpGoodP AP cb tr (npIopP AP cb tr) ∨ (npIopP AP cb tr).hdr = [] := by
  unfold npIopP
  split
  · rename_i h; exact Or.inl (Classical.choose_spec h)
  · exact Or.inr rfl

/-- The honest v2 prover: hint, then the STARK proof for the prepared statement. -/
noncomputable def npProverP (S : ChallengeSpec) (AP : AirP) (prep : Bytes → Bytes → Option Bytes)
    (join : Bytes → Bytes → Bytes) (hintOf : S.Claim → S.Witness → Bytes)
    (traceOf : S.Claim → S.Witness → Trace Fp) : TreeProver S :=
  ⟨fun pub c w =>
    let h := hintOf c w
    let cb' := (prep (S.encodeClaim c) h).getD []
    (proveTree (VdP AP) (npIopP AP cb' (traceOf c w)) pub cb').bind fun π => .pure (join h π)⟩

/-- The v2 backend: a hint and a trace of the prepared statement. -/
def npBackendP (S : ChallengeSpec) (AP : AirP) (prep : Bytes → Bytes → Option Bytes) : Backend S :=
  ⟨Bytes × Trace Fp, fun c o => ∃ cb', prep (S.encodeClaim c) o.1 = some cb' ∧
    HoldsP AP (Udr.pubOf Fp cb') o.2⟩

theorem runH_bind_pure {σ α β : Type} (H : Interp.HashOracle σ) (f : α → β) :
    ∀ (oa : OracleComp hashSpec α) (s : σ),
      runH H (oa.bind fun a => .pure (f a)) s = (f (runH H oa s).1, (runH H oa s).2)
  | .pure a, s => rfl
  | .query x k, s => by
    show runH H ((k (H s x).1).bind fun a => .pure (f a)) (H s x).2 = _
    rw [runH_bind_pure H f (k (H s x).1)]
    rfl

theorem proverQ_eqP (AP : AirP) (hdr : List Nat) :
    proverQ (VdP AP) hdr = proverQ (Vd AP.toAir) hdr := by
  unfold proverQ
  rw [show (VdP AP).schedule = (Vd AP.toAir).schedule from schedule_eqP AP dp]
  rfl

theorem headerOk_nilP (AP : AirP) (hA : AP.tables ≠ []) : (VdP AP).headerOk [] = false := by
  cases h : AP.toAir.tables with
  | nil => exact absurd h hA
  | cons T Ts =>
    show (headerOk AP.toAir dp [] && _) = false
    simp [headerOk, h]

/-- **`ProverComplete`** of the honest v2 prover against the deployed v2 verifier. -/
theorem np_proverCompleteP (S : ChallengeSpec) (AP : AirP) (htab : AP.tables.length < 2 ^ 32)
    (split : Bytes → Option (Bytes × Bytes)) (prep : Bytes → Bytes → Option Bytes)
    (join : Bytes → Bytes → Bytes) (hintOf : S.Claim → S.Witness → Bytes)
    (hsplit : ∀ c w π, S.Domain c → S.Rel c w → split (join (hintOf c w) π) = some (hintOf c w, π))
    (traceOf : S.Claim → S.Witness → Trace Fp)
    (hcomp : ∀ c w, S.Domain c → S.Rel c w → ∃ cb', prep (S.encodeClaim c) (hintOf c w) = some cb' ∧
      HoldsP AP (Udr.pubOf Fp cb') (traceOf c w) ∧ (VdP AP).headerOk (trHdr AP.toAir (traceOf c w)) = true)
    (maxInner : Nat) (hsize : ∀ hdr, (VdP AP).headerOk hdr = true → sizeBound (VdP AP) hdr ≤ maxInner)
    (hmaxI : maxInner ≤ dp.maxProofBytes) (maxB : Nat)
    (hjoin : ∀ c w π, S.Domain c → S.Rel c w → π.length ≤ maxInner → (join (hintOf c w) π).length ≤ maxB)
    (pub : Bytes) :
    ProverComplete S (npVerifierP S AP split prep).toVerifier
      (npProverP S AP prep join hintOf traceOf).toProver pub maxB := by
  intro H c w hd hr
  obtain ⟨cb', hp, hH, hok⟩ := hcomp c w hd hr
  obtain ⟨pr, hpr⟩ := npIopCompleteP AP cb' (traceOf c w) htab hH hok
  have hgood : NpGoodP AP cb' (traceOf c w) (npIopP AP cb' (traceOf c w)) := by
    unfold npIopP
    rw [dif_pos ⟨pr, hpr⟩]
    exact Classical.choose_spec (⟨pr, hpr⟩ : ∃ pr, NpGoodP AP cb' (traceOf c w) pr)
  obtain ⟨_, hwf, hcpl⟩ := hgood
  let π := (runH (pureH H) (proveTree (VdP AP) (npIopP AP cb' (traceOf c w)) pub cb') ()).1
  have hπ : π.length ≤ maxInner :=
    Nat.le_trans (size32 Fp Fp8 (VdP AP) _ pub _ H (fun _ => fit32_length _) hwf) (hsize _ hwf.hdrOk)
  have hrun : runH (pureH H) ((npProverP S AP prep join hintOf traceOf).tree pub c w) () =
      (join (hintOf c w) π, ()) := by
    show runH (pureH H) ((proveTree (VdP AP) (npIopP AP ((prep (S.encodeClaim c) (hintOf c w)).getD [])
      (traceOf c w)) pub ((prep (S.encodeClaim c) (hintOf c w)).getD [])).bind fun π => .pure _) () = _
    rw [hp, Option.getD_some, runH_bind_pure]
  refine ⟨?_, ?_⟩
  · show (runH (pureH H) ((npProverP S AP prep join hintOf traceOf).tree pub c w) ()).1.length ≤ maxB
    rw [hrun]; exact hjoin c w π hd hr hπ
  · show (runH (pureH H) ((npVerifierP S AP split prep).tree pub (S.encodeClaim c)
      (runH (pureH H) ((npProverP S AP prep join hintOf traceOf).tree pub c w) ()).1) ()).1 = true
    rw [hrun]
    show (runH (pureH H) (if claimOk S (S.encodeClaim c) then _ else _) ()).1 = true
    rw [if_pos (claimOk_encode S c)]
    show (runH (pureH H) (match split (join (hintOf c w) π) with
      | some (h, π) => match prep (S.encodeClaim c) h with
        | some cb' => (verifierP Fp Fp8 AP dp).tree pub cb' π
        | none => .pure false
      | none => .pure false) ()).1 = true
    rw [hsplit c w π hd hr]
    dsimp only
    rw [hp]
    exact bcs_complete32 Fp Fp8 (VdP AP) _ pub _ H (fun _ => fit32_length _)
      (show 0 < dp.numChunks by dp_decide) (show 0 < dp.posPerChunk by dp_decide)
      (schedOkP AP dp) hwf hcpl (Nat.le_trans hπ hmaxI)

/-- **The admission certificate of an np-udr-stark-v2 candidate with hints and native
preprocessing**: from the AIR's semantic soundness/completeness (through `prep`), L3's
decidable `NpOkP`, the size and query numerics, and the hint codec. -/
theorem admission_v2
    (ch : ChallengeParams) (art : ArtifactDescription) (pub : Bytes)
    (hpub : sha256 pub = art.publicDigest)
    (AP : AirP) (hA : AP.tables ≠ []) (htab : AP.tables.length < 2 ^ 32)
    (split : Bytes → Option (Bytes × Bytes)) (prep : Bytes → Bytes → Option Bytes)
    (join : Bytes → Bytes → Bytes)
    (himpl : art.impl.Connection ch.verifyFuel (npVerifierP ch.spec AP split prep).toVerifier)
    (hintOf : ch.spec.Claim → ch.spec.Witness → Bytes)
    (hsplit : ∀ c w π, ch.spec.Domain c → ch.spec.Rel c w →
      split (join (hintOf c w) π) = some (hintOf c w, π))
    (traceOf : ch.spec.Claim → ch.spec.Witness → Trace Fp)
    (hsound : ∀ c h cb' tr, prep (ch.spec.encodeClaim c) h = some cb' →
      HoldsP AP (Udr.pubOf Fp cb') tr → ∃ w, ch.spec.Rel c w)
    (hcomp : ∀ c w, ch.spec.Domain c → ch.spec.Rel c w →
      ∃ cb', prep (ch.spec.encodeClaim c) (hintOf c w) = some cb' ∧
        HoldsP AP (Udr.pubOf Fp cb') (traceOf c w) ∧ (VdP AP).headerOk (trHdr AP.toAir (traceOf c w)) = true)
    (maxInner : Nat) (hsize : ∀ hdr, (VdP AP).headerOk hdr = true → sizeBound (VdP AP) hdr ≤ maxInner)
    (hmaxI : maxInner ≤ dp.maxProofBytes)
    (hjoin : ∀ c w π, ch.spec.Domain c → ch.spec.Rel c w → π.length ≤ maxInner →
      (join (hintOf c w) π).length ≤ ch.maxProofBytes)
    (hmodel : ch.profile.model = .randomOracle)
    (hassm : AssumptionId.sha256RandomOracle ∈ ch.profile.allowedAssumptions)
    (htb : ch.profile.targetBits ≤ 128) (hqh : ch.profile.maxHashQueriesLog2 = 64)
    (hqp : ch.profile.maxProverQueriesLog2 = 40)
    (lo g : Nat) (hlo : ∀ hdr, (VdP AP).headerOk hdr = true → lo ≤ queryLog AP.toAir dp hdr)
    (hdom : Dominates (Udr.agreeUdr 4) lo g) (hq : QueryOk dp.numChunks g)
    (hok : V2.G.NpOkPg AP dp)
    (hNV : NVu AP.toAir dp ≤ 2 ^ 30) :
    AdmissionStatement ch art := by
  let P := npProverP ch.spec AP prep join hintOf traceOf
  have hPC := np_proverCompleteP ch.spec AP htab split prep join hintOf hsplit traceOf hcomp maxInner
    hsize hmaxI ch.maxProofBytes hjoin pub
  let bk := npBackendP ch.spec AP prep
  refine ⟨pub, (npVerifierP ch.spec AP split prep).toVerifier, hpub, himpl, bk, ?_, ?_, ?_, ?_⟩
  · rintro c ⟨h, tr⟩ ⟨cb', hp, hH⟩; exact hsound c h cb' tr hp hH
  · intro c w hd hr
    obtain ⟨cb', hp, hH, _⟩ := hcomp c w hd hr
    exact ⟨(hintOf c w, traceOf c w), cb', hp, hH⟩
  · intro c w hd hr
    obtain ⟨hl, hacc⟩ := hPC (fun m => sha256 (Interp.roTag ++ m)) c w hd hr
    exact ⟨_, hl, hacc⟩
  · right
    rw [hmodel]
    refine ⟨hassm, P.toProver, hPC, ?_⟩
    -- prover budgets
    have hPu : ∀ c w, OracleComp.QueryBound unitWeight (P.tree pub c w) (2 ^ 32) := by
      intro c w
      show OracleComp.QueryBound unitWeight ((proveTree (VdP AP)
        (npIopP AP ((prep (ch.spec.encodeClaim c) (hintOf c w)).getD []) (traceOf c w)) pub
        ((prep (ch.spec.encodeClaim c) (hintOf c w)).getD [])).bind fun π => .pure (join (hintOf c w) π)) _
      refine V3.queryBound_bind_pure _ _ _ _ ?_
      generalize (ch.spec.encodeClaim c) = cb0
      generalize ((prep cb0 (hintOf c w)).getD []) = cb'
      rcases npIopP_spec AP cb' (traceOf c w) with ⟨_, hwf, _⟩ | hnil
      · have hh : (Iop.verifier Fp Fp8 AP.toAir dp).headerOk
            (npIopP AP cb' (traceOf c w)).hdr = true := by
          rw [← headerOk_eqP]; exact hwf.hdrOk
        have hq := npProverQ AP.toAir _ hNV hh
        rw [← proverQ_eqP] at hq
        exact (prover_unit Fp Fp8 (VdP AP) _ pub _ hwf).mono hq
      · rw [proveTree_bad (VdP AP) _ pub _ (by rw [hnil]; exact headerOk_nilP AP hA)]
        exact .pure _ _
    have hPq : ∀ c w, OracleComp.QueryBound (qWeight Bcs.chunkDec) (P.tree pub c w)
        dp.numChunks := by
      intro c w
      show OracleComp.QueryBound _ ((proveTree (VdP AP)
        (npIopP AP ((prep (ch.spec.encodeClaim c) (hintOf c w)).getD []) (traceOf c w)) pub
        ((prep (ch.spec.encodeClaim c) (hintOf c w)).getD [])).bind fun π => .pure (join (hintOf c w) π)) _
      exact V3.queryBound_bind_pure _ _ _ _ (prover_chunk Fp Fp8 (VdP AP) _ pub _)
    obtain ⟨tapeLen, num, den, hb, hrom⟩ := stark_romSound_fullPg AP dp hok lo g hlo hdom hq
      hNV P pub (2 ^ 32) (Nat.le_refl _) hPu hPq
    refine ⟨tapeLen, num, den, ?_, ?_⟩
    · exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by dp_decide) htb)) hb
    · rw [hqh, hqp]
      have hrom' := V3.romSound_hint (L := fun cb => ∃ h cb', prep cb h = some cb' ∧ V2.Np.AirLangP AP cb')
        split prep (fun cb h cb' hp hl => ⟨h, cb', hp, hl⟩) (verifierP Fp Fp8 AP dp)
        P.toProver pub hrom
      refine romSound_guard (claimOk ch.spec) (fun cb hcb hL => ?_) _ _ pub hrom'
      obtain ⟨c, hc, he⟩ := claimOk_iff ch.spec cb hcb
      obtain ⟨h, cb', hp, tr, hH⟩ := hL
      exact ⟨c, hc, (h, tr), cb', by rw [he]; exact hp, hH⟩

end ZkFormal.Prover.Np.G

namespace ZkFormal.V2.G

open ArenaCore ArenaCore.Security ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra ZkFormal.Prover
  ZkFormal.Assembly

/-- **P2: the v2 admission certificate at `auxGroup = g`** (`1 ≤ g`; the `NpOkPg` hypothesis of
`admission_v2` restricts to `g ≤ 3`).  The deployed verifier is
`guardTree claimOk (hintTree split prep (verifierP Fp Fp8 AP (pg g)))`. -/
theorem admission_v2_pg (g : Nat) (hg : 1 ≤ g) : type_of% (@Prover.Np.G.admission_v2 ⟨g, hg⟩) :=
  @Prover.Np.G.admission_v2 ⟨g, hg⟩

/-- **P2: `ProverComplete` of the honest v2 prover at `auxGroup = g ≥ 1`.** -/
theorem np_proverCompletePg (g : Nat) (hg : 1 ≤ g) :
    type_of% (@Prover.Np.G.np_proverCompleteP ⟨g, hg⟩) :=
  @Prover.Np.G.np_proverCompleteP ⟨g, hg⟩

theorem npVerifierP_pg (g : Nat) (hg : 1 ≤ g) (S : ChallengeSpec) (AP : AirP)
    (split : Bytes → Option (Bytes × Bytes)) (prep : Bytes → Bytes → Option Bytes) :
    @Prover.Np.G.npVerifierP ⟨g, hg⟩ S AP split prep =
      guardTree (claimOk S) (V3.hintTree split prep (verifierP Fp Fp8 AP (pg g))) := rfl

end ZkFormal.V2.G
