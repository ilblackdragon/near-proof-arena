import ZkFormal.NearV3.Assembly.NearAirSize
import ZkFormal.NearV3.Assembly.NearAirCheck
import ZkFormal.NearV3.Assembly.Good
import ZkFormal.NearV3.Assembly.FactorSound
import ZkFormal.NearV3.Assembly.HintCodec
import ZkFormal.NearV3.Public.Prepared
import ZkFormal.V2.PG.Admission
import NearSpecV3.ChallengeD0a

/-!
# The admission certificate of the assembled v3 AIR

This module reduces the end-to-end obligation to exactly three named semantic
statements, all stated about the concrete `nearAirV3`:

* `ExtractV3Stmt` — **soundness**: `HoldsP nearAirV3` on a prepared statement
  that `prepD0` accepts yields `GoodV3` (hence, by `factorSound`, `RelD0a`).
* `RenderV3Stmt` — **completeness**: every `RelD0a` claim has a hint and an
  honest roll-aligned trace satisfying `HoldsP`.
* `AlignedV3Stmt` — the honest traces are roll-in aligned, making `nearV3_size` apply.

`nearV3_admission` composes them through `Prover.Np.G.admission_v2H` at
`auxGroup = 2` with the concrete v3 wire codecs (`prepD0 ∘ Prep.encode`, the
`Hint` codec of `Assembly.HintCodec`), the size bound `6,276,897` (item 6), and
the `NpOkPg`/`NVu` numerics (item 1).
-/

namespace ZkFormal.NearV3.Assembly

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air
  ZkFormal.Algebra ZkFormal.Prover ZkFormal.Assembly ZkFormal.V2 ZkFormal.Size NearSpecV3

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

/-- `auxGroup = 2` for the assembled AIR. -/
local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

/-- `dp` is definitionally `pg 2`. -/
theorem dp_eq_pg2 : ZkFormal.Prover.Np.G.dp = ZkFormal.V2.G.pg 2 := rfl

/-- The `NpOkPg` instance at `g = 2`, named for the certificate. -/
theorem nearAirV3_npOkPg_2 : ZkFormal.V2.G.NpOkPg nearAirV3 (ZkFormal.V2.G.pg 2) :=
  nearAirV3_npOkPg 2 (by decide) (by decide)

/-- The proved inner-proof size bound (item 6), used as `maxInner`. -/
def v3MaxInner : Nat := 6276897

/-- The hint-budget of the completeness obligation: `4 + this + maxInner ≤ 8 MiB`. -/
def v3MaxHintBytes : Nat := 2000000

theorem v3MaxHintBytes_fits :
    4 + v3MaxHintBytes + v3MaxInner ≤ challengeParamsD0a.maxProofBytes := by decide

theorem v3MaxInner_le : v3MaxInner ≤ ZkFormal.Prover.Np.G.dp.maxProofBytes := by
  show v3MaxInner ≤ 8388608
  decide

/-- `NVu` numerics for the assembled AIR at `auxGroup = 2`. -/
theorem nearV3_NVu :
    ZkFormal.Stark.NVu nearAirV3.toAir ZkFormal.Prover.Np.G.dp ≤ 2 ^ 30 := by
  rw [dp_eq_pg2]
  decide +kernel

/-- The table list is nonempty. -/
theorem nearV3_tables_ne_nil : nearAirV3.tables ≠ [] := by
  rw [nearAirV3_tables]; exact List.cons_ne_nil _ _

/-- The table count fits the u32 bound. -/
theorem nearV3_tables_lt : nearAirV3.tables.length < 2 ^ 32 := by
  rw [nearAirV3_tables_length]; decide

/-- Security-profile facts of the D0a challenge. -/
theorem d0a_model : challengeParamsD0a.profile.model = .randomOracle := by decide
theorem d0a_assm : AssumptionId.sha256RandomOracle ∈ challengeParamsD0a.profile.allowedAssumptions := by
  decide
theorem d0a_tb : challengeParamsD0a.profile.targetBits ≤ 128 := by decide
theorem d0a_qh : challengeParamsD0a.profile.maxHashQueriesLog2 = 64 := by decide
theorem d0a_qp : challengeParamsD0a.profile.maxProverQueriesLog2 = 40 := by decide

/-- The query-log lower bound (`≥ 8`) used by the security numerics. -/
theorem nearV3_lo (hdr : List Nat)
    (h : (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk hdr = true) :
    8 ≤ queryLog nearAirV3.toAir ZkFormal.Prover.Np.G.dp hdr := by
  rw [ZkFormal.V2.headerOk_eqP] at h
  exact (verifier_headerOk h).2

/-- **Soundness obligation.** Any trace accepted on a prepared statement that
`prepD0` produces reconstructs concrete semantic views `GoodV3`.  The public vector
is the protocol packing `Public.preparedBytes` (the concrete `nearAirV3.pubSegs`). -/
def ExtractV3Stmt : Prop :=
  ∀ (B : Nat) (cb : Bytes) (h : NearSpecV3.Hint) (p : NearSpecV3.Prep) (oh : Nat)
    (tr : Trace Fp),
    NearSpecV3.prepD0 cb h = .ok p →
    HoldsP nearAirV3 (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr →
    ∃ k x, GoodV3 B cb k h p x

/-- **Completeness obligation.** Every `RelD0a` claim admits a hint, a prepared
statement and an honest trace satisfying `HoldsP` with an admissible header. -/
def RenderV3Stmt : Prop :=
  ∀ (B : Nat) (cb w : List UInt8),
    NearSpecV3.checkD0a B cb w = .ok () →
    ∃ (h : NearSpecV3.Hint) (p : NearSpecV3.Prep) (oh : Nat) (tr : Trace Fp),
      NearSpecV3.prepD0 cb h = .ok p ∧
      HoldsP nearAirV3 (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr ∧
      (ZkFormal.NearV3.Assembly.Hint.encode h).length < 256 ^ 4 ∧
      (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk (trHdr nearAirV3.toAir tr) = true

/-- **Honest roll-in alignment.** The honest traces of `RenderV3Stmt` are
roll-in aligned, so the aligned size bound (`nearV3_size`) applies. -/
def AlignedV3Stmt : Prop :=
  ∀ (B : Nat) (cb w : List UInt8) (h : NearSpecV3.Hint) (p : NearSpecV3.Prep) (oh : Nat)
    (tr : Trace Fp),
    NearSpecV3.checkD0a B cb w = .ok () → NearSpecV3.prepD0 cb h = .ok p →
    HoldsP nearAirV3 (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr →
    (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk (trHdr nearAirV3.toAir tr) = true →
    RollAligned nearAirV3.toAir ZkFormal.Prover.Np.G.dp (trHdr nearAirV3.toAir tr)

/-- The proved size bound specialised to an honest trace of `traceOf`. -/
theorem v3_size_of_trace (hc : WfClaim) (hw : List UInt8)
    (traceOf : WfClaim → List UInt8 → Trace Fp)
    (halign : RollAligned nearAirV3.toAir ZkFormal.Prover.Np.G.dp
      (trHdr nearAirV3.toAir (traceOf hc hw)))
    (hheader : (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk
        (trHdr nearAirV3.toAir (traceOf hc hw)) = true) :
    Size.sizeBoundD (ZkFormal.Prover.Np.G.VdP nearAirV3)
      (trHdr nearAirV3.toAir (traceOf hc hw)) ≤ v3MaxInner := by
  exact nearV3_size (trHdr nearAirV3.toAir (traceOf hc hw)) hheader halign

/-- **The v3 admission certificate**, reduced to soundness (`hsound`),
completeness (`hcomp` + `halign`) and the wire codecs. -/
theorem nearV3_admission
    (art : ArtifactDescription) (pub : List UInt8) (hpub : sha256 pub = art.publicDigest)
    (split : List UInt8 → Option (List UInt8 × List UInt8))
    (prep : List UInt8 → List UInt8 → Option (List UInt8))
    (join : List UInt8 → List UInt8 → List UInt8)
    (himpl : art.impl.Connection challengeParamsD0a.verifyFuel
      (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prep).toVerifier)
    (hintOf : WfClaim → List UInt8 → List UInt8)
    (hsplit : ∀ c w π, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      split (join (hintOf c w) π) = some (hintOf c w, π))
    (traceOf : WfClaim → List UInt8 → Trace Fp)
    (hsound : ∀ c h cb' tr, prep (WfClaim.encode c) h = some cb' →
      HoldsP nearAirV3 (Udr.pubOf Fp cb') tr → ∃ w, WfClaim.RelD0a c w)
    (hcomp : ∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      ∃ cb', prep (WfClaim.encode c) (hintOf c w) = some cb' ∧
        HoldsP nearAirV3 (Udr.pubOf Fp cb') (traceOf c w) ∧
        (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk
          (trHdr nearAirV3.toAir (traceOf c w)) = true)
    (halign : ∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      RollAligned nearAirV3.toAir ZkFormal.Prover.Np.G.dp
        (trHdr nearAirV3.toAir (traceOf c w)))
    (hjoin : ∀ c w π, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      π.length ≤ v3MaxInner → (join (hintOf c w) π).length ≤ challengeParamsD0a.maxProofBytes) :
    AdmissionStatement challengeParamsD0a art := by
  have hsize : ∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      Size.sizeBoundD (ZkFormal.Prover.Np.G.VdP nearAirV3)
        (trHdr nearAirV3.toAir (traceOf c w)) ≤ v3MaxInner := by
    intro c w hd hr
    obtain ⟨_, _, _, hok⟩ := hcomp c w hd hr
    exact v3_size_of_trace c w traceOf (halign c w hd hr) hok
  have hlo : ∀ hdr, (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk hdr = true →
      8 ≤ queryLog nearAirV3.toAir ZkFormal.Prover.Np.G.dp hdr :=
    fun hdr h => nearV3_lo hdr h
  exact ZkFormal.Prover.Np.G.admission_v2H challengeParamsD0a art pub hpub nearAirV3
    nearV3_tables_ne_nil nearV3_tables_lt split prep join himpl hintOf hsplit traceOf hsound hcomp
    v3MaxInner hsize v3MaxInner_le hjoin d0a_model d0a_assm d0a_tb d0a_qh d0a_qp
    8 Assembly.g2_8 hlo Assembly.g2_8_dom Assembly.udr2_K24_min8_ok nearAirV3_npOkPg_2 nearV3_NVu

/-- The canonical prepared-statement codec: `prepD0` then the protocol packing
`Public.preparedBytes` (the concrete `nearAirV3.pubSegs` public vector). -/
def prepV3 (cb : List UInt8) (h : NearSpecV3.Hint) : Option (List UInt8) :=
  match NearSpecV3.prepD0 cb h with
  | .ok p => some (ZkFormal.NearV3.Public.preparedBytes p 0)
  | .error _ => none

/-- **Soundness premise from `ExtractV3Stmt`.** The AIR-to-semantics obligation, composed
with the proved `factorSound`, gives the semantic-soundness premise of the admission
theorem for the canonical `prepV3` codec. -/
theorem hsound_of_extract (hext : ExtractV3Stmt) :
    ∀ (c : WfClaim) (h : NearSpecV3.Hint) (cb' : List UInt8) (tr : Trace Fp),
      prepV3 (WfClaim.encode c) h = some cb' →
      HoldsP nearAirV3 (Udr.pubOf Fp cb') tr → ∃ w, WfClaim.RelD0a c w := by
  intro c h cb' tr hp hH
  unfold prepV3 at hp
  split at hp
  · rename_i p hprep
    injection hp with hcb'
    subst hcb'
    obtain ⟨k, x, hg⟩ := hext NearSpecV3.B0 (WfClaim.encode c) h p 0 tr hprep hH
    exact ⟨witnessOfV3 k x, (NearSpecV3.relD0a_iff NearSpecV3.B0 (WfClaim.encode c) _).mpr
      (ZkFormal.NearV3.Assembly.factorSound NearSpecV3.B0 (WfClaim.encode c) k h p x hg)⟩
  · exact absurd hp (by simp)

/-- The canonical prepared-statement codec on raw witness bytes: decode the clear
hint, then `prepD0 ∘ Prep.encode`. -/
def prepV3b (cb : List UInt8) (hb : List UInt8) : Option (List UInt8) :=
  (ZkFormal.NearV3.Assembly.Hint.decode hb).bind (prepV3 cb)

/-- **Soundness premise from `ExtractV3Stmt`, on raw witness bytes.** The clear hint
bytes decode to the `Hint` of `ExtractV3Stmt`; the prepared statement is `prepV3`. -/
theorem hsound_of_extract_b (hext : ExtractV3Stmt) :
    ∀ (c : WfClaim) (hb cb' : List UInt8) (tr : Trace Fp),
      prepV3b (WfClaim.encode c) hb = some cb' →
      HoldsP nearAirV3 (Udr.pubOf Fp cb') tr → ∃ w, WfClaim.RelD0a c w := by
  intro c hb cb' tr hp hH
  unfold prepV3b at hp
  rcases hd : ZkFormal.NearV3.Assembly.Hint.decode hb with _ | h
  · rw [hd] at hp; simp at hp
  · rw [hd] at hp; simp only [Option.bind_some] at hp
    exact hsound_of_extract hext c h cb' tr hp hH

/-- **The admission certificate with soundness discharged by `ExtractV3Stmt` and a
concrete raw-hint codec.**  The clear hint is chosen by `hintSel`; the prepared
statement is `prepV3b`.  Only completeness (`hcomp` + `halign`) and the framing
remain. -/
theorem nearV3_admission_with_extract_b (hext : ExtractV3Stmt)
    (art : ArtifactDescription) (pub : List UInt8) (hpub : sha256 pub = art.publicDigest)
    (split : List UInt8 → Option (List UInt8 × List UInt8))
    (join : List UInt8 → List UInt8 → List UInt8)
    (himpl : art.impl.Connection challengeParamsD0a.verifyFuel
      (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier)
    (hintSel : WfClaim → List UInt8 → NearSpecV3.Hint)
    (hsplits : ∀ h π : List UInt8, split (join h π) = some (h, π))
    (traceOf : WfClaim → List UInt8 → Trace Fp)
    (hcomp : ∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      ∃ cb', prepV3b (WfClaim.encode c)
          (ZkFormal.NearV3.Assembly.Hint.encode (hintSel c w)) = some cb' ∧
        HoldsP nearAirV3 (Udr.pubOf Fp cb') (traceOf c w) ∧
        (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk
          (trHdr nearAirV3.toAir (traceOf c w)) = true)
    (halign : ∀ c w, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      RollAligned nearAirV3.toAir ZkFormal.Prover.Np.G.dp
        (trHdr nearAirV3.toAir (traceOf c w)))
    (hjoin : ∀ c w π, challengeSpecD0a.Domain c → challengeSpecD0a.Rel c w →
      π.length ≤ v3MaxInner →
      (join (ZkFormal.NearV3.Assembly.Hint.encode (hintSel c w)) π).length ≤
        challengeParamsD0a.maxProofBytes) :
    AdmissionStatement challengeParamsD0a art :=
  nearV3_admission art pub hpub split prepV3b join himpl
    (fun c w => ZkFormal.NearV3.Assembly.Hint.encode (hintSel c w))
    (fun c w π _ _ => hsplits _ _) traceOf
    (fun c h cb' tr hp hH => hsound_of_extract_b hext c h cb' tr hp hH) hcomp halign hjoin

end ZkFormal.NearV3.Assembly
