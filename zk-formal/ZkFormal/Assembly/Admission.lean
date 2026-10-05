import ZkFormal.Assembly.RomFull
import ZkFormal.Prover.Compose
import ZkFormal.Prover.NpLocalMain
import ZkFormal.Prover.NpQ
import ZkFormal.Prover.BcsQuery
import ZkFormal.Prover.BcsChunk

/-!
# ZkFormal.Assembly.Admission — the judge's `AdmissionStatement` for an np-udr-stark candidate

`np_admission` assembles the whole certificate for any challenge `ch` (random-oracle
profile, target ≤ 128 bits, budgets 2^64 / 2^40) and any AIR `A`:

| conjunct | from |
|---|---|
| public digest | `hpub` (kernel `sha256` of the concrete `public.bin`) |
| `FORMAL_IMPL_CONNECTION` | `himpl` (`rfl` on the native-lean route) |
| `FORMAL_SEMANTIC_SOUNDNESS` | `hsound` — the AIR's soundness (L5/L6) |
| `FORMAL_SEMANTIC_COMPLETENESS` | `hcomp` — the AIR's completeness (L5/L6) |
| `VerifierComplete` | `np_proverComplete` at `H = sha256(roTag ‖ ·)` |
| `CryptoSound` (ROM) | `np_proverComplete` (every `H`), `stark_romSound_full` (L3 `rbrWith` ∘ L2 transport ∘ L4 facts, kernel numerics), `romSound_guard` |

The backend is `B c tr := Holds A (pubOf (encodeClaim c)) tr`.  The deployed verifier
is `npVerifier ch.spec A` (claim guard ∘ L4's compiled verifier, see `Guard.lean`).
-/

namespace ZkFormal.Assembly

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Prover

/-- The np backend: AIR traces for the claim's canonical bytes. -/
def npBackend (S : ChallengeSpec) (A : Air) : Backend S :=
  ⟨Trace Fp, fun c tr => Holds A (Udr.pubOf Fp (S.encodeClaim c)) tr⟩

theorem inLang_of_guard (S : ChallengeSpec) (A : Air) (cb : Bytes) (hok : claimOk S cb = true)
    (h : Udr.AirLang Fp A cb) : (npBackend S A).InLang cb := by
  obtain ⟨c, hc, he⟩ := claimOk_iff S cb hok
  obtain ⟨tr, htr⟩ := h
  exact ⟨c, hc, tr, by show Holds A (Udr.pubOf Fp (S.encodeClaim c)) tr; rw [he]; exact htr⟩

/-- **The admission certificate of an np-udr-stark candidate**, from the open
obligations of the prover model (`Prover.Statements`), L3's decidable `NpOk`, the AIR's
semantic soundness/completeness and the concrete numeric checks. -/
theorem np_admission
    (ch : ChallengeParams) (art : ArtifactDescription) (pub : Bytes)
    (hpub : sha256 pub = art.publicDigest)
    (A : Air) (hA : A.tables ≠ []) (htab : A.tables.length < 2 ^ 32)
    (himpl : art.impl.Connection ch.verifyFuel (npVerifier ch.spec A).toVerifier)
    (traceOf : ch.spec.Claim → ch.spec.Witness → Trace Fp)
    (hsound : ∀ c tr, Holds A (Udr.pubOf Fp (ch.spec.encodeClaim c)) tr → ∃ w, ch.spec.Rel c w)
    (hcomp : ∀ c w, ch.spec.Domain c → ch.spec.Rel c w →
      Holds A (Udr.pubOf Fp (ch.spec.encodeClaim c)) (traceOf c w) ∧
      (Vd A).headerOk (trHdr A (traceOf c w)) = true)
    (hsize : ∀ hdr, (Vd A).headerOk hdr = true → sizeBound (Vd A) hdr ≤ ch.maxProofBytes)
    (hmax : ch.maxProofBytes ≤ Params.default.maxProofBytes)
    (hmodel : ch.profile.model = .randomOracle)
    (hassm : AssumptionId.sha256RandomOracle ∈ ch.profile.allowedAssumptions)
    (htb : ch.profile.targetBits ≤ 128) (hqh : ch.profile.maxHashQueriesLog2 = 64)
    (hqp : ch.profile.maxProverQueriesLog2 = 40)
    (lo g : Nat) (hlo : ∀ hdr, (Vd A).headerOk hdr = true → lo ≤ queryLog A Params.default hdr)
    (hdom : Dominates (Udr.agreeUdr 4) lo g) (hq : QueryOk Params.default.numChunks g)
    (hok : Udr.Np.NpOk A Params.default)
    (hNV : NVu A Params.default ≤ 2 ^ 30) :
    AdmissionStatement ch art := by
  let P := npProver ch.spec A traceOf
  have hPC := np_proverComplete ch.spec A
    (fun cb tr h hh => Np.npIopComplete' A cb tr htab h hh) traceOf hcomp ch.maxProofBytes hsize hmax pub
  refine ⟨pub, (npVerifier ch.spec A).toVerifier, hpub, himpl, npBackend ch.spec A, ?_, ?_, ?_, ?_⟩
  · intro c tr h; exact hsound c tr h
  · intro c w hd hr; exact ⟨traceOf c w, (hcomp c w hd hr).1⟩
  · intro c w hd hr
    obtain ⟨hl, hacc⟩ := hPC (fun m => sha256 (Interp.roTag ++ m)) c w hd hr
    exact ⟨_, hl, hacc⟩
  · right
    rw [hmodel]
    refine ⟨hassm, P.toProver, hPC, ?_⟩
    obtain ⟨tapeLen, num, den, hb, hrom⟩ := stark_romSound_full A Params.default hok lo g hlo hdom hq
      hNV P pub (2 ^ 32) (Nat.le_refl _) (np_prover_unit prover_unit ch.spec A
        (fun hdr h => Np.npProverQ A hdr hNV h) hA traceOf pub)
      (np_prover_chunk prover_chunk ch.spec A traceOf pub)
    refine ⟨tapeLen, num, den, ?_, ?_⟩
    · exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) htb)) hb
    · rw [hqh, hqp]
      exact romSound_guard (claimOk ch.spec) (inLang_of_guard ch.spec A) _ _ pub hrom

end ZkFormal.Assembly
