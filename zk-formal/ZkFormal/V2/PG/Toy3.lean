import ZkFormal.V2.PG.Admission
import ZkFormal.V2.Toy

/-!
# ZkFormal.V2.PG.Toy3 — the toy np-udr-stark-v2 admission at `auxGroup = 3`

`toyP_admission_g3`: `V2.Toy.toyP_admission` re-instantiated through the P2 admission theorem
(`Prover.Np.G.admission_v2`) with the instance `g = 3`, i.e. against the verifier
`verifierP Fp Fp8 toyAirP (pg 3)`.  All numerics are re-checked at `pg 3` by `decide +kernel`
(`toy_npOkPg`, `toy_NVuP`, `toy_sizeMaxSchedP`, `toy_headerP`).  The toy table has no
interactions, so its layout does not depend on `g`; this file exercises the parameter plumbing
of the P2 soundness and completeness chain end to end.
-/

namespace ZkFormal.V2.Toy.G3

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Prover ZkFormal.Assembly ZkFormal.V2.Toy

/-- Group size 3. -/
local instance inst3 : Prover.Np.G.AuxG := ⟨3, by decide⟩

abbrev Vt : IopSpec Fp Fp8 := Prover.Np.G.VdP toyAirP

theorem toy_headerP (c w : Bytes) : Vt.headerOk (trHdr toyAirP.toAir (traceOf c w)) = true := by
  show (headerOk toyAirP.toAir (G.pg 3) [4] &&
    decide (minQueryLog ≤ queryLog toyAirP.toAir (G.pg 3) [4])) = true
  decide +kernel

/-- **Semantic completeness through `prep`.** -/
theorem toy_compP (c w : Bytes) (hd : toySpec.Domain c) (hr : toySpec.Rel c w) :
    ∃ cb', prep (toySpec.encodeClaim c) (hintOf c w) = some cb' ∧
      HoldsP toyAirP (Udr.pubOf Fp cb') (traceOf c w) ∧
      Vt.headerOk (trHdr toyAirP.toAir (traceOf c w)) = true :=
  ⟨enc c w, sorted_perm_prep c w hd hr.1 hr.2, toy_holdsP c w hd hr.1, toy_headerP c w⟩

theorem toy_hsplit (c w π : Bytes) (hd : toySpec.Domain c) (hr : toySpec.Rel c w) :
    split (join (hintOf c w) π) = some (hintOf c w, π) :=
  split_join w π (by have := hr.1.length_eq; show w.length ≤ 64; have : c.length ≤ 64 := hd; omega)

/-! ## Numerics -/

theorem toy_npOkPg : V2.G.NpOkPg toyAirP (G.pg 3) := by
  refine ⟨⟨⟨3, rfl, by decide, by decide⟩, ?_, by decide⟩, by decide +kernel⟩
  intro T hT
  simp only [toyAirP, List.mem_singleton] at hT
  subst hT
  decide

theorem toy_NVuP : NVu toyAirP.toAir (G.pg 3) ≤ 2 ^ 30 := by decide +kernel

/-- Bytes of the inner STARK proof at any admissible header. -/
def maxInner : Nat := 2829897

theorem toy_sizeMaxSchedP : V2.SizeSched.sizeMaxSched toyAirP.toAir (G.pg 3) = maxInner := by
  decide +kernel

/-- `Vt` shares v1's header check, schedule and query parameters. -/
theorem Vt_headerOk (hdr : List Nat) :
    Vt.headerOk hdr = (Iop.verifier Fp Fp8 toyAirP.toAir (G.pg 3)).headerOk hdr := rfl

theorem Vt_schedule : Vt.schedule = (Iop.verifier Fp Fp8 toyAirP.toAir (G.pg 3)).schedule :=
  rfl

theorem Vt_numChunks : Vt.numChunks = (Iop.verifier Fp Fp8 toyAirP.toAir (G.pg 3)).numChunks :=
  rfl

theorem Vt_posPerChunk :
    Vt.posPerChunk = (Iop.verifier Fp Fp8 toyAirP.toAir (G.pg 3)).posPerChunk := rfl

theorem Vt_sizeBound (hdr : List Nat) :
    sizeBound Vt hdr = sizeBound (Iop.verifier Fp Fp8 toyAirP.toAir (G.pg 3)) hdr := by
  unfold sizeBound
  rw [Vt_schedule, Vt_numChunks, Vt_posPerChunk]

theorem toy_sizeP (hdr : List Nat) (h : Vt.headerOk hdr = true) : sizeBound Vt hdr ≤ maxInner := by
  rw [← toy_sizeMaxSchedP, Vt_sizeBound]
  rw [Vt_headerOk] at h
  exact V2.SizeSched.sizeBound_le_sched (F := Fp) (K := Fp8) toyAirP.toAir (G.pg 3) hdr
    (verifier_headerOk h).1

theorem toy_maxInner : maxInner ≤ (G.pg 3).maxProofBytes := by decide

theorem toy_hjoin (c w π : Bytes) (hd : toySpec.Domain c) (hr : toySpec.Rel c w)
    (hπ : π.length ≤ maxInner) : (join (hintOf c w) π).length ≤ 8388608 := by
  have := hr.1.length_eq
  have hd' : c.length ≤ 64 := hd
  have : maxInner + 65 ≤ 8388608 := by decide
  simp only [join, hintOf, List.length_append, List.length_singleton]
  omega

theorem toy_lo (hdr : List Nat) (h : Vt.headerOk hdr = true) :
    8 ≤ queryLog toyAirP.toAir (G.pg 3) hdr := by
  rw [Vt_headerOk] at h
  exact (verifier_headerOk h).2

/-! ## The admission statement -/

/-- **P2: the closed admission statement of the toy np-udr-stark-v2 candidate at
`auxGroup = 3`** (verifier `verifierP Fp Fp8 toyAirP (pg 3)` behind the guard and hint split). -/
theorem toyP_admission_g3 (pid model : String) (tb : Nat) (allowed : List String)
    (fuel rfuel : Nat) (pd bd : Digest) (tid : String)
    (hmodel : model = "random_oracle") (htb : tb ≤ 128)
    (hallowed : "random-oracle-fiat-shamir-sha256" ∈ allowed)
    (hpub : sha256 publicBin = pd) :
    AdmissionStatement
      (challengeParamsWith (profileOf pid model tb allowed 40 64) fuel 8388608 rfuel)
      { publicDigest := pd,
        impl := .nativeTrusted bd tid (Prover.Np.G.npVerifierP toySpec toyAirP split prep).toVerifier } := by
  refine Prover.Np.G.admission_v2 _ _ publicBin hpub toyAirP toyAirP_tables (by decide) split prep join rfl
    hintOf toy_hsplit traceOf (fun c h cb' tr hp hH => toy_soundP c h cb' tr hp hH) toy_compP
    maxInner toy_sizeP toy_maxInner toy_hjoin ?_ ?_ htb rfl rfl 8 g2_8 toy_lo g2_8_dom
    udr2_K24_min8_ok toy_npOkPg toy_NVuP
  · show secModelOf model = _
    rw [hmodel]; rfl
  · show AssumptionId.sha256RandomOracle ∈ allowed.flatMap assumptionOf
    exact List.mem_flatMap.2 ⟨_, hallowed, by simp [assumptionOf]⟩

end ZkFormal.V2.Toy.G3
