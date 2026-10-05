import ZkFormal.Assembly.Params
import ZkFormal.Stark.L2Facts
import ZkFormal.Stark.ChunkBound
import ZkFormal.Stark.Instance
import ZkFormal.Stark.SchedOk

/-!
# ZkFormal.Assembly.RomBound — `CryptoSound`'s ROM conjunct for np-udr-stark (lane L7)

`np_romSound`: for any AIR `A` and any parameter set with 9 positions of 26 bits
and blowup 16, L3's round-by-round facts `RbrWith (Iop.verifier Fp Fp8 A prm)
(AirLang Fp A) Fp8.all 2^36 (= Udr.Np.badBudget) (agreeUdr 4) D` and the honest prover's query
budgets give the judge's `RomSound` at the profile budgets (2^64 / 2^40) with a
bound `num/den`, `num · 2^128 ≤ den`, as soon as a concrete `g` dominates the
chunk-good count on the admissible domains and passes `QueryOk` (kernel).

All verifier-side hypotheses of `Bcs.Transport.stark_romSound_rbr` are
discharged here from L4 (`SchedOk`, `L2Facts`, `ChunkBound`) and L1/L2
(`hdec_deployed`).
-/

namespace ZkFormal.Assembly

open ArenaCore ArenaCore.Security ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- Every admissible header of an AIR with at least one table has query domain
`≥ 2^(1 + logBlowup)`. -/
theorem queryLog_ge_of_headerOk (A : Air) (prm : Params) (hdr : List Nat) (hA : A.tables ≠ [])
    (h : headerOk A prm hdr = true) : 1 + prm.logBlowup ≤ queryLog A prm hdr := by
  simp only [headerOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hlen, hall⟩, _⟩, _⟩ := h
  obtain ⟨T, Ts, hT⟩ : ∃ T Ts, A.tables = T :: Ts := by
    cases h' : A.tables with
    | nil => exact absurd h' hA
    | cons T Ts => exact ⟨T, Ts, rfl⟩
  obtain ⟨l, ls, hhd⟩ : ∃ l ls, hdr = l :: ls := by
    cases hdr with
    | nil => rw [hT] at hlen; simp at hlen
    | cons l ls => exact ⟨l, ls, rfl⟩
  subst hhd
  have hl := (hall (T, l) (by rw [hT]; exact List.mem_cons_self)).1.1.1
  have hmem : l + prm.logBlowup ∈ (layout A prm (l :: ls)).map (·.lde) := by
    simp [layout, hT]
  have := le_foldr_max (b := 0) hmem
  unfold queryLog; omega

/-- Profile shape of the parameters used by the numeric checks. -/
structure ShapeOk (prm : Params) : Prop where
  ppc : prm.posPerChunk = 9
  bits : prm.posBits = 26
  blow : prm.logBlowup = 4
  k2 : 2 ≤ prm.numChunks
  k32 : prm.numChunks ≤ 2 ^ 32

theorem ShapeOk.default : ShapeOk Params.default := ⟨rfl, rfl, rfl, by decide, by decide⟩

/-- **ROM soundness at 2^-128 for np-udr-stark**, from L3's `RbrWith`. -/
theorem np_romSound (A : Air) (prm : Params) (hprm : ShapeOk prm)
    (lo g : Nat) (hlo : ∀ hdr, (Iop.verifier Fp Fp8 A prm).headerOk hdr = true → lo ≤ queryLog A prm hdr)
    (hdom : Dominates (Udr.agreeUdr 4) lo g) (hq : QueryOk prm.numChunks g)
    (D : PT Fp8 (Oracle Fp) → Prop)
    (hR : Udr.RbrWith (Iop.verifier Fp Fp8 A prm) (Udr.AirLang Fp A) Fp8.all (2 ^ 36)
      (Udr.agreeUdr prm.logBlowup) D)
    (hNV : NVu A prm ≤ 2 ^ 30)
    {S : ChallengeSpec} (P : TreeProver S) (pub : Bytes) (NPu : Nat) (hNP : NPu ≤ 2 ^ 32)
    (hPu : ∀ c w, OracleComp.QueryBound unitWeight (P.tree pub c w) NPu)
    (hPq : ∀ c w, OracleComp.QueryBound (qWeight Bcs.chunkDec) (P.tree pub c w) prm.numChunks) :
    ∃ tapeLen num den : Nat, num * 2 ^ 128 ≤ den ∧
      RomSound S (Udr.AirLang Fp A) (verifier Fp Fp8 A prm).toVerifier P.toProver pub
        (2 ^ 64) (2 ^ 40) tapeLen num den := by
  have hS := schedOk (F := Fp) (K := Fp8) A prm
  have hG : ∀ hdr, (Iop.verifier Fp Fp8 A prm).headerOk hdr = true →
      Udr.agreeUdr prm.logBlowup (2 ^ (Iop.verifier Fp Fp8 A prm).queryLog hdr) ^
          (Iop.verifier Fp Fp8 A prm).posPerChunk *
        2 ^ (256 - (Iop.verifier Fp Fp8 A prm).posPerChunk * (Iop.verifier Fp Fp8 A prm).queryLog hdr)
        ≤ g := by
    intro hdr h
    have hub := np_queryLog_le_posBits Fp Fp8 A prm hdr h
    change queryLog A prm hdr ≤ prm.posBits at hub
    change Udr.agreeUdr prm.logBlowup (2 ^ queryLog A prm hdr) ^ prm.posPerChunk *
        2 ^ (256 - prm.posPerChunk * queryLog A prm hdr) ≤ g
    rw [hprm.ppc, hprm.blow]
    rw [hprm.bits] at hub
    exact hdom _ (by omega) (hlo hdr h)
  have hql : ∀ hdr, (Iop.verifier Fp Fp8 A prm).headerOk hdr = true →
      (Iop.verifier Fp Fp8 A prm).queryLog hdr ≤ (Iop.verifier Fp Fp8 A prm).posBits :=
    np_queryLog_le_posBits Fp Fp8 A prm
  have hpb : (Iop.verifier Fp Fp8 A prm).posPerChunk * (Iop.verifier Fp Fp8 A prm).posBits ≤ 256 := by
    change prm.posPerChunk * prm.posBits ≤ 256
    rw [hprm.ppc, hprm.bits]; decide
  have hp : 0 < (Iop.verifier Fp Fp8 A prm).posPerChunk := by
    change 0 < prm.posPerChunk
    rw [hprm.ppc]; decide
  have hN : 2 ^ 64 + 2 ^ 40 * NPu + NVu A prm ≤ 2 ^ 100 := by
    have : 2 ^ 40 * NPu ≤ 2 ^ 40 * 2 ^ 32 := Nat.mul_le_mul_left _ hNP
    have e : (2 : Nat) ^ 40 * 2 ^ 32 = 2 ^ 72 := by rw [← Nat.pow_add]
    have : (2 : Nat) ^ 64 + 2 ^ 72 + 2 ^ 30 ≤ 2 ^ 100 := by decide
    omega
  have hrom := Bcs.Transport.stark_romSound_rbr (Iop.verifier Fp Fp8 A prm) hS hprm.k2 hprm.k32
    (Udr.AirLang Fp A) Fp8.all (2 ^ 36) (Udr.agreeUdr prm.logBlowup) D hR (2 * 3 ^ 8)
    (Bcs.Transport.hdec_deployed) hp hpb hql g hG P pub (2 ^ 64) (2 ^ 40) NPu (NVu A prm)
    prm.numChunks prm.numChunks hN hPu (np_starkTree_unit Fp Fp8 A prm pub) hPq
    (np_starkTree_chunk (F := Fp) (K := Fp8) A prm pub)
  refine ⟨_, _, _, ?_, hrom⟩
  exact full_ok prm.numChunks g NPu (NVu A prm) hprm.k2 hNP hNV hq

end ZkFormal.Assembly
