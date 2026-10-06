import ZkFormal.Assembly.RomFull
import ZkFormal.V2.Np.Main

/-!
# ZkFormal.V2.RomFull — `stark_romSound_fullP`: the closed soundness chain of v2

L3 (`V2.Np.rbrWithP`) ∘ L2 (`Bcs.Transport.stark_romSound_rbr`, generic in the IOP)
∘ L4 facts ∘ L1 ∘ L7 numerics, for the deployed v2 verifier `verifierP Fp Fp8 AP prm`.

v2's IOP has v1's header check, schedule, query rule and size cap.  So every
verifier-side side condition of L2's transport transfers from v1 field by field:
* `schedOkP`, from v1's `schedOk`;
* the unit query budget `NVu AP.toAir prm`, from v1's `np_bounds` and the generic
  `compile_queryBound`;
* the chunk budget, from the generic `chunk_queryBound`.
The numerics (`QueryOk`, `full_ok`) are v1's: the bound is the same, `num · 2^128 ≤ den`.
-/

namespace ZkFormal.V2

open ArenaCore ArenaCore.Security ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra ZkFormal.Assembly

section
variable {F K : Type} [Lean.Grind.Field F] [Lean.Grind.Field K] [StarkField F K] [DecidableEq F]
  [DecidableEq K] [PubVal F]

theorem schedOkP (AP : AirP) (prm : Params) : Bcs.Adapter.SchedOk (Iop.verifierP F K AP prm) :=
  let h := schedOk (F := F) (K := K) AP.toAir prm
  ⟨h.first, h.roots, h.depth⟩

theorem npBoundsP (AP : AirP) (prm : Params) :
    IopBounds (Iop.verifierP F K AP prm) (schedBound AP.toAir prm) (oracleBound prm) prm.maxLogLde :=
  let h := np_bounds F K AP.toAir prm
  ⟨h.sched, h.oracles, h.depth⟩

/-- Unit query budget of the deployed v2 verifier: v1's `NVu`. -/
theorem verifierP_queryBound (AP : AirP) (prm : Params) (pub cb pb : Bytes) :
    OracleComp.QueryBound unitWeight ((verifierP F K AP prm).tree pub cb pb) (NVu AP.toAir prm) := by
  rw [verifierP_eq_compile]
  have := compile_queryBound F K (Iop.verifierP F K AP prm) _ _ _ (npBoundsP AP prm) pub cb pb
  exact this

end

/-- **ROM soundness of the deployed np-udr-stark-v2 verifier, all lanes composed.** -/
theorem stark_romSound_fullP (AP : AirP) (prm : Params) (hok : V2.Np.NpOkP AP prm)
    (lo g : Nat) (hlo : ∀ hdr, (Iop.verifierP Fp Fp8 AP prm).headerOk hdr = true →
      lo ≤ queryLog AP.toAir prm hdr)
    (hdom : Dominates (Udr.agreeUdr 4) lo g) (hq : QueryOk prm.numChunks g)
    (hNV : NVu AP.toAir prm ≤ 2 ^ 30)
    {S : ChallengeSpec} (P : TreeProver S) (pub : Bytes) (NPu : Nat) (hNP : NPu ≤ 2 ^ 32)
    (hPu : ∀ c w, OracleComp.QueryBound unitWeight (P.tree pub c w) NPu)
    (hPq : ∀ c w, OracleComp.QueryBound (qWeight Bcs.chunkDec) (P.tree pub c w) prm.numChunks) :
    ∃ tapeLen num den : Nat, num * 2 ^ 128 ≤ den ∧
      RomSound S (V2.Np.AirLangP AP) (verifierP Fp Fp8 AP prm).toVerifier P.toProver pub
        (2 ^ 64) (2 ^ 40) tapeLen num den := by
  obtain ⟨⟨hprm0, h1, h2⟩, h3⟩ := hok
  subst hprm0
  have hprm := ShapeOk.default
  let V := Iop.verifierP Fp Fp8 AP Params.default
  have hS : Bcs.Adapter.SchedOk V := schedOkP AP Params.default
  have hql : ∀ hdr, V.headerOk hdr = true → V.queryLog hdr ≤ V.posBits :=
    np_queryLog_le_posBits Fp Fp8 AP.toAir Params.default
  have hG : ∀ hdr, V.headerOk hdr = true →
      Udr.agreeUdr Params.default.logBlowup (2 ^ V.queryLog hdr) ^ V.posPerChunk *
        2 ^ (256 - V.posPerChunk * V.queryLog hdr) ≤ g := by
    intro hdr h
    have hub := hql hdr h
    change queryLog AP.toAir Params.default hdr ≤ 26 at hub
    change Udr.agreeUdr 4 (2 ^ queryLog AP.toAir Params.default hdr) ^ 9 *
        2 ^ (256 - 9 * queryLog AP.toAir Params.default hdr) ≤ g
    exact hdom _ (by omega) (hlo hdr h)
  have hpb : V.posPerChunk * V.posBits ≤ 256 := by change 9 * 26 ≤ 256; decide
  have hp : 0 < V.posPerChunk := by change 0 < 9; decide
  have hN : 2 ^ 64 + 2 ^ 40 * NPu + NVu AP.toAir Params.default ≤ 2 ^ 100 := by
    have : 2 ^ 40 * NPu ≤ 2 ^ 40 * 2 ^ 32 := Nat.mul_le_mul_left _ hNP
    have e : (2 : Nat) ^ 40 * 2 ^ 32 = 2 ^ 72 := by rw [← Nat.pow_add]
    have : (2 : Nat) ^ 64 + 2 ^ 72 + 2 ^ 30 ≤ 2 ^ 100 := by decide
    omega
  have hR := V2.Np.rbrWithP AP Params.default ⟨⟨rfl, h1, h2⟩, h3⟩
  have hrom := Bcs.Transport.stark_romSound_rbr V hS hprm.k2 hprm.k32
    (V2.Np.AirLangP AP) Fp8.all (2 ^ 36) (Udr.agreeUdr Params.default.logBlowup) _ hR (2 * 3 ^ 8)
    (Bcs.Transport.hdec_deployed) hp hpb hql g hG P pub (2 ^ 64) (2 ^ 40) NPu (NVu AP.toAir Params.default)
    Params.default.numChunks Params.default.numChunks hN hPu
    (fun cb pb => verifierP_queryBound AP Params.default pub cb pb) hPq
    (fun cb pb => chunk_queryBound Fp Fp8 V pub cb pb)
  refine ⟨_, _, _, ?_, hrom⟩
  exact full_ok Params.default.numChunks g NPu (NVu AP.toAir Params.default) hprm.k2 hNP hNV hq

end ZkFormal.V2
