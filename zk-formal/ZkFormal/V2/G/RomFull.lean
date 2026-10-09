import ZkFormal.V2.RomFull
import ZkFormal.V2.G.Main

/-!
# ZkFormal.V2.G.RomFull — `stark_romSound_fullPg`: v2's closed soundness chain at `pg g`

`V2.stark_romSound_fullP` with `NpOkPg` (any `auxGroup = g`, `1 ≤ g ≤ 3`) in place of
`NpOkP` (`auxGroup = 1`).  Only L3 (`G.rbrWithPg`) depends on `g`; the L2 transport, the
L4 schedule/query facts (`schedOkP`, `npBoundsP`, `verifierP_queryBound`) are generic in
`prm`, and the numerics only read `numChunks`, `posPerChunk`, `posBits`, `logBlowup`.
-/

namespace ZkFormal.V2

open ArenaCore ArenaCore.Security ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra ZkFormal.Assembly

/-- **ROM soundness of the np-udr-stark-v2 verifier with `auxGroup = g ∈ {1,2,3}`, all lanes composed.** -/
theorem stark_romSound_fullPg (AP : AirP) (prm : Params) (hok : V2.G.NpOkPg AP prm)
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
  obtain ⟨⟨⟨gg, hprm0, hg1, hg3⟩, h1, h2⟩, h3⟩ := hok
  subst hprm0
  have hprm : ShapeOk (G.pg gg) := ⟨rfl, rfl, rfl, ShapeOk.default.k2, ShapeOk.default.k32⟩
  let V := Iop.verifierP Fp Fp8 AP (G.pg gg)
  have hS : Bcs.Adapter.SchedOk V := schedOkP AP (G.pg gg)
  have hql : ∀ hdr, V.headerOk hdr = true → V.queryLog hdr ≤ V.posBits :=
    np_queryLog_le_posBits Fp Fp8 AP.toAir (G.pg gg)
  have hG : ∀ hdr, V.headerOk hdr = true →
      Udr.agreeUdr (G.pg gg).logBlowup (2 ^ V.queryLog hdr) ^ V.posPerChunk *
        2 ^ (256 - V.posPerChunk * V.queryLog hdr) ≤ g := by
    intro hdr h
    have hub := hql hdr h
    change queryLog AP.toAir (G.pg gg) hdr ≤ 26 at hub
    change Udr.agreeUdr 4 (2 ^ queryLog AP.toAir (G.pg gg) hdr) ^ 9 *
        2 ^ (256 - 9 * queryLog AP.toAir (G.pg gg) hdr) ≤ g
    exact hdom _ (by omega) (hlo hdr h)
  have hpb : V.posPerChunk * V.posBits ≤ 256 := by change 9 * 26 ≤ 256; decide
  have hp : 0 < V.posPerChunk := by change 0 < 9; decide
  have hN : 2 ^ 64 + 2 ^ 40 * NPu + NVu AP.toAir (G.pg gg) ≤ 2 ^ 100 := by
    have : 2 ^ 40 * NPu ≤ 2 ^ 40 * 2 ^ 32 := Nat.mul_le_mul_left _ hNP
    have e : (2 : Nat) ^ 40 * 2 ^ 32 = 2 ^ 72 := by rw [← Nat.pow_add]
    have : (2 : Nat) ^ 64 + 2 ^ 72 + 2 ^ 30 ≤ 2 ^ 100 := by decide
    omega
  have hR := V2.G.rbrWithPg AP (G.pg gg) ⟨⟨⟨gg, rfl, hg1, hg3⟩, h1, h2⟩, h3⟩
  have hrom := Bcs.Transport.stark_romSound_rbr V hS hprm.k2 hprm.k32
    (V2.Np.AirLangP AP) Fp8.all (2 ^ 36) (Udr.agreeUdr (G.pg gg).logBlowup) _ hR (2 * 3 ^ 8)
    (Bcs.Transport.hdec_deployed) hp hpb hql g hG P pub (2 ^ 64) (2 ^ 40) NPu (NVu AP.toAir (G.pg gg))
    (G.pg gg).numChunks (G.pg gg).numChunks hN hPu
    (fun cb pb => verifierP_queryBound AP (G.pg gg) pub cb pb) hPq
    (fun cb pb => chunk_queryBound Fp Fp8 V pub cb pb)
  refine ⟨_, _, _, ?_, hrom⟩
  exact full_ok (G.pg gg).numChunks g NPu (NVu AP.toAir (G.pg gg)) hprm.k2 hNP hNV hq


end ZkFormal.V2
