import ZkFormal.Assembly.RomBound
import ZkFormal.Udr.Np.Main

/-!
# ZkFormal.Assembly.RomFull — `stark_romSound_full`: the closed soundness chain

L3 (`Udr.Np.rbrWith`) ∘ L2 (`stark_romSound_rbr`) ∘ L4 (`schedOk`, `L2Facts`,
`ChunkBound`) ∘ L1 (`hdec_deployed`) ∘ L7 numerics, for the deployed verifier of any
AIR satisfying L3's decidable side condition `NpOk`.

Remaining inputs: `NpOk A prm` (decidable), a chunk-good dominator `g` over the
admissible query domains with `QueryOk prm.numChunks g` (kernel), `NVu ≤ 2^30`
(kernel on the concrete AIR), and the honest prover's budgets.

**Caveat (R-L7-1).** `Params.udr2'_ok` checks the bound only at the largest domain
`n = 2^26`.  The adversary chooses the header, and admissible headers allow query
domains down to `2^5`, where 24 chunks give ≈ 2^-115 (`udr2_K24_q5_fails`).  So
`QueryOk 24 g` is unprovable for any `g` dominating `q = 5`; with `numChunks = 26`
it holds (`udr2_K26_ok`).
-/

namespace ZkFormal.Assembly

open ArenaCore ArenaCore.Security ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- **ROM soundness of the deployed np-udr-stark verifier, all lanes composed.** -/
theorem stark_romSound_full (A : Air) (prm : Params) (hok : Udr.Np.NpOk A prm)
    (lo g : Nat) (hlo : ∀ hdr, (Iop.verifier Fp Fp8 A prm).headerOk hdr = true → lo ≤ queryLog A prm hdr)
    (hdom : Dominates (Udr.agreeUdr 4) lo g) (hq : QueryOk prm.numChunks g)
    (hNV : NVu A prm ≤ 2 ^ 30)
    {S : ChallengeSpec} (P : TreeProver S) (pub : Bytes) (NPu : Nat) (hNP : NPu ≤ 2 ^ 32)
    (hPu : ∀ c w, OracleComp.QueryBound unitWeight (P.tree pub c w) NPu)
    (hPq : ∀ c w, OracleComp.QueryBound (qWeight Bcs.chunkDec) (P.tree pub c w) prm.numChunks) :
    ∃ tapeLen num den : Nat, num * 2 ^ 128 ≤ den ∧
      RomSound S (Udr.AirLang Fp A) (verifier Fp Fp8 A prm).toVerifier P.toProver pub
        (2 ^ 64) (2 ^ 40) tapeLen num den := by
  obtain rfl : prm = Params.default := hok.1
  exact np_romSound A Params.default ShapeOk.default lo g hlo hdom hq (Udr.Np.Doomed A Params.default)
    (Udr.Np.rbrWith A Params.default hok) hNV P pub NPu hNP hPu hPq

/-- Same, with the admissible-domain floor `2^5` of any non-empty AIR and `g = g2_5`:
only `NpOk`, `QueryOk numChunks g2_5`, `NVu` and the prover budgets remain. -/
theorem stark_romSound_full' (A : Air) (prm : Params) (hok : Udr.Np.NpOk A prm) (hA : A.tables ≠ [])
    (hq : QueryOk prm.numChunks g2_5) (hNV : NVu A prm ≤ 2 ^ 30)
    {S : ChallengeSpec} (P : TreeProver S) (pub : Bytes) (NPu : Nat) (hNP : NPu ≤ 2 ^ 32)
    (hPu : ∀ c w, OracleComp.QueryBound unitWeight (P.tree pub c w) NPu)
    (hPq : ∀ c w, OracleComp.QueryBound (qWeight Bcs.chunkDec) (P.tree pub c w) prm.numChunks) :
    ∃ tapeLen num den : Nat, num * 2 ^ 128 ≤ den ∧
      RomSound S (Udr.AirLang Fp A) (verifier Fp Fp8 A prm).toVerifier P.toProver pub
        (2 ^ 64) (2 ^ 40) tapeLen num den := by
  have hprm : prm = Params.default := hok.1
  refine stark_romSound_full A prm hok 5 g2_5 (fun hdr h => ?_) g2_5_dom hq hNV P pub NPu hNP hPu hPq
  have := queryLog_ge_of_headerOk A prm hdr hA (verifier_headerOk h).1
  rw [hprm] at this ⊢; exact this

end ZkFormal.Assembly
