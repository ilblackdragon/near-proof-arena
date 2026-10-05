import ZkFormal.Toy.Air
import ZkFormal.Toy.Model
import ZkFormal.Assembly.Admission

/-!
# ZkFormal.Toy.Certificate — M2: the complete admission statement of the toy candidate

`toy_admission`: `AdmissionStatement` for the DEMO toy challenge (`ZkToySpec`), for the
judge-rendered parameters of a `validity-classical-128`-style profile, the native-lean
artifact description with model `Toy.Model.verifier`, and `public.bin = publicBin`.

Everything toy-specific is proved here (AIR soundness/completeness, header/size/
query-budget numerics, public digest is left to the judge-facing module where the
digest literal is known).  The remaining inputs are exactly the open obligations of
other lanes / of L7's own sub-lanes, bundled in `ToyPending`:

| field | statement | owner |
|---|---|---|
| `bcs`, `size`, `proverQ`, `proverChunk` | `Prover.{BcsComplete,Size,ProverQ,ProverChunk}Stmt` | L7-bcs |
| `npIop`, `npProverQ` | `Prover.{NpIopComplete,NpProverQ}Stmt` | L7-iop |
| `rbr` | `Udr.RbrFacts (Iop.verifier Fp Fp8 toyAir default) (AirLang Fp toyAir) Fp8.all 2^36 (agreeUdr 4)` | L3 (`Np.rbr_of` from its open Stmts) |
| `query` | `QueryOk Params.default.numChunks g2_5` | **false for 24 chunks** — R-L7-1 (true after `numChunks := 26`: `udr2_K26_ok`) |
-/

namespace ZkFormal.Toy

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Prover ZkFormal.Assembly

/-- Open obligations the toy certificate is composed against. -/
structure ToyPending : Prop where
  bcs : BcsCompleteStmt
  size : SizeStmt
  proverQ : ProverQStmt
  proverChunk : ProverChunkStmt
  npIop : NpIopCompleteStmt
  npProverQ : NpProverQStmt
  rbr : Udr.RbrFacts (Vd toyAir) (Udr.AirLang Fp toyAir) Fp8.all (2 ^ 36) (Udr.agreeUdr 4)
  query : QueryOk Params.default.numChunks g2_5

/-- `public.bin` of the toy candidate. -/
def publicBin : Bytes := Bytes.ofString "np-udr-stark-v1/toy-square/v1"

theorem toy_headers (hdr : List Nat) (h : headerOk toyAir Params.default hdr = true) :
    hdr = [1] ∨ hdr = [2] ∨ hdr = [3] ∨ hdr = [4] := by
  match hdr, h with
  | [], h => simp [headerOk, toyAir] at h
  | l :: _ :: _, h => simp [headerOk, toyAir] at h
  | [l], h =>
    have hl : 1 ≤ l ∧ l ≤ 4 := by
      simp only [headerOk, toyAir, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      have := h.1.1.2 (toyTable, l) (by simp)
      exact ⟨this.1.1.1, this.1.1.2⟩
    match l, hl with
    | 1, _ => exact Or.inl rfl
    | 2, _ => exact Or.inr (Or.inl rfl)
    | 3, _ => exact Or.inr (Or.inr (Or.inl rfl))
    | 4, _ => exact Or.inr (Or.inr (Or.inr rfl))

theorem toy_size (hdr : List Nat) (h : headerOk toyAir Params.default hdr = true) :
    sizeBound (Vd toyAir) hdr ≤ 8388608 := by
  rcases toy_headers hdr h with rfl | rfl | rfl | rfl <;> decide +kernel

theorem toy_NVu : NVu toyAir Params.default ≤ 2 ^ 30 := by decide +kernel

/-- **M2: the toy admission statement**, from the open obligations. -/
theorem toy_admission (hp : ToyPending) (pid model : String) (tb : Nat) (allowed : List String)
    (fuel rfuel : Nat) (pd bd : Digest) (tid : String)
    (hmodel : model = "random_oracle") (htb : tb ≤ 128)
    (hallowed : "random-oracle-fiat-shamir-sha256" ∈ allowed)
    (hpub : sha256 publicBin = pd) :
    AdmissionStatement
      (ZkToySpec.challengeParamsWith (ZkToySpec.profileOf pid model tb allowed 40 64) fuel 8388608 rfuel)
      { publicDigest := pd, impl := .nativeTrusted bd tid Model.verifier } := by
  obtain ⟨D, hR⟩ := hp.rbr
  refine np_admission hp.bcs hp.size hp.proverQ hp.proverChunk hp.npIop hp.npProverQ _ _ publicBin hpub
    toyAir toyAir_tables rfl (fun c w => honestTrace w)
    (fun c tr h => toy_sound c tr h)
    (fun c w _ hr => ⟨toy_holds c w hr, toy_header w⟩)
    toy_size (Nat.le_refl _) ?_ ?_ htb rfl rfl 5 g2_5
    (fun hdr h => queryLog_ge_of_headerOk toyAir Params.default hdr toyAir_tables h)
    g2_5_dom hp.query D hR toy_NVu
  · show ZkToySpec.secModelOf model = _
    rw [hmodel]; rfl
  · show AssumptionId.sha256RandomOracle ∈ allowed.flatMap ZkToySpec.assumptionOf
    exact List.mem_flatMap.2 ⟨_, hallowed, by simp [ZkToySpec.assumptionOf]⟩

end ZkFormal.Toy
