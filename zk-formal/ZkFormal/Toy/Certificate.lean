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
other lanes, bundled (IOP completeness, prover budgets and L3 soundness are proved) in `ToyPending`:

| field | statement | owner |
|---|---|---|
| `bcs`, `size` | `Prover.{BcsComplete,Size}Stmt` — false for hash functions with non-32-byte answers; proved for 32-byte ones (`bcs_complete32`, `size32`); closes once L4 normalises answers (`fit32`, R-L7-bcs-1) | L4 + L7-bcs |
| `min8` | admissible headers have `queryLog ≥ 8` (then `QueryOk 24 g2_8` = `udr2_K24_min8_ok`) | L4 (lane/zk-L4e, R-L7-1 decision) |
-/

namespace ZkFormal.Toy

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Prover ZkFormal.Assembly

/-- Open obligations the toy certificate is composed against. -/
structure ToyPending : Prop where
  bcs : BcsCompleteStmt
  size : SizeStmt
  /-- Admissible headers have query domain `≥ 2^8` (R-L7-1 decision (b), L4 lane/zk-L4e). -/
  min8 : ∀ hdr, headerOk toyAir Params.default hdr = true → 8 ≤ queryLog toyAir Params.default hdr

/-- `public.bin` of the toy candidate. -/
def publicBin : Bytes := Bytes.ofString "np-udr-stark-v1/toy-square/v1"

theorem toy_headers (hdr : List Nat) (h : headerOk toyAir Params.default hdr = true) :
    ∃ l, hdr = [l] ∧ l < 17 ∧ 1 ≤ l := by
  match hdr, h with
  | [], h => simp [headerOk, toyAir] at h
  | _ :: _ :: _, h => simp [headerOk, toyAir] at h
  | [l], h =>
    simp only [headerOk, toyAir, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    have := h.1.1.2 (toyTable, l) (by simp)
    exact ⟨l, rfl, Nat.lt_succ_of_le this.1.1.2, this.1.1.1⟩

theorem toy_size_all : ∀ l, l < 17 → 1 ≤ l → sizeBound (Vd toyAir) [l] ≤ 8388608 := by
  decide +kernel

theorem toy_size (hdr : List Nat) (h : headerOk toyAir Params.default hdr = true) :
    sizeBound (Vd toyAir) hdr ≤ 8388608 := by
  obtain ⟨l, rfl, h1, h2⟩ := toy_headers hdr h
  exact toy_size_all l h1 h2

/-- L3's side condition for the toy AIR. -/
theorem toy_npOk : Udr.Np.NpOk toyAir Params.default := by
  refine ⟨rfl, ?_, by decide⟩
  intro T hT
  simp only [toyAir, List.mem_singleton] at hT
  subst hT
  decide

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
  refine np_admission hp.bcs hp.size _ _ publicBin hpub
    toyAir toyAir_tables (by decide) rfl (fun c w => honestTrace w)
    (fun c tr h => toy_sound c tr h)
    (fun c w _ hr => ⟨toy_holds c w hr, toy_header w⟩)
    toy_size (Nat.le_refl _) ?_ ?_ htb rfl rfl 8 g2_8 hp.min8
    g2_8_dom udr2_K24_min8_ok toy_npOk toy_NVu
  · show ZkToySpec.secModelOf model = _
    rw [hmodel]; rfl
  · show AssumptionId.sha256RandomOracle ∈ allowed.flatMap ZkToySpec.assumptionOf
    exact List.mem_flatMap.2 ⟨_, hallowed, by simp [ZkToySpec.assumptionOf]⟩

end ZkFormal.Toy
