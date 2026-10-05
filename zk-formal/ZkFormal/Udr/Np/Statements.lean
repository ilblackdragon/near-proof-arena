import ZkFormal.Udr.Np.Stage

/-!
# ZkFormal.Udr.Np.Statements — obligations for `RbrFacts` of np-udr-stark

`ZkFormal.Udr.Np.Compose` proves
`RbrFacts (Iop.verifier Fp Fp8 A prm) (AirLang Fp A) Fp8.all (2^36) (agreeUdr prm.logBlowup)`
from these.  Notation: `V := Iop.verifier Fp Fp8 A prm`; `E := τ.entries.length`.
The schedule alternates message (even `E`) and challenge (odd `E`) slots.

| Statement | transition | content |
|---|---|---|
| `ShapedPrefixStmt` | – | shapes of extensions restrict to prefixes |
| `ScheduleAltStmt` | – | message slots are exactly the even ones |
| `Msg0Stmt` | main | `¬ InLang ⇒` decoded trace fails or main far (base-field decoding) |
| `Msg2Stmt` | `msg []` after `α_fp` | frame |
| `Msg4Stmt` | aux, finals | aux running-product chain ⇒ grand products; evaluation homomorphism |
| `Msg6Stmt` | quotient | `C_t(h) ≠ 0 = (h^T-1)Q_t(h)` on `H` |
| `Msg8Stmt` | OOD values | DEEP farness / global checks = semantic identity at `z` |
| `MsgLateStmt` | batching / FRI messages | frame (later commitments do not affect earlier conditions) |
| `Chal1Stmt` | `α_fp` | fingerprints (`gpAlpha`) |
| `Chal3Stmt` | `γ` | grand product (`gpGamma`, `Air.multBound`) |
| `Chal5Stmt` | `α_c` | constraint combination (root bound) |
| `Chal7Stmt` | `z` | ALI identity (root bound; `z ∈ F` counted as bad) |
| `ChalLateStmt` | batching `r_k`, FRI `β_i`, `γ_i` | strong line lemma (`strong_line_rs`) |
| `QueryStmt` | query phase | FRI pass-set bound + local bridge from `checkAt` |
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- The per-round bad-challenge budget (`Params.commitBad / 3^8`). -/
def badBudget : Nat := 2 ^ 36

/-- Side conditions on the AIR and parameters used by the proofs (all
decidable on the concrete AIR). -/
def NpOk (A : Air) (prm : Params) : Prop :=
  prm = Params.default ∧
  ∀ T ∈ A.tables, T.allConstraints.length + 2 * T.auxCount prm.auxGroup + 3 * T.interactions.length
    ≤ 2 ^ 20

/-- Shorthand for the verifier. -/
abbrev Vnp (A : Air) (prm : Params) : IopSpec Fp Fp8 := Iop.verifier Fp Fp8 A prm

def ShapedPrefixStmt : Prop :=
  ∀ (A : Air) (prm : Params) (τ : PTn),
    (∀ m, Shaped (Vnp A prm) (τ.push m) → Shaped (Vnp A prm) τ) ∧
    (∀ c, Shaped (Vnp A prm) (τ.pushChal c) → Shaped (Vnp A prm) τ)

def ScheduleAltStmt : Prop :=
  ∀ (A : Air) (prm : Params) (τ : PTn), Shaped (Vnp A prm) τ →
    ((Vnp A prm).NextIsProver τ → τ.entries.length % 2 = 0) ∧
    ((Vnp A prm).NextIsChal τ → τ.entries.length % 2 = 1)

/-- A message transition at `E = k`. -/
def MsgAt (k : Nat) : Prop :=
  ∀ (A : Air) (prm : Params), NpOk A prm → ∀ (τ : PTn) m,
    Shaped (Vnp A prm) (τ.push m) → (Vnp A prm).NextIsProver τ → τ.entries.length = k →
    Stage A prm τ → Stage A prm (τ.push m)

/-- A challenge transition at `E = k`. -/
def ChalAt (k : Nat) : Prop :=
  ∀ (A : Air) (prm : Params), NpOk A prm → ∀ τ : PTn,
    Shaped (Vnp A prm) τ → (Vnp A prm).NextIsChal τ → τ.entries.length = k → Stage A prm τ →
    count Fp8.all (fun c => Shaped (Vnp A prm) (τ.pushChal c) ∧ ¬ Stage A prm (τ.pushChal c)) ≤ badBudget

def Msg0Stmt : Prop := MsgAt 0
def Msg2Stmt : Prop := MsgAt 2
def Msg4Stmt : Prop := MsgAt 4
def Msg6Stmt : Prop := MsgAt 6
def Msg8Stmt : Prop := MsgAt 8
def MsgLateStmt : Prop := ∀ k, 10 ≤ k → MsgAt k
def Chal1Stmt : Prop := ChalAt 1
def Chal3Stmt : Prop := ChalAt 3
def Chal5Stmt : Prop := ChalAt 5
def Chal7Stmt : Prop := ChalAt 7
def ChalLateStmt : Prop := ∀ k, 9 ≤ k → ChalAt k

def QueryStmt : Prop :=
  ∀ (A : Air) (prm : Params), NpOk A prm → ∀ τ : PTn,
    Stage A prm τ → (Vnp A prm).AtQuery τ → Shaped (Vnp A prm) τ →
    (Vnp A prm).global ((Vnp A prm).prep τ.erase) = true →
    count (List.range ((Vnp A prm).domSize τ))
      (fun x => (Vnp A prm).ChecksPass τ x ((Vnp A prm).trueOpenings τ x)) ≤
      agreeUdr prm.logBlowup ((Vnp A prm).domSize τ)

end ZkFormal.Udr.Np
