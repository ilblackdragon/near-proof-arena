import NearSpecV3.D3.FunctionCall
import NearSpecV3.D3.Signed
import NearSpecV3.ChunkValidationV0a
import NearSpecV3.ChunkValidationD1a

/-!
# The domain rungs as restrictions of the top relation (decision 2026-10-30, option 1) — definitions

Definitions and the projection lemmas only (the trusted part the `near-chunk-v3-1` statement
imports); the checker admission lemmas are in `Rungs.lean`.

The `near-chunk-v3` v3.0 statement is the union `RelD0 ∨ RelD1 ∨ RelD2 ∨ RelD3` of four separate
transcriptions. Its rung inclusions were tested, not proved, and `D1 ⊂ D2` turned out false
(`Examples/D1NotSubD2.lean`: D0/D1 never compare the `epoch_start_after` flags with the headers).
The owner's decision is the follow-up `docs/CONTRACTS.md` already proposed: **each rung is the top
relation restricted to its domain**,

  `RelRungDk cb w := RelD3 cb w ∧ InRungDk cb w`,

so every inclusion is a projection and the statement collapses to `RelD3`.

## The domains

`DomDk cb w` says that the rung's own checker does not report an exclusion (`out of domain …`): it
carries exactly the domain restrictions that rung had — D0's receipt-only witnesses, D1's
Transfer-only transactions and receipts, the codecs each decoder admits, the D0a/D1a amendments
(gas limit, proof routing, canonical scheduler state, unfolded-trie / ChaCha / depth / transaction
bounds) and every `c.*` / `w.*` / `e.*` / `r.*` exclusion. Where the checker rejects (`invalid: …`)
before reaching a later domain check, the domain predicate holds; in the rung relation that case
also requires `RelD3`, i.e. it is decided by the top relation.

`InRungDk` is cumulative along the order the statement uses (`D0a ⊂ D0 ⊂ D1 ⊂ D2`,
`D1a ⊂ D1`), so the inclusions are definitional:

| rung | `InRung` |
|---|---|
| D2 | `DomD2` |
| D1 | `DomD1 ∧ InRungD2` |
| D1a | `DomD1a B ∧ InRungD1` |
| D0 | `DomD0 ∧ InRungD1` |
| D0a | `DomD0a B ∧ InRungD0` |

## The fast checkers

The old checkers stay as executable implementations. `checkD2` accepts only `RelRungD2` chunks
(`rungD2_of_checkD2`, via `relD2_relD3`). For D0/D0a/D1/D1a this does **not** hold alone — the
genesis-flag counterexample is a `checkD1` accept outside `RelRungD1`
(`Examples.not_rungD1_of_checkD1`) — but it holds when `checkD2` accepts too
(`rungD1_of_checks`, `rungD1a_of_checks`, `rungD0_of_checks`, `rungD0a_of_checks`), so a lower-rung
prover is admitted together with a D2 run.

The checker relations `RelD0`, `RelD0a`, `RelD1`, `RelD1a`, `RelD2` keep their meaning
(checker acceptance): they are the statements of the separate D0/D0a/D1 challenges (the signed
`near-chunk-validation-d0` declares `NearSpecV3.RelD0`) and of the zk-formal D0a/D1a proof stack.
-/

namespace NearSpecV3

open NearSpec

/-- The checker does not report an exclusion. -/
def notExcluded (r : Except String Unit) : Bool :=
  match r with
  | .ok _ => true
  | .error e => !(e.toList.take 13 == "out of domain".toList)

def DomD0 (cb w : Bytes) : Bool := notExcluded (checkD0 cb w)
def DomD0a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) : Bool :=
  notExcluded (checkD0a B cb w W Dp)
def DomD1 (cb w : Bytes) : Bool := notExcluded (checkD1 cb w)
def DomD1a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) (N : Nat := NT0) : Bool :=
  notExcluded (checkD1a B cb w W Dp N)
def DomD2 (cb w : Bytes) : Bool := notExcluded (checkD2 cb w)

/-! ## The cumulative domains and the rung relations -/

def InRungD2 (cb w : Bytes) : Prop := DomD2 cb w = true
def InRungD1 (cb w : Bytes) : Prop := DomD1 cb w = true ∧ InRungD2 cb w
def InRungD1a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) (N : Nat := NT0) : Prop :=
  DomD1a B cb w W Dp N = true ∧ InRungD1 cb w
def InRungD0 (cb w : Bytes) : Prop := DomD0 cb w = true ∧ InRungD1 cb w
def InRungD0a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) : Prop :=
  DomD0a B cb w W Dp = true ∧ InRungD0 cb w

def RelRungD2 (cb w : Bytes) : Prop := D3.RelD3 cb w ∧ InRungD2 cb w
def RelRungD1 (cb w : Bytes) : Prop := D3.RelD3 cb w ∧ InRungD1 cb w
def RelRungD1a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) (N : Nat := NT0) : Prop :=
  D3.RelD3 cb w ∧ InRungD1a B cb w W Dp N
def RelRungD0 (cb w : Bytes) : Prop := D3.RelD3 cb w ∧ InRungD0 cb w
def RelRungD0a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) : Prop :=
  D3.RelD3 cb w ∧ InRungD0a B cb w W Dp

instance (cb w : Bytes) : Decidable (RelRungD2 cb w) := by unfold RelRungD2 InRungD2; infer_instance
instance (cb w : Bytes) : Decidable (RelRungD1 cb w) := by
  unfold RelRungD1 InRungD1 InRungD2; infer_instance
instance (cb w : Bytes) : Decidable (RelRungD0 cb w) := by
  unfold RelRungD0 InRungD0 InRungD1 InRungD2; infer_instance
instance (B : Nat) (cb w : Bytes) (W Dp N : Nat) : Decidable (RelRungD1a B cb w W Dp N) := by
  unfold RelRungD1a InRungD1a InRungD1 InRungD2; infer_instance
instance (B : Nat) (cb w : Bytes) (W Dp : Nat) : Decidable (RelRungD0a B cb w W Dp) := by
  unfold RelRungD0a InRungD0a InRungD0 InRungD1 InRungD2; infer_instance

/-! ## The inclusions: projections -/

theorem rungD0a_rungD0 {B : Nat} {cb w : Bytes} {W Dp : Nat} (h : RelRungD0a B cb w W Dp) :
    RelRungD0 cb w := ⟨h.1, h.2.2⟩
theorem rungD0_rungD1 {cb w : Bytes} (h : RelRungD0 cb w) : RelRungD1 cb w := ⟨h.1, h.2.2⟩
theorem rungD1a_rungD1 {B : Nat} {cb w : Bytes} {W Dp N : Nat} (h : RelRungD1a B cb w W Dp N) :
    RelRungD1 cb w := ⟨h.1, h.2.2⟩
theorem rungD1_rungD2 {cb w : Bytes} (h : RelRungD1 cb w) : RelRungD2 cb w := ⟨h.1, h.2.2⟩
theorem rungD2_rungD3 {cb w : Bytes} (h : RelRungD2 cb w) : D3.RelD3 cb w := h.1

/-- **D0 ⊂ D1 ⊂ D2 ⊂ D3**, for the rung relations. -/
theorem rung_chain {cb w : Bytes} (h : RelRungD0 cb w) :
    RelRungD1 cb w ∧ RelRungD2 cb w ∧ D3.RelD3 cb w :=
  ⟨rungD0_rungD1 h, rungD1_rungD2 (rungD0_rungD1 h), h.1⟩

/-- **The witness lift, as a projection**: a `RelRungD1a` chunk is a `RelD3` chunk on the same
bytes (`zk-formal/ZkFormal/PQ/Join/Coverage.lean`'s `WitnessLift`). -/
theorem rungD1a_lift {B : Nat} {cb w : Bytes} {W Dp N : Nat} (h : RelRungD1a B cb w W Dp N) :
    ∃ w2, D3.RelD3 cb w2 := ⟨w, h.1⟩

end NearSpecV3
