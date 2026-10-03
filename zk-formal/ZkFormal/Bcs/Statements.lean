import ZkFormal.Bcs.Extract
import ZkFormal.Bcs.MmcsDefs
import ZkFormal.Game
import ZkFormal.Collision

/-!
# ZkFormal.Bcs.Statements — lane L2 sublemmas (frozen statements)

Each `…Stmt` is an independent obligation; `Bcs.Compose` proves the lane's
top theorem `bcs_romSound` from them.  Status: docs/zk-formal/STATUS-L2.md.

* `GameStmt` — the judge's ROM game reduces to a potential (generalises
  `ZkFormal.romSound_of_potential`: weights bounded by `W` instead of `1`,
  and the acceptance obligation only for well-formed logs of length at most
  the tape length, stated through `evalT`).
* `QBAddStmt`, `StepMixStmt` — budget/potential algebra.
* `InvPotStmt` — the inversion potential (`InvBad` has probability
  `≤ 1024·q/2^256` for logs of at most `N ≤ 2^100` entries).
* `MmcsStmt` — the MMCS (mixed heights) is binding and rooted.
* `BudgetStmt` — the profile arithmetic.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

def GameStmt : Prop :=
  ∀ {S : ChallengeSpec} (L : Bytes → Prop) (P : TreeProver S) (V : TreeVerifier) (pub : Bytes)
    (qH qP NPu NVu : Nat),
    (∀ c wit, OracleComp.QueryBound unitWeight (P.tree pub c wit) NPu) →
    (∀ cb pb, OracleComp.QueryBound unitWeight (V.tree pub cb pb) NVu) →
    ∀ (w : Bytes → Nat) (W NPw NVw : Nat), (∀ x, w x ≤ W) →
    (∀ c wit, OracleComp.QueryBound w (P.tree pub c wit) NPw) →
    (∀ cb pb, OracleComp.QueryBound w (V.tree pub cb pb) NVw) →
    ∀ (Φ : Table → Nat) (C M : Nat), 0 < M → StepBound Φ w C →
    (∀ (tbl : Table) (cb pb : Bytes), TableWF tbl → tbl.length ≤ qH + qP * NPu + NVu →
      evalT tbl (V.tree pub cb pb) = some true → ¬ L cb → M ≤ Φ tbl) →
    RomSound S L V.toVerifier P.toProver pub qH qP (qH + qP * NPu + NVu)
      (Φ [] + C * (qH * W + qP * NPw + NVw)) M

def QBAddStmt : Prop :=
  ∀ {α : Type} (A : OracleComp hashSpec α) (w₁ w₂ : Bytes → Nat) (c₁ c₂ a b : Nat),
    OracleComp.QueryBound w₁ A a → OracleComp.QueryBound w₂ A b →
    OracleComp.QueryBound (fun x => c₁ * w₁ x + c₂ * w₂ x) A (c₁ * a + c₂ * b)

/-- Potentials with different weights combine (and weights can be raised). -/
def StepMixStmt : Prop :=
  ∀ (Φ₁ Φ₂ : Table → Nat) (w₁ w₂ w : Bytes → Nat) (C₁ C₂ : Nat),
    StepBound Φ₁ w₁ C₁ → StepBound Φ₂ w₂ C₂ → (∀ x, C₁ * w₁ x + C₂ * w₂ x ≤ w x) →
    StepBound (fun t => Φ₁ t + Φ₂ t) w 1

def InvPotStmt : Prop :=
  ∀ N, N ≤ 2 ^ 100 → ∃ Φ : Table → Nat, StepBound Φ unitWeight 1024 ∧ Φ [] = 0 ∧
    ∀ tbl : Table, tbl.length ≤ N → BadHist InvBad tbl → roRange ≤ Φ tbl

def MmcsStmt : Prop := mmcs.Binding ∧ mmcs.Rooted

/-- Numerator of the compiled bound (`bcs_romSound`), over `roRange ^ K`.
`B`: per-challenge bad count; `G = ∏_{j<K} g j`: query-phase good count;
`NPq`, `NVq`: query-chunk queries per honest proof / per verification. -/
def bcsNum (K B G qH qP NPu NVu NPq NVq : Nat) : Nat :=
  let N := qH + qP * NPu + NVu
  let A := roRange ^ (K - 1) * (B + 1024) + roRange ^ (K - 2) * (2 * N)
  qH * (A + G) + qP * (A * NPu + G * NPq) + (A * NVu + G * NVq)

/-- Budget algebra at the profile's budgets: if the query phase alone is
below `2^-129` (with `2^64 + 2^40·NPq + NVq` chunk queries), everything is
below `2^-128`. -/
def BudgetStmt : Prop :=
  ∀ K B G NPu NVu NPq NVq : Nat, 2 ≤ K → B ≤ 2 ^ 50 → NPu ≤ 2 ^ 30 → NVu ≤ 2 ^ 30 →
    G * (2 ^ 64 + 2 ^ 40 * NPq + NVq) * 2 ^ 129 ≤ roRange ^ K →
    bcsNum K B G (2 ^ 64) (2 ^ 40) NPu NVu NPq NVq * 2 ^ 128 ≤ roRange ^ K

end ZkFormal.Bcs
