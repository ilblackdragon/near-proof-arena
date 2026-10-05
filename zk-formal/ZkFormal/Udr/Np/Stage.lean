import ZkFormal.Udr.Np.Sem

/-!
# ZkFormal.Udr.Np.Stage — DEEP words, the FRI run, and the doomed stages

`Stage A prm τ` is L3's doomed predicate on well-shaped transcripts, by
number of entries `E` (the schedule strictly alternates message / challenge,
so `E = 2·#challenges` or `2·#challenges + 1`):

| `E` | after | doomed |
|---|---|---|
| 0 | – | claim not in the language |
| 1 | main | main far, or decoded trace fails `Holds` |
| 2, 3 | `α_fp` | main far, local constraint fails, or fingerprint multisets differ |
| 4 | `γ` | main far, local constraint fails, or grand products differ |
| 5 | aux, finals | main/aux far, a constraint (incl. aux) fails on `H`, or bus finals fail |
| 6 | `α_c` | far, `C_t ≠ 0` somewhere on `H`, or bus finals fail |
| 7 | quotient | far, `C_t ≠ (X^T - 1)·Q_t` as functions, or bus finals fail |
| 8 | `z` | far, (`z ∉ F` and `C_t(z) ≠ (z^T-1)Q_t(z)`), or bus finals fail |
| ≥ 9 | OOD values … | global checks fail, or (some batched DEEP word far and all FRI challenges so far good) |

For `E ≥ 9` the batching rounds drawn so far are applied to each class's
DEEP word; during FRI the class words are the fully batched ones.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

section
variable (A : Air) (prm : Params)

/-! ## DEEP words and batching -/

/-- DEEP columns of class `m` in the verifier's batching order: per table,
main at `z`, main at `ωz`, aux at `z`, aux at `ωz`, quotient at `z`. -/
def deepCols (lay : List TLayout) (m : Nat) : List (Col × Bool) :=
  (lay.zipIdx.filter fun (L, _) => L.lde == m).flatMap fun (L, t) =>
    (List.range L.width).map (fun c => (⟨t, 0, c⟩, false)) ++
    (List.range L.width).map (fun c => (⟨t, 0, c⟩, true)) ++
    (List.range L.aux).map (fun c => (⟨t, 1, c⟩, false)) ++
    (List.range L.aux).map (fun c => (⟨t, 1, c⟩, true)) ++
    (List.range L.quot).map (fun c => (⟨t, 2, c⟩, false))

/-- The OOD point. -/
def zOf (τ : PTn) : Fp8 := τ.chals.getD 3 0

/-- Claimed OOD value of a column at `z` (`s = false`) or `ωz` (`s = true`). -/
def claimed (τ : PTn) (d : Col) (s : Bool) : Fp8 :=
  let o := ((splitOod (layOf A prm τ) (τ.elems.getD 1 [])).1).getD d.t ⟨[], [], [], [], []⟩
  match d.kind, s with
  | 0, false => o.mainZ.getD d.c 0
  | 0, true => o.mainG.getD d.c 0
  | 1, false => o.auxZ.getD d.c 0
  | 1, true => o.auxG.getD d.c 0
  | _, _ => o.quotZ.getD d.c 0

/-- The interleaved DEEP word of class `m`. -/
def deepWord (τ : PTn) (m : Nat) : Word Nat Fp8 := fun p j =>
  match (deepCols (layOf A prm τ) m)[j]? with
  | some (d, s) =>
    let ζ := if s then omg (tl A prm τ d.t).log * zOf τ else zOf τ
    (colVal τ d p - claimed A prm τ d s) * (pt (n0Of A prm τ) m p - ζ)⁻¹
  | none => 0

/-- Number of batching rounds. -/
def nBatch (τ : PTn) : Nat := batchRounds (layOf A prm τ)

/-- Batching challenges drawn so far. -/
def batchChals (τ : PTn) : List Fp8 := (τ.chals.drop 4).take (nBatch A prm τ)

/-- The (partially) batched DEEP word of class `m`. -/
def batchedWord (τ : PTn) (m : Nat) : Word Nat Fp8 := batchAll (batchChals A prm τ) (deepWord A prm τ m)

/-- Class `m`'s batched word is not within its radius of `RS[T]` (interleaved). -/
def BatchFar (τ : PTn) (m log : Nat) : Prop :=
  ¬ CloseRS (pt (n0Of A prm τ) m) (2 ^ m) (2 ^ log) (eRad prm m) (batchedWord A prm τ m)

/-! ## The FRI run -/

def ellOf (τ : PTn) : Nat := finalLayer A prm (hdrOf τ)

/-- Natural-to-verifier position map at layer `ℓ - k` (pairs `j, j + n/2`
↦ verifier positions `2q, 2q+1`). -/
def permK (n0 ℓ : Nat) : Nat → Nat → Nat
  | 0, j => j
  | k + 1, j => 2 * permK n0 ℓ k (j % 2 ^ (n0 - ℓ + k)) + j / 2 ^ (n0 - ℓ + k)

/-- Verifier position of natural index `j` at layer `i ≤ ℓ`. -/
def permAt (τ : PTn) (i j : Nat) : Nat := permK (n0Of A prm τ) (ellOf A prm τ) (ellOf A prm τ - i) j

/-- The FRI setup (layer `i`: domain size `2^(n0-i)`, degree bound `2^(n0-b-i)`). -/
structure SetupData where
  r : Nat
  nn : Nat → Nat
  DD : Nat → Nat
  xs : Nat → Nat → Fp8

def setupData (τ : PTn) : SetupData where
  r := ellOf A prm τ
  nn i := 2 ^ (n0Of A prm τ - i)
  DD i := 2 ^ (n0Of A prm τ - prm.logBlowup - i)
  xs i j := pt (n0Of A prm τ) (n0Of A prm τ - i) (permAt A prm τ i j)

/-- FRI challenges drawn so far, with their kinds. -/
def friChals (τ : PTn) : List ((Bool × Nat) × Fp8) :=
  (friChalKinds A prm (hdrOf τ)).zip (τ.chals.drop (4 + nBatch A prm τ))

def betaOf (τ : PTn) (i : Nat) : Fp8 := ((friChals A prm τ).lookup (false, i)).getD 0
def gammaOf (τ : PTn) (i : Nat) : Fp8 := ((friChals A prm τ).lookup (true, i)).getD 0

/-- Committed FRI layers `(layer, arity log)`. -/
def commitsOf (τ : PTn) : List (Nat × Nat) := friCommits A prm (hdrOf τ)

/-- Value at verifier position `p` of committed layer number `k` (FRI oracle `3 + k`). -/
def committedAt (τ : PTn) (k a p : Nat) : Fp8 :=
  (ksOfRow (F := Fp) ((matOf (oracleOf τ (3 + k)) 0).row (p >>> a))).getD (p % 2 ^ a) 0

/-- Batched DEEP value of class `m` at verifier position `p` (column 0 of the full batch). -/
def deepAtPos (τ : PTn) (m p : Nat) : Fp8 := batchedWord A prm τ m p 0

/-- Roll-in word entering layer `i + 1`. -/
def rollG (τ : PTn) (i : Nat) : Word Unit Fp8 := fun j _ =>
  if rollInAt A prm (hdrOf τ) (i + 1) then
    deepAtPos A prm τ (n0Of A prm τ - (i + 1)) (permAt A prm τ (i + 1) j)
  else 0

/-- The FRI layer words (committed layers read from their oracles, virtual
layers computed by folding and rolling in). -/
def friF (τ : PTn) : Nat → Word Unit Fp8
  | 0 => fun j _ =>
    match (commitsOf A prm τ).head? with
    | some (_, a) => committedAt τ 0 a (permAt A prm τ 0 j)
    | none => deepAtPos A prm τ (n0Of A prm τ) (permAt A prm τ 0 j)
  | i + 1 =>
    match (commitsOf A prm τ).zipIdx.find? (fun ((c, _), _) => c == i + 1) with
    | some ((_, a), k) => fun j _ => committedAt τ k a (permAt A prm τ (i + 1) j)
    | none =>
      let S := setupData A prm τ
      let half : Nat := S.nn (i + 1)
      let u := friF τ i
      let ev0 : Word Unit Fp8 := fun j _ => (u j () + u (j + half) ()) * (2 : Fp8)⁻¹
      let od0 : Word Unit Fp8 := fun j _ => (u j () - u (j + half) ()) * (2 * S.xs i j)⁻¹
      line (line ev0 od0 (betaOf A prm τ i)) (rollG A prm τ i) (gammaOf A prm τ (i + 1))

/-! ## Strong-line conditions of the FRI challenges -/

/-- `Strong` for the RS code `RS[xs, n, D]` (proof-free form; it is
`Strong (rsCode xs n D _ _)` by definition). -/
def StrongRS (xs : Nat → Fp8) (n D e : Nat) (u0 u1 : Word Unit Fp8) (z : Fp8) : Prop :=
  ∀ w : Word Unit Fp8, (∃ P : Nat → Fp8, ∀ i, i < n → w i () = ev D P (xs i)) →
    dist n (line u0 u1 z) w ≤ e →
    ∃ v0 v1 : Word Unit Fp8, (∃ P : Nat → Fp8, ∀ i, i < n → v0 i () = ev D P (xs i)) ∧
      (∃ P : Nat → Fp8, ∀ i, i < n → v1 i () = ev D P (xs i)) ∧
      ∀ i, i < n → line u0 u1 z i = w i → u0 i = v0 i ∧ u1 i = v1 i

/-- Even / odd parts of FRI layer `i` (on layer `i + 1`). -/
def evenF (τ : PTn) (i : Nat) : Word Unit Fp8 := fun j _ =>
  let S := setupData A prm τ
  (friF A prm τ i j () + friF A prm τ i (j + S.nn (i + 1)) ()) * (2 : Fp8)⁻¹
def oddF (τ : PTn) (i : Nat) : Word Unit Fp8 := fun j _ =>
  let S := setupData A prm τ
  (friF A prm τ i j () - friF A prm τ i (j + S.nn (i + 1)) ()) * (2 * S.xs i j)⁻¹
def foldF (τ : PTn) (i : Nat) : Word Unit Fp8 := line (evenF A prm τ i) (oddF A prm τ i) (betaOf A prm τ i)

/-- The FRI challenge `c` of kind `(roll, i)` satisfies its strong-line condition. -/
def FriChalGood (τ : PTn) (roll : Bool) (i : Nat) (c : Fp8) : Prop :=
  let S := setupData A prm τ
  let n0 := n0Of A prm τ
  if roll then
    StrongRS (S.xs i) (S.nn i) (S.DD i) (eRad prm (n0 - i)) (foldF A prm τ (i - 1)) (rollG A prm τ (i - 1)) c
  else
    StrongRS (S.xs (i + 1)) (S.nn (i + 1)) (S.DD (i + 1)) (eRad prm (n0 - (i + 1)))
      (evenF A prm τ i) (oddF A prm τ i) c

/-- Every FRI challenge drawn so far is good. -/
def FriGoodSoFar (τ : PTn) : Prop :=
  ∀ q (hq : q < (friChals A prm τ).length),
    FriChalGood A prm τ (friChals A prm τ)[q].1.1 (friChals A prm τ)[q].1.2 (friChals A prm τ)[q].2

/-! ## The doomed stages -/

/-- Some (main/aux) constraint value is nonzero on the trace domain. -/
noncomputable def CsFailH (τ : PTn) (αfp γ : Fp8) : Prop :=
  ∃ t, t < A.tables.length ∧ ∃ r, r < 2 ^ (tl A prm τ t).log ∧
    ∃ c ∈ csAt A prm τ t αfp γ (omg (tl A prm τ t).log ^ r), c ≠ 0

/-- **L3's doomed predicate** (on shaped transcripts). -/
noncomputable def Stage (τ : PTn) : Prop :=
  let ch := fun k => τ.chals.getD k 0
  let pub := pubOf Fp τ.cb
  match τ.entries.length with
  | 0 => ¬ AirLang Fp A τ.cb
  | 1 => ¬ AllClose A prm τ 1 ∨ ¬ Air.Holds A pub (decTrace A prm τ)
  | 2 | 3 => ¬ AllClose A prm τ 1 ∨ LocalFail A prm τ ∨ FpDiffer A prm τ (ch 0)
  | 4 => ¬ AllClose A prm τ 1 ∨ LocalFail A prm τ ∨ GpDiffer A prm τ (ch 0) (ch 1)
  | 5 => ¬ AllClose A prm τ 2 ∨ CsFailH A prm τ (ch 0) (ch 1) ∨ BusFinalsFail A prm τ
  | 6 => ¬ AllClose A prm τ 2 ∨
      (∃ t, t < A.tables.length ∧ ∃ r, r < 2 ^ (tl A prm τ t).log ∧
        Ct A prm τ t (ch 0) (ch 1) (ch 2) (omg (tl A prm τ t).log ^ r) ≠ 0) ∨ BusFinalsFail A prm τ
  | 7 => ¬ AllClose A prm τ 3 ∨
      (∃ t, t < A.tables.length ∧ ∃ x, Ct A prm τ t (ch 0) (ch 1) (ch 2) x ≠
        (x ^ (2 ^ (tl A prm τ t).log) - 1) * Qt A prm τ t x) ∨ BusFinalsFail A prm τ
  | 8 => ¬ AllClose A prm τ 3 ∨
      (¬ (ch 3).IsBase ∧ ∃ t, t < A.tables.length ∧ Ct A prm τ t (ch 0) (ch 1) (ch 2) (ch 3) ≠
        ((ch 3) ^ (2 ^ (tl A prm τ t).log) - 1) * Qt A prm τ t (ch 3)) ∨ BusFinalsFail A prm τ
  | _ => GlobalFail A prm τ ∨
      ((∃ L ∈ layOf A prm τ, BatchFar A prm τ L.lde L.log) ∧ FriGoodSoFar A prm τ)

/-- The doomed predicate handed to L2: malformed transcripts are doomed. -/
noncomputable def Doomed (τ : PTn) : Prop :=
  ¬ Shaped (Iop.verifier Fp Fp8 A prm) τ ∨ Stage A prm τ

end
end ZkFormal.Udr.Np
