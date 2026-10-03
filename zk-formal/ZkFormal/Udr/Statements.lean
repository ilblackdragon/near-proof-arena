import ZkFormal.Udr.RS

/-!
# ZkFormal.Udr.Statements — the L3 sublemmas as named propositions

Each `…Stmt : Prop` is an independent proof obligation (owned by a sub-agent,
proved in its own file as `theorem … : …Stmt`).  `ZkFormal.Udr.Compose`
derives the L3 results from these propositions taken as hypotheses, so
downstream lanes can build against the statements before the proofs land.

| Statement | Content |
|---|---|
| `RsGapStmt` | Berlekamp–Welch: RS line proximity gap at `2e + D ≤ n`, threshold `3n + 2e + 1` |
| `FriStmt` | FRI pass-set argument with virtual folds and roll-ins |
| `GpGammaStmt` | grand product: distinct multisets ⇒ few product collisions |
| `GpAlphaStmt` | fingerprints: distinct message multisets ⇒ few fingerprint collisions |
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

/-! ## Berlekamp–Welch: the `d/2` line gap for Reed–Solomon codes -/

/-- **RS correlated agreement at the unique-decoding radius** (BCIKS20
Thm 4.1, with an elementary proof and a weaker but sufficient threshold):
if more than `3n + 2e + 1` challenges in a duplicate-free list make
`u0 + z·u1` `e`-close to `RS[xs, n, D]` and `2e + D ≤ n`, then `(u0, u1)`
has correlated agreement. -/
def RsGapStmt : Prop :=
  ∀ (K : Type) [Field K] (xs : Nat → K) (n D e : Nat) (hD : D ≤ n) (hxs : Distinct xs n),
    2 * e + D ≤ n → LineGap (rsCode xs n D hD hxs) e (3 * n + 2 * e + 1)

/-! ## FRI with binary folds, virtual layers and roll-ins -/

namespace Fri

/-- Domains of the FRI layers `0, …, r`: layer `i` has `nn i` points
`xs i 0, …`; `xs i (j + nn (i+1)) = - xs i j` and `xs (i+1) j = (xs i j)²`
(natural-order cosets of 2-power subgroups); degree bounds halve. -/
structure Setup (K : Type) [Field K] where
  r : Nat
  nn : Nat → Nat
  DD : Nat → Nat
  xs : Nat → Nat → K
  hnn : ∀ i, i < r → nn i = 2 * nn (i + 1)
  hDD : ∀ i, i < r → DD i = 2 * DD (i + 1)
  hDn : ∀ i, i ≤ r → DD i ≤ nn i
  hdist : ∀ i, i ≤ r → Distinct (xs i) (nn i)
  hneg : ∀ i j, i < r → j < nn (i + 1) → xs i (j + nn (i + 1)) = - xs i j
  hsq : ∀ i j, i < r → j < nn (i + 1) → xs (i + 1) j = xs i j * xs i j
  hnz : ∀ i j, i ≤ r → j < nn i → xs i j ≠ 0
  htwo : (2 : K) ≠ 0

variable {K : Type} [Field K]

/-- The RS code at layer `i`. -/
def Setup.code (S : Setup K) (i : Nat) (hi : i ≤ S.r) : LinCode Unit K (S.nn i) (S.nn i - S.DD i + 1) :=
  rsCode (S.xs i) (S.nn i) (S.DD i) (S.hDn i hi) (S.hdist i hi)

/-- A (possibly cheating) FRI transcript: layer words `f i` (`f 0` is the
batched input; `f (i+1)` is a committed oracle, or for a virtual layer simply
the fold itself), roll-in words `G i` (living on layer `i+1`; zero if no
table enters there), fold and roll-in challenges, and the final polynomial
`pr` (length `DD r`). -/
structure Run (K : Type) [Field K] where
  f : Nat → Word Unit K
  G : Nat → Word Unit K
  β : Nat → K
  γ : Nat → K
  pr : Nat → K

/-- Even part of a layer-`i` word, on layer `i+1`. -/
def evenW (S : Setup K) (i : Nat) (u : Word Unit K) : Word Unit K :=
  fun j _ => (u j () + u (j + S.nn (i + 1)) ()) * (2 : K)⁻¹

/-- Odd part of a layer-`i` word, on layer `i+1`. -/
def oddW (S : Setup K) (i : Nat) (u : Word Unit K) : Word Unit K :=
  fun j _ => (u j () - u (j + S.nn (i + 1)) ()) * (2 * S.xs i j)⁻¹

/-- The fold `f_e + β·f_o` of layer `i`. -/
def foldW (S : Setup K) (R : Run K) (i : Nat) : Word Unit K :=
  line (evenW S i (R.f i)) (oddW S i (R.f i)) (R.β i)

/-- The fold followed by the roll-in `+ γ·G`. -/
def rollW (S : Setup K) (R : Run K) (i : Nat) : Word Unit K :=
  line (foldW S R i) (R.G i) (R.γ i)

/-- `passK S R k j`: every verifier check from layer `r - k` upwards passes on
the query path through position `j` of layer `r - k` (the final layer is
checked against the final polynomial). -/
def passK (S : Setup K) (R : Run K) : Nat → Nat → Prop
  | 0, j => R.f S.r j () = ev (S.DD S.r) R.pr (S.xs S.r j)
  | k + 1, j =>
    R.f (S.r - k) (j % S.nn (S.r - k)) = rollW S R (S.r - (k + 1)) (j % S.nn (S.r - k)) ∧
      passK S R k (j % S.nn (S.r - k))

/-- All challenges of the run are outside the strong-line bad sets (radii `e`). -/
def GoodChallenges (S : Setup K) (R : Run K) (e : Nat → Nat) : Prop :=
  ∀ i (hi : i < S.r),
    Strong (S.code (i + 1) hi) (e (i + 1)) (evenW S i (R.f i)) (oddW S i (R.f i)) (R.β i) ∧
    Strong (S.code (i + 1) hi) (e (i + 1)) (foldW S R i) (R.G i) (R.γ i)

end Fri

/-- **FRI pass-set argument (UDR, no weights).**  With good challenges, if at
least `nn 0 - e 0` query positions of layer 0 pass every check, then `f 0`
agrees with a codeword on the whole pass set (so it is `e 0`-close). -/
def FriStmt : Prop :=
  ∀ (K : Type) [Field K] (S : Fri.Setup K) (R : Fri.Run K) (e : Nat → Nat),
    (∀ i, i < S.r → e i ≤ 2 * e (i + 1)) → Fri.GoodChallenges S R e →
    S.nn 0 - e 0 ≤ count (List.range (S.nn 0)) (Fri.passK S R S.r) →
    ∃ p : Nat → K, ∀ j, j < S.nn 0 → Fri.passK S R S.r j → R.f 0 j () = ev (S.DD 0) p (S.xs 0 j)

/-! ## Grand-product multiset argument -/

/-- **Product round.** Distinct multisets of field elements give products
`∏ (γ - a)` that coincide for at most `max |a| |b|` challenges. -/
def GpGammaStmt : Prop :=
  ∀ (K : Type) [Field K] (a b Ks : List K), Ks.Nodup → ¬ a.Perm b →
    count Ks (fun γ => (a.map (γ - ·)).prod = (b.map (γ - ·)).prod) ≤ max a.length b.length

/-- Fingerprint of a message `m` (a list of field elements) at `α`:
`m₀ + α·m₁ + α²·m₂ + …`. -/
def fp {K : Type} [Field K] (α : K) (m : List K) : K := m.foldr (fun a acc => a + α * acc) 0

/-- **Fingerprint round.** Distinct multisets of width-`w` messages (all
drawn from a list `Ms` of candidate messages; multiplicities are expanded in
`A`, `B`) have fingerprint multisets that coincide for at most `|Ms| · w`
challenges.  (Proof idea: fix a message `m*` whose multiplicities differ; a
bad `α` must make `fp α m* = fp α m` for some other `m ∈ Ms`.)  The bound
depends on the number of *distinct* messages, not on multiplicities. -/
def GpAlphaStmt : Prop :=
  ∀ (K : Type) [Field K] (w : Nat) (A B Ms : List (List K)) (Ks : List K),
    Ks.Nodup → (∀ m, m ∈ A ++ B → m ∈ Ms ∧ m.length = w) → ¬ A.Perm B →
    count Ks (fun α => (A.map (fp α)).Perm (B.map (fp α))) ≤ Ms.length * w

end ZkFormal.Udr
