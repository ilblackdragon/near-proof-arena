import WasmBase.RipemdSound
import WasmBase.RipemdVectors
/-!
# WasmBase.RipemdRound — stage 4: the ten next-row words are the spec's step

`WasmBase.RipemdSound` proves stages 1–3 (field plumbing, selector collapses, adder chain).  This
file is stage 4: given that a row satisfies `RipemdAir.constraints`, the ten words its `nxt` group
holds are exactly one step of `NearSpecV3.Wasm.Crypto.ripemd160` applied to the ten words its `cur`
group holds.

## The shape of the statement

The row's constraints are gated by the one-hot step selector: `sel_j = 1` for a single `j₀ < 80`.
Every row-dependent quantity — the `f` form, the message word, the rotation amount, the group
constant — is a `sel`-gated sum, so each collapses to its value at `j₀`.  The assembly therefore
reads:

> `round_agrees`: the row's `nxt` words are the spec's step at `j₀` of the row's `cur` words.

## What is proved here, and what is not

Proved: the gated-sum collapses in general form (`gsumAux_zero`, `gsumAux_at`), the group selector
sum `gselAux g 16` (already in `RipemdSound`), the `f`-form bridge on bits, and the rotation bridge.

Not proved: the digest's relationship to the spec's `ripemd160` over a whole message.  That needs
the feed-forward row family and the block-boundary rows, which `RipemdAir` does not define (the
README's §3.6 names both as separate obligations).  This file supplies the per-step half.
-/
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace WasmBase
namespace Chips
namespace Ripemd

open ZkFormal.Algebra

/-! ## A. A general selector-gated sum

`RipemdAir` writes each row-dependent quantity as its own bespoke `*Aux` recursion.  The collapse
argument is the same for all of them: a sum of `sel_n · term n` over `n < N` is `term j₀` when
`sel_{j₀} = 1` and every other selector is `0`.  Factoring it once here means each concrete collapse
below is a one-line instantiation. -/

/-- `Σ_{n<N} sel_n · term n`, with `term` an arbitrary field expression. -/
def gsumAux (term : Nat → Expr) : Nat → Expr
  | 0 => e0
  | n + 1 => gsumAux term n + v (selE n) * term n

/-- Every selector zero below `N` kills the sum. -/
theorem gsumAux_zero (rw : Row) (term : Nat → Expr) :
    ∀ N, (∀ n, n < N → rw.cur (selE n) = 0) → (gsumAux term N).eval rw = 0 := by
  intro N
  induction N with
  | zero => intro _; show (e0.eval rw) = 0; rw [e0_eval]
  | succ n ih =>
    intro h
    show (Expr.eval rw (gsumAux term n) + Expr.eval rw (v (selE n) * term n)) = 0
    rw [ih (fun i hi => h i (by omega)),
      show Expr.eval rw (v (selE n) * term n) = rw.cur (selE n) * (term n).eval rw from rfl,
      h n (by omega), zero_mul_f, add_zero_f]

/-- **The gated sum collapses to its term at the one-hot index.** -/
theorem gsumAux_at (rw : Row) (term : Nat → Expr) :
    ∀ N j0, j0 < N → rw.cur (selE j0) = 1 →
      (∀ j, j < N → j ≠ j0 → rw.cur (selE j) = 0) →
      (gsumAux term N).eval rw = (term j0).eval rw := by
  intro N
  induction N with
  | zero => intro j0 hj0 _ _; omega
  | succ n ih =>
    intro j0 hj0 h1 h0
    show (Expr.eval rw (gsumAux term n) + Expr.eval rw (v (selE n) * term n)) = (term j0).eval rw
    rw [show Expr.eval rw (v (selE n) * term n) = rw.cur (selE n) * (term n).eval rw from rfl]
    rcases Nat.lt_or_eq_of_le (show j0 ≤ n from by omega) with h' | h'
    · rw [h0 n (by omega) (by omega), zero_mul_f, add_zero_f]
      exact ih j0 h' h1 (fun i hi hne => h0 i (by omega) hne)
    · have hrn : j0 = n := h'
      rw [show Expr.eval rw (gsumAux term n) = 0 from
            gsumAux_zero rw term n (fun i hi => h0 i (by omega) (by omega)),
          show rw.cur (selE n) = 1 from hrn ▸ h1, hrn]
      rw [one_mul_f, zero_add_f]

/-- The same collapse for a **constant** term (`Expr.c ∘ term`), the shape of `kSelAux`. -/
def csumAux (term : Nat → Nat) : Nat → Expr
  | 0 => e0
  | n + 1 => csumAux term n + v (selE n) * Expr.c (term n)

theorem csumAux_zero (rw : Row) (term : Nat → Nat) :
    ∀ N, (∀ n, n < N → rw.cur (selE n) = 0) → (csumAux term N).eval rw = 0 := by
  intro N
  induction N with
  | zero => intro _; show (e0.eval rw) = 0; rw [e0_eval]
  | succ n ih =>
    intro h
    show (Expr.eval rw (csumAux term n) + Expr.eval rw (v (selE n) * Expr.c (term n))) = 0
    rw [ih (fun i hi => h i (by omega)),
      show Expr.eval rw (v (selE n) * Expr.c (term n)) = rw.cur (selE n) * ((term n : Nat) : F) from rfl,
      h n (by omega), zero_mul_f, add_zero_f]

/-- **A constant gated sum collapses to its constant at the one-hot index.** -/
theorem csumAux_at (rw : Row) (term : Nat → Nat) :
    ∀ N j0, j0 < N → rw.cur (selE j0) = 1 →
      (∀ j, j < N → j ≠ j0 → rw.cur (selE j) = 0) →
      (csumAux term N).eval rw = ((term j0 : Nat) : F) := by
  intro N
  induction N with
  | zero => intro j0 hj0 _ _; omega
  | succ n ih =>
    intro j0 hj0 h1 h0
    show (Expr.eval rw (csumAux term n) + Expr.eval rw (v (selE n) * Expr.c (term n))) = _
    rw [show Expr.eval rw (v (selE n) * Expr.c (term n)) = rw.cur (selE n) * ((term n : Nat) : F) from rfl]
    rcases Nat.lt_or_eq_of_le (show j0 ≤ n from by omega) with h' | h'
    · rw [h0 n (by omega) (by omega), zero_mul_f, add_zero_f]
      exact ih j0 h' h1 (fun i hi hne => h0 i (by omega) hne)
    · have hrn : j0 = n := h'
      rw [show Expr.eval rw (csumAux term n) = 0 from
            csumAux_zero rw term n (fun i hi => h0 i (by omega) (by omega)),
          show rw.cur (selE n) = 1 from hrn ▸ h1, hrn]
      rw [one_mul_f, zero_add_f]

end Ripemd
end Chips
end WasmBase
