import WasmBase.RipemdForms
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

/-! ## B. The gated sum in general form

`RipemdAir` gates five row-dependent quantities by *two* different expressions: the raw step selector
`sel_n` (the message word `xL`/`xR`, the rotation `rot`, the group constant `kL`/`kR`) and the
*group* selector sum `gsel_g = Σ_{n<16} sel_{16g+n}` (the `f` form).  A single general form covers
both — `gsumG gate term N = Σ_{n<N} gate n · term n` — so the collapse argument is written once and
instantiated five times.  `gsumAux`/`csumAux` in §A are the `gate = sel_n` instances. -/

/-- `Σ_{n<N} gate n · term n`, with `gate` and `term` arbitrary row expressions. -/
def gsumG (gate term : Nat → Expr) : Nat → Expr
  | 0 => e0
  | n + 1 => gsumG gate term n + gate n * term n

/-- Every gate zero below `N` kills the sum. -/
theorem gsumG_zero (rw : Row) (gate term : Nat → Expr) :
    ∀ N, (∀ n, n < N → (gate n).eval rw = 0) → (gsumG gate term N).eval rw = 0 := by
  intro N
  induction N with
  | zero => intro _; show (e0.eval rw) = 0; rw [e0_eval]
  | succ n ih =>
    intro h
    show (Expr.eval rw (gsumG gate term n) + Expr.eval rw (gate n * term n)) = 0
    rw [ih (fun i hi => h i (by omega)),
      show Expr.eval rw (gate n * term n) = (gate n).eval rw * (term n).eval rw from rfl,
      h n (by omega), zero_mul_f, add_zero_f]

/-- **The gated sum collapses to its term at the one gate that is 1.** -/
theorem gsumG_at (rw : Row) (gate term : Nat → Expr) :
    ∀ N j0, j0 < N → (gate j0).eval rw = 1 →
      (∀ j, j < N → j ≠ j0 → (gate j).eval rw = 0) →
      (gsumG gate term N).eval rw = (term j0).eval rw := by
  intro N
  induction N with
  | zero => intro j0 hj0 _ _; omega
  | succ n ih =>
    intro j0 hj0 h1 h0
    show (Expr.eval rw (gsumG gate term n) + Expr.eval rw (gate n * term n)) = (term j0).eval rw
    rw [show Expr.eval rw (gate n * term n) = (gate n).eval rw * (term n).eval rw from rfl]
    rcases Nat.lt_or_eq_of_le (show j0 ≤ n from by omega) with h' | h'
    · rw [h0 n (by omega) (by omega), zero_mul_f, add_zero_f]
      exact ih j0 h' h1 (fun i hi hne => h0 i (by omega) hne)
    · have hrn : j0 = n := h'
      rw [hrn]
      rw [show Expr.eval rw (gsumG gate term n) = 0 from
            gsumG_zero rw gate term n (fun i hi => h0 i (by omega) (by omega))]
      rw [show (gate n).eval rw = 1 from hrn ▸ h1, one_mul_f, zero_add_f]

/-! ### The five instances

Each of `RipemdAir`'s bespoke `*Aux` recursions is `gsumG` at a specific `(gate, term)` pair.  These
are definitional identities, so each concrete collapse below is `gsumG_at` after a rewrite. -/

/-- `gsumAux term` is the `gate = sel_n` instance. -/
theorem gsumAux_eq_gsumG (term : Nat → Expr) :
    ∀ N, gsumAux term N = gsumG (fun n => v (selE n)) term N := by
  intro N
  induction N with
  | zero => rfl
  | succ n ih =>
    show gsumAux term n + v (selE n) * term n =
      gsumG (fun n => v (selE n)) term n + v (selE n) * term n
    rw [ih]

/-- `csumAux term` is the `gate = sel_n`, `term = Expr.c ∘ term` instance. -/
theorem csumAux_eq_gsumG (term : Nat → Nat) :
    ∀ N, csumAux term N = gsumG (fun n => v (selE n)) (fun n => Expr.c (term n)) N := by
  intro N
  induction N with
  | zero => rfl
  | succ n ih =>
    show csumAux term n + v (selE n) * Expr.c (term n) =
      gsumG (fun n => v (selE n)) (fun n => Expr.c (term n)) n + v (selE n) * Expr.c (term n)
    rw [ih]

/-- In `F_p`, `a * 1 = a`. -/
theorem mul_one_f (a : F) : a * (1 : F) = a := by grind

/-- `gselAux g N = Σ_{n<N} sel_{16g+n}` is the `gate = sel_{16g+n}`, `term = 1` instance — up to the
`· 1` that `gsumG`'s product carries and `gselAux`'s summand does not.  Stated at the value level so
the `· 1` is discharged by `e1_eval` and `mul_one_f`. -/
theorem gselAux_eq_gsumG_eval (rw : Row) (g : Nat) :
    ∀ N, (gselAux g N).eval rw =
      (gsumG (fun n => v (selE (16 * g + n))) (fun _ => e1) N).eval rw := by
  intro N
  induction N with
  | zero => rfl
  | succ n ih =>
    show (gselAux g n).eval rw + rw.cur (selE (16 * g + n)) =
      (gsumG (fun n => v (selE (16 * g + n))) (fun _ => e1) n).eval rw
        + rw.cur (selE (16 * g + n)) * (e1).eval rw
    rw [ih, e1_eval, mul_one_f]

/-- The message word's term: `xL_k − X[rl[n]]_k` (left) or `xR_k − X[rr[n]]_k` (right). -/
def xselTerm (b k : Nat) : Nat → Expr := fun n =>
  v ((if b = 0 then xlC else xrC) + k) -
    v (xBit (if b = 0 then rlVal n else rrVal n) k)

/-- `xselAux b k` is the `gate = sel_n` instance on `xselTerm`. -/
theorem xselAux_eq_gsumG (b k : Nat) :
    ∀ N, xselAux b k N = gsumG (fun n => v (selE n)) (xselTerm b k) N := by
  intro N
  induction N with
  | zero => rfl
  | succ n ih =>
    show xselAux b k n + v (selE n) * xselTerm b k n =
      gsumG (fun n => v (selE n)) (xselTerm b k) n + v (selE n) * xselTerm b k n
    rw [ih]

/-- The rotation's term: `rot_k − t3[(k+32−sl[n]) mod 32]` (left) or `t6[·]` (right). -/
def rotTerm (b k : Nat) : Nat → Expr := fun n =>
  v (rotBit b k) -
    v (tBit (if b = 0 then 2 else 6)
      ((k + W - (if b = 0 then slVal n else srVal n)) % W))

/-- `rotAux b k` is the `gate = sel_n` instance on `rotTerm`. -/
theorem rotAux_eq_gsumG (b k : Nat) :
    ∀ N, rotAux b k N = gsumG (fun n => v (selE n)) (rotTerm b k) N := by
  intro N
  induction N with
  | zero => rfl
  | succ n ih =>
    show rotAux b k n + v (selE n) * rotTerm b k n =
      gsumG (fun n => v (selE n)) (rotTerm b k) n + v (selE n) * rotTerm b k n
    rw [ih]

/-- The `f` term: `fL_k − form_g(bl,cl,dl)_k` (left) or `fR_k − form_{4−g}(br,cr,dr)_k` (right). -/
def fTerm (b k : Nat) : Nat → Expr := fun n => fColB b k - formB b n k

/-- `fSumAux b k` is the `gate = gselAux · 16` instance on `fTerm`. -/
theorem fSumAux_eq_gsumG (b k : Nat) :
    ∀ N, fSumAux b k N = gsumG (fun n => gselAux n 16) (fTerm b k) N := by
  intro N
  induction N with
  | zero => rfl
  | succ n ih =>
    show fSumAux b k n + gselAux n 16 * (fColB b k - formB b n k) =
      gsumG (fun n => gselAux n 16) (fTerm b k) n + gselAux n 16 * fTerm b k n
    rw [ih]
    rfl

/-! ### Row-level collapses

`RipemdAir`'s constraint `c` is "the expression evaluates to zero".  Each row-dependent column is
pinned by its own gated sum, so a row satisfying `c = 0` has that column equal to the term at the
one-hot index. -/

/-- The message-word gated sum's value: the row's `xL_k`/`xR_k` column minus the selected `X` bit. -/
theorem xselAux_eq_at (rw : Row) (b k j0 : Nat) (hj : j0 < STEPS)
    (h1 : rw.cur (selE j0) = 1)
    (h0 : ∀ j, j < STEPS → j ≠ j0 → rw.cur (selE j) = 0) :
    (xselAux b k STEPS).eval rw =
      rw.cur ((if b = 0 then xlC else xrC) + k) -
        rw.cur (xBit (if b = 0 then rlVal j0 else rrVal j0) k) := by
  have h := gsumG_at rw (fun n => v (selE n)) (xselTerm b k) STEPS j0 hj h1 h0
  rw [← xselAux_eq_gsumG] at h
  exact h

/-- **The message-word column equals the selected `X` word.** -/
theorem xsel_eq (rw : Row) (b k j0 : Nat) (hj : j0 < STEPS)
    (h1 : rw.cur (selE j0) = 1)
    (h0 : ∀ j, j < STEPS → j ≠ j0 → rw.cur (selE j) = 0)
    (hc : (xselConstrB b k).eval rw = 0) :
    rw.cur ((if b = 0 then xlC else xrC) + k) =
      rw.cur (xBit (if b = 0 then rlVal j0 else rrVal j0) k) := by
  have h := xselAux_eq_at rw b k j0 hj h1 h0
  exact sub_eq_zero' (by rw [← h]; exact hc)

/-- The rotation gated sum's value: the row's `rot_k` column minus the addressed `t3`/`t6` bit. -/
theorem rotAux_eq_at (rw : Row) (b k j0 : Nat) (hj : j0 < STEPS)
    (h1 : rw.cur (selE j0) = 1)
    (h0 : ∀ j, j < STEPS → j ≠ j0 → rw.cur (selE j) = 0) :
    (rotAux b k STEPS).eval rw =
      rw.cur (rotBit b k) -
        rw.cur (tBit (if b = 0 then 2 else 6)
          ((k + W - (if b = 0 then slVal j0 else srVal j0)) % W)) := by
  have h := gsumG_at rw (fun n => v (selE n)) (rotTerm b k) STEPS j0 hj h1 h0
  rw [← rotAux_eq_gsumG] at h
  exact h

/-- **The rotation column equals the rotated `t3`/`t6` bit.** -/
theorem rot_eq (rw : Row) (b k j0 : Nat) (hj : j0 < STEPS)
    (h1 : rw.cur (selE j0) = 1)
    (h0 : ∀ j, j < STEPS → j ≠ j0 → rw.cur (selE j) = 0)
    (hc : (rotConstrB b k).eval rw = 0) :
    rw.cur (rotBit b k) =
      rw.cur (tBit (if b = 0 then 2 else 6)
        ((k + W - (if b = 0 then slVal j0 else srVal j0)) % W)) := by
  have h := rotAux_eq_at rw b k j0 hj h1 h0
  exact sub_eq_zero' (by rw [← h]; exact hc)

/-- The `f` gated sum's value: the row's `f` column minus the group's form bit. -/
theorem fSumAux_eq_at (rw : Row) (b k g0 : Nat) (hg0 : g0 < GROUPS)
    (h1 : (gselAux g0 16).eval rw = 1)
    (h0 : ∀ g, g < GROUPS → g ≠ g0 → (gselAux g 16).eval rw = 0) :
    (fSumAux b k GROUPS).eval rw = (fColB b k).eval rw - (formB b g0 k).eval rw := by
  have h := gsumG_at rw (fun n => gselAux n 16) (fTerm b k) GROUPS g0 hg0 h1 h0
  rw [← fSumAux_eq_gsumG] at h
  exact h

/-- **The `f` column equals the group's form.**  The gate here is the group selector sum, so the
hypotheses are its profile: `1` on group `g0`, `0` on every other group. -/
theorem f_eq (rw : Row) (b k g0 : Nat) (hg0 : g0 < GROUPS)
    (h1 : (gselAux g0 16).eval rw = 1)
    (h0 : ∀ g, g < GROUPS → g ≠ g0 → (gselAux g 16).eval rw = 0)
    (hc : (fConstrB b k).eval rw = 0) :
    (fColB b k).eval rw = (formB b g0 k).eval rw := by
  have h := fSumAux_eq_at rw b k g0 hg0 h1 h0
  exact sub_eq_zero' (by rw [← h]; exact hc)

/-- **The group selector profile**, derived from the one-hot selector alone: the group containing the
one-hot index has `gsel = 1`, every other group `gsel = 0`.  This is what `f_eq` consumes. -/
theorem gsel_profile (rw : Row) (g0 n0 : Nat) (_hg0 : g0 < GROUPS) (hn : n0 < 16)
    (hj : 16 * g0 + n0 < STEPS)
    (h1 : rw.cur (selE (16 * g0 + n0)) = 1)
    (h0 : ∀ j, j < STEPS → j ≠ 16 * g0 + n0 → rw.cur (selE j) = 0) :
    (gselAux g0 16).eval rw = 1 ∧ ∀ g, g < GROUPS → g ≠ g0 → (gselAux g 16).eval rw = 0 := by
  have hS : STEPS = 80 := rfl
  have hG : GROUPS = 5 := rfl
  refine ⟨gselAux_at rw g0 16 n0 hn h1 (fun n hnn hne => h0 _ (by omega) (by omega)), ?_⟩
  intro g _ hne
  exact gselAux_zero rw g 16 (fun n hnn => h0 _ (by omega) (by omega))

end Ripemd
end Chips
end WasmBase
