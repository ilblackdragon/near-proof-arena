import ZkFormal.Near.Extract.Eval

/-!
# ZkFormal.Near.Render.Proof.NodeEv — constraints evaluated over the integers

`ev C D fst lst trn P e`: the value of `e` over `ℤ` with current-row cells `C`,
next-row cells `D`, the three selectors and public inputs `P`.  `ev_sound`:
if the cells of a trace are the images of `C`/`D`, then `e.eval` is the image
of `ev …`; so a constraint vanishes as soon as its integer value is `0`
(`eval_zero_of_ev`).  Used to check the honest node table's constraints with
`omega` instead of field arithmetic.
-/

namespace ZkFormal.Near.Render

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

namespace EvI

/-- Integer value of an expression. -/
def ev (C D : Nat → Int) (fst lst trn : Int) (P : Nat → Int) : Expr → Int
  | .const v => (v : Int)
  | .col x nx => if nx then D x else C x
  | .pub i => P i
  | .isFirst => fst
  | .isLast => lst
  | .isTransition => trn
  | .add a b => ev C D fst lst trn P a + ev C D fst lst trn P b
  | .mul a b => ev C D fst lst trn P a * ev C D fst lst trn P b
  | .neg a => - ev C D fst lst trn P a

theorem ev_sound {tr : Trace Fp} {t q : Nat} {pub : List Fp} {C D : Nat → Int}
    (hC : ∀ x, tr.cell t q x = ((C x : Int) : Fp))
    (hD : ∀ x, tr.cell t ((q + 1) % tr.height t) x = ((D x : Int) : Fp)) :
    ∀ e : Expr, e.eval tr t q pub = ((ev C D (if q = 0 then 1 else 0) (if q + 1 = tr.height t then 1 else 0)
      (if q + 1 = tr.height t then 0 else 1) (fun i => ((pub.getD i 0).toNat : Int)) e : Int) : Fp)
  | .const v => by
    show (v : Fp) = _
    simp only [ev]; rw [Lean.Grind.Ring.intCast_natCast]
  | .col x nx => by
    cases nx
    · exact hC x
    · exact hD x
  | .pub i => by
    show pub.getD i 0 = _
    simp only [ev]; rw [Lean.Grind.Ring.intCast_natCast]; exact (Fp.ofNat_toNat _).symm
  | .isFirst => by
    show (if q = 0 then 1 else 0 : Fp) = _
    simp only [ev]; split <;> rfl
  | .isLast => by
    show (if q + 1 = tr.height t then 1 else 0 : Fp) = _
    simp only [ev]; split <;> rfl
  | .isTransition => by
    show (if q + 1 = tr.height t then 0 else 1 : Fp) = _
    simp only [ev]; split <;> rfl
  | .add a b => by
    show a.eval tr t q pub + b.eval tr t q pub = _
    rw [ev_sound hC hD a, ev_sound hC hD b]; simp only [ev]; rw [Lean.Grind.Ring.intCast_add]
  | .mul a b => by
    show a.eval tr t q pub * b.eval tr t q pub = _
    rw [ev_sound hC hD a, ev_sound hC hD b]; simp only [ev]; rw [Lean.Grind.Ring.intCast_mul]
  | .neg a => by
    show -a.eval tr t q pub = _
    rw [ev_sound hC hD a]; simp only [ev]; rw [Lean.Grind.Ring.intCast_neg]

theorem eval_zero_of_ev {tr : Trace Fp} {t q : Nat} {pub : List Fp} {C D : Nat → Int}
    (hC : ∀ x, tr.cell t q x = ((C x : Int) : Fp))
    (hD : ∀ x, tr.cell t ((q + 1) % tr.height t) x = ((D x : Int) : Fp)) {e : Expr}
    (h : ev C D (if q = 0 then 1 else 0) (if q + 1 = tr.height t then 1 else 0)
      (if q + 1 = tr.height t then 0 else 1) (fun i => ((pub.getD i 0).toNat : Int)) e = 0) :
    e.eval tr t q pub = 0 := by
  rw [ev_sound hC hD e, h]; rfl

/-- The integer image of a natural cell. -/
theorem ofNat_int (v : Nat) : Fp.ofNat v = (((v : Nat) : Int) : Fp) := by
  rw [Lean.Grind.Ring.intCast_natCast]; rfl

/-- Integer cells from natural cells below a width `W` (junk above). -/
def cellsI (f : Nat → Nat) (W : Nat) (tr : Trace Fp) (t q : Nat) (x : Nat) : Int :=
  if x < W then (f x : Int) else ((tr.cell t q x).toNat : Int)

theorem cellsI_ok {f : Nat → Nat} {W : Nat} {tr : Trace Fp} {t q : Nat}
    (h : ∀ x, x < W → tr.cell t q x = Fp.ofNat (f x)) : ∀ x, tr.cell t q x = ((cellsI f W tr t q x : Int) : Fp) := by
  intro x
  unfold cellsI
  split
  · rw [h x (by assumption), ofNat_int]
  · rw [Lean.Grind.Ring.intCast_natCast]; exact (Fp.ofNat_toNat _).symm

end EvI

end ZkFormal.Near.Render
