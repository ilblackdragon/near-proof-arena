import M5T1.Bus
import M5T1.Walk

/-!
# M5T1.MsgRowBase — the `MSG` constraints as natural-number facts (F-2)

Helpers for `MsgRow.lean`: `V tr pub r s j` is column `s` (offset `j`) of row `r` of `MSG`
(table 3 of `fullAir`) as a natural `< p`; every constraint of `Msg.constraints` used by the row
lemma is restated (`c…`) as the exact natural-number fact it gives on a row of a `Holds` trace,
under the Boolean facts it needs (supplied by the caller: the descriptor columns come from the
schema, `MsgRow.sch_row`).
-/

namespace M5T1.MsgRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.Bus

section
variable (tr : Trace Fp) (pub : List Fp)
/-- Column `s` (offset `j`) of `MSG` row `r`, as a natural `< p`. -/
def V (r : Nat) (s : String) (j : Nat := 0) : Nat := ev tr 3 r pub (Msg.c s j)
end

section ev
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

@[simp] theorem ev_hsub (a b : Expr) : ev tr t r pub (a - b) =
    (ev tr t r pub a + (2013265921 - ev tr t r pub b) % 2013265921) % 2013265921 := by
  show ev tr t r pub (.add a (.neg b)) = _
  rw [ev_add, ev_neg]
@[simp] theorem ev_hmul (a b : Expr) : ev tr t r pub (a * b) = ev tr t r pub a * ev tr t r pub b % 2013265921 :=
  ev_mul a b
@[simp] theorem ev_hadd (a b : Expr) : ev tr t r pub (a + b) = (ev tr t r pub a + ev tr t r pub b) % 2013265921 :=
  ev_add a b
@[simp] theorem ev_one' : ev tr t r pub (1 : Expr) = 1 := by
  show ev tr t r pub (.const 1) = 1; rw [ev_const]
@[simp] theorem ev_K' (c : Nat) : ev tr t r pub (K c) = c % 2013265921 := ev_const c

theorem evc (r : Nat) (s : String) (j : Nat) : ev tr 3 r pub (Msg.c s j) = V tr pub r s j := rfl

theorem evn (h : r + 1 < tr.height 3) (s : String) (j : Nat) :
    ev tr 3 r pub (Msg.n s j) = V tr pub (r + 1) s j := by
  show ev tr 3 r pub (.col (Msg.L.off s + j) true) = ev tr 3 (r + 1) pub (.col (Msg.L.off s + j) false)
  rw [Bus.ev_next, Nat.mod_eq_of_lt h]

theorem ev_tr (h : r + 1 < tr.height t) : ev tr t r pub .isTransition = 1 := by
  show (Expr.eval .isTransition tr t r pub).toNat = 1
  simp only [Expr.eval, Expr.evalWith, rowEnv, show ¬ (r + 1 = tr.height t) by omega, ite_false]
  rfl

theorem ev_first0 : ev tr t 0 pub .isFirst = 1 := rfl

theorem ev_last (h : r + 1 = tr.height t) : ev tr t r pub .isLast = 1 := by
  show (Expr.eval .isLast tr t r pub).toNat = 1
  simp only [Expr.eval, Expr.evalWith, rowEnv, h, ite_true]
  rfl

theorem V_lt (tr : Trace Fp) (pub : List Fp) (r : Nat) (s : String) (j : Nat := 0) :
    V tr pub r s j < 2013265921 := ev_lt _

theorem V_eq {s : String} {j c : Nat} (h : Msg.L.off s + j = c) (r : Nat) :
    V tr pub r s j = (tr.cell 3 r c).toNat := by subst h; rfl
end ev

/-! ## Little-endian values -/

theorem leV_append (l : List Nat) (a : Nat) : leV (l ++ [a]) = leV l + 256 ^ l.length * a := by
  induction l with
  | nil => simp [leV]
  | cons b l ih => simp only [List.cons_append, leV, ih, List.length_cons, Nat.pow_succ]; rw [Nat.mul_add,
      ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ l.length)]; omega

theorem leV_lt (l : List Nat) (h : ∀ b ∈ l, b < 256) : leV l < 256 ^ l.length := by
  induction l with
  | nil => simp [leV]
  | cons b l ih =>
    have hb := h b (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [leV, List.length_cons, Nat.pow_succ]
    omega

/-! ## The `MSG` table of `fullAir` -/

section holds
variable {tape xtape : List (Nat × Bool × List Nat)} {tr : Trace Fp} {pub : List Fp}

theorem msg_lt : 3 < (fullAir tape xtape).tables.length := by rw [fullAir_len]; decide

theorem msg_height (H : Holds (fullAir tape xtape) pub tr) : tr.height 3 ≤ 2 ^ 20 := by
  have h := (H.logBound 3 msg_lt).2
  have h8 : ((fullAir tape xtape).tables[3]'msg_lt).maxLog = 20 := rfl
  rw [h8] at h
  exact Nat.pow_le_pow_right (by decide) h

theorem mcons (H : Holds (fullAir tape xtape) pub tr) {r : Nat} (hr : r < tr.height 3) {e : Expr}
    (he : e ∈ Msg.constraints) : ev tr 3 r pub e = 0 :=
  ev_of_eval (H.constr 3 msg_lt r hr e he)

theorem mc (H : Holds (fullAir tape xtape) pub tr) {r : Nat} (hr : r < tr.height 3) (i : Nat)
    (hi : i < Msg.constraints.length) (X : Expr) (hX : Msg.constraints[i]'hi = X) :
    ev tr 3 r pub X = 0 := hX ▸ mcons H hr (List.getElem_mem hi)

/-- The `RNG` byte facts of an active row (`b`, `dm`). -/
theorem msg_rng (H : Holds (fullAir tape xtape) pub tr) (h1 : NoRng tape) (h2 : NoRng xtape)
    {r : Nat} (hr : r < tr.height 3) (hA : V tr pub r "act" = 1) {e : Expr}
    (hi : rcv B_RNG (Msg.c "act") [e] ∈ Msg.interactions) : ev tr 3 r pub e < 256 := by
  have hg : (Msg.c "act").eval tr 3 r pub = 1 := eval_of_ev (e := Msg.c "act") hA (by decide)
  exact rng_recv H h1 h2 msg_lt hr hi rfl rfl (by rw [multNat_one hg]; decide) rfl

theorem b_lt (H : Holds (fullAir tape xtape) pub tr) (h1 : NoRng tape) (h2 : NoRng xtape)
    {r : Nat} (hr : r < tr.height 3) (hA : V tr pub r "act" = 1) : V tr pub r "b" < 256 :=
  msg_rng H h1 h2 hr hA (by simp only [Msg.interactions]; simp)

theorem dm_lt (H : Holds (fullAir tape xtape) pub tr) (h1 : NoRng tape) (h2 : NoRng xtape)
    {r : Nat} (hr : r < tr.height 3) (hA : V tr pub r "act" = 1) (i : Nat) (hi : i < 3) :
    V tr pub r "dm" i < 256 := by
  apply msg_rng H h1 h2 hr hA
  simp only [Msg.interactions]
  obtain _ | _ | _ | i := i <;> simp <;> omega

/-! ### The constraints, one by one (`Msg.constraints[i]`) -/

local macro "vsimp" h:ident : tactic =>
  `(tactic| simp only [ev_hsub, ev_hmul, ev_hadd, ev_one', ev_K', evc] at $h:ident)

local macro "vomega" : tactic =>
  `(tactic| ((try simp only [Nat.one_mul, Nat.mul_one, Nat.zero_mul, Nat.mul_zero, Nat.zero_add,
    Nat.add_zero, Nat.zero_mod, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul,
    Nat.mod_mod] at *) <;> omega))

variable (H : Holds (fullAir tape xtape) pub tr) {r : Nat}
include H

theorem cbool (hr : r < tr.height 3) (i : Nat) (hi : i < 5) :
    V tr pub r (["e", "k0", "first", "endm", "z"].getD i "") ≤ 1 := by
  obtain _ | _ | _ | _ | _ | i := i
  · exact bool_le (mc H hr 0 (by decide) _ rfl)
  · exact bool_le (mc H hr 1 (by decide) _ rfl)
  · exact bool_le (mc H hr 2 (by decide) _ rfl)
  · exact bool_le (mc H hr 3 (by decide) _ rfl)
  · exact bool_le (mc H hr 4 (by decide) _ rfl)
  · vomega

theorem e_le (hr : r < tr.height 3) : V tr pub r "e" ≤ 1 := cbool H hr 0 (by decide)
theorem k0_le (hr : r < tr.height 3) : V tr pub r "k0" ≤ 1 := cbool H hr 1 (by decide)
theorem first_le (hr : r < tr.height 3) : V tr pub r "first" ≤ 1 := cbool H hr 2 (by decide)
theorem endm_le (hr : r < tr.height 3) : V tr pub r "endm" ≤ 1 := cbool H hr 3 (by decide)
theorem z_le (hr : r < tr.height 3) : V tr pub r "z" ≤ 1 := cbool H hr 4 (by decide)

/-- `(1 − act)·first`: a `first` row is active. -/
theorem c6 (hr : r < tr.height 3) (hf : V tr pub r "first" = 1) : V tr pub r "act" = 1 := by
  have h := mc H hr 6 (by decide) ((1 - Msg.c "act") * Msg.c "first") rfl
  vsimp h; rw [hf] at h
  have := V_lt tr pub r "act"; vomega

/-- `isFirst·(first − 1)`: row 0 starts a message. -/
theorem c9 (h0 : 0 < tr.height 3) : V tr pub 0 "first" = 1 := by
  have h := mc H h0 9 (by decide) (.isFirst * (Msg.c "first" - 1)) rfl
  vsimp h; rw [ev_first0] at h
  have := V_lt tr pub 0 "first"; vomega

theorem c10 (hr : r + 1 < tr.height 3) (hA : V tr pub r "act" = 0) : V tr pub (r + 1) "act" = 0 := by
  have h := mc H (r := r) (by vomega) 10 (by decide) (.isTransition * (1 - Msg.c "act") * Msg.n "act") rfl
  vsimp h; rw [ev_tr hr, evn hr, hA] at h
  have := V_lt tr pub (r + 1) "act"; vomega

theorem c11 (hr : r + 1 < tr.height 3) (he : V tr pub r "e" ≤ 1) (hm : V tr pub r "endm" ≤ 1) :
    V tr pub (r + 1) "first" =
      (if V tr pub r "e" = 1 ∧ V tr pub r "endm" = 1 then V tr pub (r + 1) "act" else 0) := by
  have h := mc H (r := r) (by vomega) 11 (by decide)
    (.isTransition * (Msg.n "first" - Msg.n "act" * Msg.c "e" * Msg.c "endm")) rfl
  vsimp h; rw [ev_tr hr, evn hr, evn hr] at h
  have := V_lt tr pub (r + 1) "act"; have := V_lt tr pub (r + 1) "first"
  split
  · rename_i hc; rw [hc.1, hc.2] at h; vomega
  · rename_i hc
    have : V tr pub r "e" = 0 ∨ V tr pub r "endm" = 0 := by vomega
    rcases this with h' | h' <;> rw [h'] at h <;> simp at h <;> vomega

theorem c12 (hr : r + 1 < tr.height 3) (hA : V tr pub r "act" = 1) (hm : V tr pub r "endm" = 0) :
    V tr pub (r + 1) "act" = 1 := by
  have h := mc H (r := r) (by vomega) 12 (by decide)
    (.isTransition * Msg.c "act" * (1 - Msg.n "act") * (1 - Msg.c "endm")) rfl
  vsimp h; rw [ev_tr hr, evn hr, hA, hm] at h
  have := V_lt tr pub (r + 1) "act"; vomega

theorem c13 (hr : r + 1 < tr.height 3) (hA : V tr pub (r + 1) "act" = 1)
    (hf : V tr pub (r + 1) "first" = 0) : V tr pub r "inm" = 1 := by
  have h := mc H (r := r) (by vomega) 13 (by decide)
    (.isTransition * (Msg.c "inm" - Msg.n "act" * (1 - Msg.n "first"))) rfl
  vsimp h; rw [ev_tr hr, evn hr, evn hr, hA, hf] at h
  have := V_lt tr pub r "inm"; vomega

/-- A constraint `isTransition · inm · (n x − c x)`. -/
theorem cconst (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) (i : Nat) (s : String)
    (hi' : i < Msg.constraints.length)
    (hX : Msg.constraints[i]'hi' = .isTransition * Msg.c "inm" * (Msg.n s - Msg.c s)) :
    V tr pub (r + 1) s = V tr pub r s := by
  have h := mc H (r := r) (by vomega) i hi' _ hX
  vsimp h; rw [ev_tr hr, evn hr, hi] at h
  have := V_lt tr pub (r + 1) s; have := V_lt tr pub r s; vomega

theorem c14 (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) : V tr pub (r + 1) "mf" = V tr pub r "mf" :=
  cconst H hr hi 14 "mf" (by decide) rfl
theorem c15 (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) : V tr pub (r + 1) "mt" = V tr pub r "mt" :=
  cconst H hr hi 15 "mt" (by decide) rfl

theorem c18 (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) :
    V tr pub (r + 1) "j" = (V tr pub r "j" + 1) % 2013265921 := by
  have h := mc H (r := r) (by vomega) 18 (by decide)
    (.isTransition * Msg.c "inm" * (Msg.n "j" - Msg.c "j" - 1)) rfl
  vsimp h; rw [ev_tr hr, evn hr, hi] at h
  have := V_lt tr pub (r + 1) "j"; have := V_lt tr pub r "j"; vomega

theorem c19 (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) (he : V tr pub r "e" ≤ 1) :
    V tr pub (r + 1) "qf" = (V tr pub r "qf" + V tr pub r "e" * V tr pub (r + 1) "newR") % 2013265921 := by
  have h := mc H (r := r) (by vomega) 19 (by decide)
    (.isTransition * Msg.c "inm" * (Msg.n "qf" - Msg.c "qf" - Msg.c "e" * Msg.n "newR")) rfl
  vsimp h; rw [ev_tr hr, evn hr, evn hr, hi] at h
  have := V_lt tr pub (r + 1) "qf"; have := V_lt tr pub r "qf"; have := V_lt tr pub (r + 1) "newR"
  rcases (show V tr pub r "e" = 0 ∨ V tr pub r "e" = 1 by vomega) with h' | h' <;> rw [h'] at h ⊢ <;>
    simp at h ⊢ <;> vomega

theorem c20 (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) :
    V tr pub (r + 1) "k0" = V tr pub r "e" := by
  have h := mc H (r := r) (by vomega) 20 (by decide)
    (.isTransition * Msg.c "inm" * (Msg.n "k0" - Msg.c "e")) rfl
  vsimp h; rw [ev_tr hr, evn hr, hi] at h
  have := V_lt tr pub (r + 1) "k0"; have := V_lt tr pub r "e"; vomega

theorem c21 (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) (he : V tr pub r "e" ≤ 1) :
    V tr pub (r + 1) "k" = (if V tr pub r "e" = 1 then 0 else (V tr pub r "k" + 1) % 2013265921) := by
  have h := mc H (r := r) (by vomega) 21 (by decide)
    (.isTransition * Msg.c "inm" * (Msg.n "k" - (1 - Msg.c "e") * (Msg.c "k" + 1))) rfl
  vsimp h; rw [ev_tr hr, evn hr, hi] at h
  have := V_lt tr pub (r + 1) "k"; have := V_lt tr pub r "k"
  rcases (show V tr pub r "e" = 0 ∨ V tr pub r "e" = 1 by vomega) with h' | h' <;> rw [h'] at h ⊢ <;>
    simp at h ⊢ <;> vomega

theorem c22 (hr : r < tr.height 3) (hz : V tr pub r "z" ≤ 1) (hs : V tr pub r "skipS" < 2013265921)
    (hn : V tr pub r "nextS" < 2013265921) :
    V tr pub r "ns" = (if V tr pub r "z" = 1 then V tr pub r "skipS" else V tr pub r "nextS") := by
  have h := mc H hr 22 (by decide)
    (Msg.c "ns" - Msg.c "nextS" - Msg.c "z" * (Msg.c "skipS" - Msg.c "nextS")) rfl
  vsimp h
  have := V_lt tr pub r "ns"
  rcases (show V tr pub r "z" = 0 ∨ V tr pub r "z" = 1 by vomega) with h' | h' <;> rw [h'] at h ⊢ <;>
    simp at h ⊢ <;> vomega

theorem c23 (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) (he : V tr pub r "e" ≤ 1) :
    V tr pub (r + 1) "s" = (if V tr pub r "e" = 1 then V tr pub r "ns" else V tr pub r "s") := by
  have h := mc H (r := r) (by vomega) 23 (by decide)
    (.isTransition * Msg.c "inm" * (Msg.n "s" - (1 - Msg.c "e") * Msg.c "s" - Msg.c "e" * Msg.c "ns")) rfl
  vsimp h; rw [ev_tr hr, evn hr, hi] at h
  have := V_lt tr pub (r + 1) "s"; have := V_lt tr pub r "s"; have := V_lt tr pub r "ns"
  rcases (show V tr pub r "e" = 0 ∨ V tr pub r "e" = 1 by vomega) with h' | h' <;> rw [h'] at h ⊢ <;>
    simp at h ⊢ <;> vomega

theorem c24 (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) (he : V tr pub r "e" = 0) :
    V tr pub (r + 1) "L" = V tr pub r "L" := by
  have h := mc H (r := r) (by vomega) 24 (by decide)
    (.isTransition * Msg.c "inm" * (1 - Msg.c "e") * (Msg.n "L" - Msg.c "L")) rfl
  vsimp h; rw [ev_tr hr, evn hr, hi, he] at h
  have := V_lt tr pub (r + 1) "L"; have := V_lt tr pub r "L"; vomega

theorem c25 (hr : r < tr.height 3) (hp : V tr pub r "kLP" + V tr pub r "kLE" = 1) (he : V tr pub r "e" = 1)
    (hz : V tr pub r "z" = 0) : V tr pub r "setL" = 1 := by
  have h := mc H hr 25 (by decide)
    (Msg.c "setL" - (Msg.c "kLP" + Msg.c "kLE") * Msg.c "e" * (1 - Msg.c "z")) rfl
  vsimp h; rw [hp, he, hz] at h
  have := V_lt tr pub r "setL"; simp at h; vomega

theorem c26 (hr : r + 1 < tr.height 3) (hi : V tr pub r "inm" = 1) (hs : V tr pub r "setL" = 1) :
    V tr pub (r + 1) "L" = V tr pub r "acc" := by
  have h := mc H (r := r) (by vomega) 26 (by decide)
    (.isTransition * Msg.c "inm" * Msg.c "setL" * (Msg.n "L" - Msg.c "acc")) rfl
  vsimp h; rw [ev_tr hr, evn hr, hi, hs] at h
  have := V_lt tr pub (r + 1) "L"; have := V_lt tr pub r "acc"; vomega

theorem c27 (hr : r < tr.height 3) (hv : V tr pub r "var" = 0) : V tr pub r "L" = V tr pub r "fixL" := by
  have h := mc H hr 27 (by decide) ((1 - Msg.c "var") * (Msg.c "L" - Msg.c "fixL")) rfl
  vsimp h; rw [hv] at h
  have := V_lt tr pub r "L"; have := V_lt tr pub r "fixL"; simp at h; vomega

theorem c28 (hr : r < tr.height 3) (he : V tr pub r "e" = 1) :
    V tr pub r "L" = (V tr pub r "k" + 1) % 2013265921 := by
  have h := mc H hr 28 (by decide) (Msg.c "e" * (Msg.c "k" - Msg.c "L" + 1)) rfl
  vsimp h; rw [he] at h
  have := V_lt tr pub r "L"; have := V_lt tr pub r "k"; vomega

/-- The message-start constraints `first · (x − y)`. -/
theorem cfirst (hr : r < tr.height 3) (hf : V tr pub r "first" = 1) :
    V tr pub r "j" = 0 ∧ V tr pub r "k" = 0 ∧ V tr pub r "s" = 0 ∧ V tr pub r "qf" = V tr pub r "mf" ∧
      V tr pub r "k0" = 1 := by
  have h1 := mc H hr 29 (by decide) (Msg.c "first" * Msg.c "j") rfl
  have h2 := mc H hr 30 (by decide) (Msg.c "first" * Msg.c "k") rfl
  have h3 := mc H hr 31 (by decide) (Msg.c "first" * Msg.c "s") rfl
  have h4 := mc H hr 32 (by decide) (Msg.c "first" * (Msg.c "qf" - Msg.c "mf")) rfl
  have h5 := mc H hr 33 (by decide) (Msg.c "first" * (Msg.c "k0" - 1)) rfl
  vsimp h1; vsimp h2; vsimp h3; vsimp h4; vsimp h5
  rw [hf] at h1 h2 h3 h4 h5
  have := V_lt tr pub r "j"; have := V_lt tr pub r "k"; have := V_lt tr pub r "s"
  have := V_lt tr pub r "qf"; have := V_lt tr pub r "mf"; have := V_lt tr pub r "k0"
  vomega

/-- `pb = pw·b`. -/
theorem c35 (hr : r < tr.height 3) :
    V tr pub r "pb" = V tr pub r "pw" * V tr pub r "b" % 2013265921 := by
  have h := mc H hr 35 (by decide) (Msg.c "pb" - Msg.c "pw" * Msg.c "b") rfl
  vsimp h
  have := V_lt tr pub r "pb"
  have : V tr pub r "pw" * V tr pub r "b" % 2013265921 < 2013265921 := Nat.mod_lt _ (by decide)
  generalize V tr pub r "pw" * V tr pub r "b" % 2013265921 = x at *
  vomega

theorem c36 (hr : r < tr.height 3) (hl : V tr pub r "kLP" + V tr pub r "kLE" + V tr pub r "kCNT" = 1)
    (hk : V tr pub r "k0" = 1) : V tr pub r "pw" = 1 ∧ V tr pub r "acc" = V tr pub r "b" := by
  have h1 := mc H hr 36 (by decide)
    ((Msg.c "kLP" + Msg.c "kLE" + Msg.c "kCNT") * Msg.c "k0" * (Msg.c "pw" - 1)) rfl
  have h2 := mc H hr 37 (by decide)
    ((Msg.c "kLP" + Msg.c "kLE" + Msg.c "kCNT") * Msg.c "k0" * (Msg.c "acc" - Msg.c "b")) rfl
  vsimp h1; vsimp h2
  rw [show (V tr pub r "kLP" + V tr pub r "kLE") % 2013265921 = V tr pub r "kLP" + V tr pub r "kLE" from
    Nat.mod_eq_of_lt (by vomega), hl, hk] at h1 h2
  have := V_lt tr pub r "pw"; have := V_lt tr pub r "acc"; have := V_lt tr pub r "b"
  vomega

theorem c38 (hr : r + 1 < tr.height 3) (hk : V tr pub (r + 1) "k0" = 0)
    (hl : V tr pub (r + 1) "kLP" + V tr pub (r + 1) "kLE" + V tr pub (r + 1) "kCNT" = 1) :
    V tr pub (r + 1) "pw" = 256 * V tr pub r "pw" % 2013265921 ∧
      V tr pub (r + 1) "acc" = (V tr pub r "acc" + V tr pub (r + 1) "pb") % 2013265921 := by
  have h1 := mc H (r := r) (by vomega) 38 (by decide)
    (.isTransition * (1 - Msg.n "k0") * (Msg.n "kLP" + Msg.n "kLE" + Msg.n "kCNT") *
      (Msg.n "pw" - K 256 * Msg.c "pw")) rfl
  have h2 := mc H (r := r) (by vomega) 39 (by decide)
    (.isTransition * (1 - Msg.n "k0") * (Msg.n "kLP" + Msg.n "kLE" + Msg.n "kCNT") *
      (Msg.n "acc" - Msg.c "acc" - Msg.n "pb")) rfl
  vsimp h1; vsimp h2
  simp only [ev_tr hr, evn hr] at h1 h2
  rw [show (V tr pub (r + 1) "kLP" + V tr pub (r + 1) "kLE") % 2013265921 =
    V tr pub (r + 1) "kLP" + V tr pub (r + 1) "kLE" from Nat.mod_eq_of_lt (by vomega), hl, hk] at h1 h2
  have := V_lt tr pub (r + 1) "pw"; have := V_lt tr pub (r + 1) "acc"; have := V_lt tr pub r "acc"
  have := V_lt tr pub (r + 1) "pb"; have := V_lt tr pub r "pw"
  simp at h1 h2
  vomega

theorem c40 (hr : r < tr.height 3) (hl : V tr pub r "kLP" + V tr pub r "kLE" + V tr pub r "kCNT" = 1)
    (he : V tr pub r "e" = 1) : V tr pub r "b" = 0 := by
  have h := mc H hr 40 (by decide) ((Msg.c "kLP" + Msg.c "kLE" + Msg.c "kCNT") * Msg.c "e" * Msg.c "b") rfl
  vsimp h
  rw [show (V tr pub r "kLP" + V tr pub r "kLE") % 2013265921 = V tr pub r "kLP" + V tr pub r "kLE" from
    Nat.mod_eq_of_lt (by vomega), hl, he] at h
  have := V_lt tr pub r "b"; vomega

/-- `(1 − isLenP·e)·z`: `z = 0` off the last byte of a `K_LP`/`K_LE` prefix. -/
theorem c41 (hr : r < tr.height 3) (hp : V tr pub r "kLP" + V tr pub r "kLE" ≤ 1) (he : V tr pub r "e" ≤ 1)
    (h : V tr pub r "kLP" + V tr pub r "kLE" = 0 ∨ V tr pub r "e" = 0) : V tr pub r "z" = 0 := by
  have h1 := mc H hr 41 (by decide) ((1 - (Msg.c "kLP" + Msg.c "kLE") * Msg.c "e") * Msg.c "z") rfl
  vsimp h1
  rw [show (V tr pub r "kLP" + V tr pub r "kLE") % 2013265921 = V tr pub r "kLP" + V tr pub r "kLE" from
    Nat.mod_eq_of_lt (by omega)] at h1
  have := V_lt tr pub r "z"
  rcases h with h | h <;> rw [h] at h1 <;> vomega

/-- `z · acc`: `z = 1 ⇒ acc = 0`. -/
theorem c42 (hr : r < tr.height 3) (hz : V tr pub r "z" = 1) : V tr pub r "acc" = 0 := by
  have h2 := mc H hr 42 (by decide) (Msg.c "z" * Msg.c "acc") rfl
  vsimp h2; rw [hz] at h2
  have := V_lt tr pub r "acc"; vomega

/-- `isLenP·e·(acc·accInv − 1 + z)`: `z = 0 ⇒ acc ≠ 0` on the last byte of a prefix. -/
theorem c43 (hr : r < tr.height 3) (hp : V tr pub r "kLP" + V tr pub r "kLE" = 1) (he : V tr pub r "e" = 1)
    (hz : V tr pub r "z" = 0) : V tr pub r "acc" ≠ 0 := by
  have h3 := mc H hr 43 (by decide)
    ((Msg.c "kLP" + Msg.c "kLE") * Msg.c "e" * (Msg.c "acc" * Msg.c "accInv" - 1 + Msg.c "z")) rfl
  vsimp h3
  rw [show (V tr pub r "kLP" + V tr pub r "kLE") % 2013265921 = 1 from by rw [hp], he, hz] at h3
  intro h0; rw [h0] at h3; simp at h3

theorem c44 (hr : r < tr.height 3) (hc : V tr pub r "kC" = 1) : V tr pub r "b" = V tr pub r "cv" := by
  have h := mc H hr 44 (by decide) (Msg.c "kC" * (Msg.c "b" - Msg.c "cv")) rfl
  vsimp h; rw [hc] at h
  have := V_lt tr pub r "b"; have := V_lt tr pub r "cv"; vomega

theorem c45 (hr : r < tr.height 3) (hm : V tr pub r "endm" = 1) : V tr pub r "e" = 1 := by
  have h := mc H hr 45 (by decide) (Msg.c "endm" * (1 - Msg.c "e")) rfl
  vsimp h; rw [hm] at h
  have := V_lt tr pub r "e"; vomega

theorem c46 (hr : r < tr.height 3) (hm : V tr pub r "endm" = 1) (ho : V tr pub r "endOK" ≤ 1)
    (hz : V tr pub r "z" ≤ 1) (hs : V tr pub r "skipEnd" ≤ 1) :
    V tr pub r "endOK" + V tr pub r "z" * V tr pub r "skipEnd" = 1 := by
  have h := mc H hr 46 (by decide)
    (Msg.c "endm" * (1 - Msg.c "endOK" - Msg.c "z" * Msg.c "skipEnd")) rfl
  vsimp h; rw [hm] at h
  rcases (show V tr pub r "z" = 0 ∨ V tr pub r "z" = 1 by vomega) with h' | h' <;> rw [h'] at h ⊢ <;>
  rcases (show V tr pub r "skipEnd" = 0 ∨ V tr pub r "skipEnd" = 1 by vomega) with h'' | h'' <;>
    rw [h''] at h ⊢ <;> simp at h ⊢ <;> vomega

theorem c47 (hr : r < tr.height 3) (he : V tr pub r "e" = 1) (hm : V tr pub r "endm" = 0) :
    V tr pub r "cont" = 1 ∧ V tr pub r "z" * V tr pub r "skipEnd" = 0 := by
  have h1 := mc H hr 47 (by decide) (Msg.c "e" * (1 - Msg.c "endm") * (1 - Msg.c "cont")) rfl
  have h2 := mc H hr 48 (by decide) (Msg.c "z" * Msg.c "skipEnd" * (1 - Msg.c "endm")) rfl
  vsimp h1; vsimp h2; rw [he, hm] at h1; rw [hm] at h2
  have := V_lt tr pub r "cont"
  simp at h1 h2
  have h3 : V tr pub r "z" * V tr pub r "skipEnd" % 2013265921 = 0 := by vomega
  refine ⟨by vomega, ?_⟩
  have hz := z_le H hr
  rcases (show V tr pub r "z" = 0 ∨ V tr pub r "z" = 1 by vomega) with h' | h' <;> rw [h'] at h3 ⊢ <;> simp at h3 ⊢
  have := V_lt tr pub r "skipEnd"; vomega

theorem c49 (hr : r + 1 = tr.height 3) (hA : V tr pub r "act" = 1) : V tr pub r "endm" = 1 := by
  have h := mc H (r := r) (by vomega) 49 (by decide) (.isLast * Msg.c "act" * (1 - Msg.c "endm")) rfl
  vsimp h; rw [ev_last hr, hA] at h
  have := V_lt tr pub r "endm"; vomega

end holds

end M5T1.MsgRow
