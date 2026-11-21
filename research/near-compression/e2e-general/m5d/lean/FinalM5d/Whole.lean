import FinalM5d.BusMem
import FinalM5d.Tail

/-!
# FinalM5d.Whole — the deployed FINAL AIR, and facts about it from `Holds` of the whole AIR

**`finalAirS`** is the AIR the prover runs: `finalAir`'s twelve Lean tables, then lane B's chip
stub `chipStubOn B_IF384` (`StateM5a.ChipStub`), the Lean stand-in for the native SHA-512
compression chip's `IF384` sends (lane B's `holds_of_holdsX` turns a precheck-accepted trace —
every bus but `IF384` balanced, the chip's sends a permutation of the `IF384` receives — into
`Holds finalAirS`; without the stub `Holds finalAir` would be unsatisfiable, since `S384` receives
on `IF384` and no Lean table sends there).

Generic plumbing here (`onlyIn`, `occ_in`, `evalOne`, `ev_eq_of_msg`); the first whole-AIR
theorem is **`hb_bytes`**: on every active `FIN` row, every statement-stream cell is a byte —
`FinRow.HbBytes`, until now a premise of `final_template_sound`. The chain: `FIN` receives
`HB (k, hb_k)` → only `STMT` sends `HB`, with `h = 1`, hence `act = 1` → `STMT` sends
`SB (CLAIM, k, b)` → only `S384` receives `SB`, with a data flag `f_j = 1`, hence `act = 1`
(the flags are monotone) → `S384` looks the byte up on `R8` / `S2` / `S5` → only `RNG` sends
those, and its value `v` is the 8-bit decomposition `Σ 2^i β_i` with boolean `β`.
-/

namespace FinalM5d.Whole

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.BusMem FinalM5d.FinRow

/-- **The deployed FINAL AIR**: `finalAir` + the `IF384` chip stub (table 12). -/
def finalAirS : Air :=
  { finalAir with tables := finalAir.tables ++ [StateM5a.ChipStub.chipStubOn B_IF384] }

theorem finalAirS_len : finalAirS.tables.length = 13 := rfl

/-! ## Generic -/

/-- Only the tables `ks` have an interaction on `(b, s)`. -/
def onlyIn (A : Air) (b : Nat) (s : Bool) (ks : List Nat) : Bool :=
  (List.range A.tables.length).all fun t =>
    ks.contains t || (A.tables[t]!).interactions.all fun i => !(i.bus == b && i.send == s)

theorem occ_in {A : Air} {tr : Trace Fp} {pub : List Fp} {b : Nat} {s : Bool} {m : List Fp}
    {ks : List Nat} (h : onlyIn A b s ks = true) (ho : Occ A tr pub b s m) :
    ∃ t ∈ ks, ∃ ht : t < A.tables.length, ∃ r, r < tr.height t ∧ ∃ i ∈ (A.tables[t]'ht).interactions,
      i.bus = b ∧ i.send = s ∧ i.multNat tr t r pub ≠ 0 ∧ i.msgVal tr t r pub = m := by
  obtain ⟨t, ht, r, hr, i, hi, hb, hs, hn, hm⟩ := ho
  have h1 := List.all_eq_true.1 h t (List.mem_range.2 ht)
  simp only [Bool.or_eq_true, List.contains_iff_mem] at h1
  rcases h1 with hk | hall
  · exact ⟨t, hk, ht, r, hr, i, hi, hb, hs, hn, hm⟩
  · exfalso
    rw [getElem!_pos A.tables t ht] at hall
    have := List.all_eq_true.1 hall i hi
    simp [hb, hs] at this

/-- An interaction list has nothing on `(b, s)`. -/
def noneOn (l : List Interaction) (b : Nat) (s : Bool) : Bool :=
  l.all fun i => !(i.bus == b && i.send == s)

theorem not_mem_of_noneOn {l : List Interaction} {b : Nat} {s : Bool} (h : noneOn l b s = true)
    {i : Interaction} (hi : i ∈ l) (hb : i.bus = b) (hs : i.send = s) : False := by
  have := List.all_eq_true.1 h i hi
  simp [hb, hs] at this

variable {tr : Trace Fp} {pub : List Fp}

theorem evalOne {e : Expr} {t r : Nat} (h : ev tr t r pub e = 1) : e.eval tr t r pub = 1 :=
  Fp.ext (by rw [Fp.toNat_one]; exact h)

theorem ev_one {e : Expr} {t r : Nat} (h : e.eval tr t r pub = 1) : ev tr t r pub e = 1 := by
  unfold ev; rw [h]; rfl

/-- Equal field values have equal naturals. -/
theorem ev_eq_of_eval {e e' : Expr} {t r t' r' : Nat} (h : e.eval tr t r pub = e'.eval tr t' r' pub) :
    ev tr t r pub e = ev tr t' r' pub e' := by
  unfold ev; rw [h]

theorem msg_cons {e : Expr} {es : List Expr} {t r : Nat} {m : List Fp}
    (h : (e :: es).map (fun x => x.eval tr t r pub) = m) :
    ∃ m', m = e.eval tr t r pub :: m' ∧ es.map (fun x => x.eval tr t r pub) = m' := by
  subst h; exact ⟨_, rfl, rfl⟩

/-- Componentwise reading of a message equality. -/
theorem msg_get {es es' : List Expr} {t r t' r' : Nat}
    (h : es.map (fun x => x.eval tr t r pub) = es'.map (fun x => x.eval tr t' r' pub)) (j : Nat)
    (hj : j < es.length) (hj' : j < es'.length) :
    ev tr t r pub (es[j]'hj) = ev tr t' r' pub (es'[j]'hj') := by
  apply ev_eq_of_eval
  have := congrArg (fun l => l[j]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
    Option.map_some, Option.some.injEq] at this
  exact this

/-- A gate `g · x` with `g = 1` gives `x = 0`. -/
theorem gated {g x : Expr} {t r : Nat} (h : (g * x).eval tr t r pub = 0) (hg : ev tr t r pub g = 1) :
    ev tr t r pub x = 0 := by
  rcases ev_mul_eq_zero (ev_of_eval h) with h1 | h1
  · omega
  · exact h1

/-- `1 - x = 0` gives `x = 1`. -/
theorem one_sub {x : Expr} {t r : Nat} (h : ev tr t r pub (1 - x) = 0) : ev tr t r pub x = 1 := by
  have := ev_sub_eq h
  change ev tr t r pub (.const 1) = _ at this
  rw [ev_const] at this
  omega

/-- A boolean constraint `x (x − 1) = 0`. -/
theorem bool_le {x : Expr} {t r : Nat} (h : (bool x).eval tr t r pub = 0) : ev tr t r pub x ≤ 1 := by
  rcases ev_mul_eq_zero (ev_of_eval h) with h1 | h1
  · omega
  · have := ev_sub_eq h1
    change _ = ev tr t r pub (.const 1) at this
    rw [ev_const] at this
    omega

/-! ## Table indices of `finalAirS` -/

theorem tab1 : finalAirS.tables[1]'(by decide) = S384.table := rfl
theorem tab2 : finalAirS.tables[2]'(by decide) = Rng.table := rfl
theorem tab3 : finalAirS.tables[3]'(by decide) = Stmt.table := rfl
theorem tab4 : finalAirS.tables[4]'(by decide) = Fin.table := rfl

/-! ## Who sends / receives the buses of the byte chain -/

theorem only_HB_send : onlyIn finalAirS B_HB true [3] = true := by decide +kernel
theorem only_SB_recv : onlyIn finalAirS B_SB false [1] = true := by decide +kernel
theorem only_R8_send : onlyIn finalAirS B_R8 true [2] = true := by decide +kernel
theorem only_S2_send : onlyIn finalAirS B_S2 true [2] = true := by decide +kernel
theorem only_S5_send : onlyIn finalAirS B_S5 true [2] = true := by decide +kernel

end FinalM5d.Whole
