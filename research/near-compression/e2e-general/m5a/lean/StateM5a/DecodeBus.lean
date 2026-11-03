import StateM5a.Bus
import StateM5a.Air

/-!
# StateM5a.DecodeBus — a bus's message list, table by table (generic, then `DOWN` / `UP` of M5a)

`Bus.busList A tr pub b s` is the list of messages on bus `b` (side `s`) over all tables.  This
file splits it per table and per interaction:

* `rowBusList_filter`: only the interactions on `(b, s)` contribute;
* `rowBusList_one`: an interaction with one multiplicity bit `m` contributes its message once when
  `m = 1` and nothing when `m = 0`;
* `tableBusList_nil`: a table without an interaction on `(b, s)` contributes nothing;
* `busList_append`: the tables the prover adds after the Lean AIR (`m5aAir D`) contribute nothing to
  a bus none of them uses.

Decoding is then a plain `List.map`: `Bus.holds_perm` gives a permutation of field messages and
`List.Perm.map dec` a permutation of decoded records, for *any* decoder `dec` (no injectivity is
needed in this direction).  The decoded records are what `Traffic` consumes.
-/

namespace StateM5a.DecodeBus

open ZkFormal.Air StateM5a.Bus

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

/-- Only the interactions on `(b, s)` contribute to a row's list. -/
theorem rowBusList_filter (is : List Interaction) (tr : Trace F) (t r : Nat) (pub : List F) (b : Nat)
    (s : Bool) : rowBusList is tr t r pub b s =
      rowBusList (is.filter fun i => decide (i.bus = b ∧ i.send = s)) tr t r pub b s := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [rowBusList, List.flatMap_cons] at ih ⊢
    rw [ih, List.filter_cons]
    by_cases h : i.bus = b ∧ i.send = s
    · simp [h]
    · simp only [h, ↓reduceIte, decide_false, Bool.false_eq_true, List.nil_append]

theorem rowBusList_nil (is : List Interaction) (tr : Trace F) (t r : Nat) (pub : List F) (b : Nat)
    (s : Bool) (h : ∀ i ∈ is, ¬ (i.bus = b ∧ i.send = s)) : rowBusList is tr t r pub b s = [] := by
  rw [rowBusList_filter, List.filter_eq_nil_iff.2 (fun i hi => by simpa using h i hi)]
  rfl

theorem tableBusList_nil (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F) (b : Nat)
    (s : Bool) (h : ∀ i ∈ is, ¬ (i.bus = b ∧ i.send = s)) : tableBusList is tr t pub b s = [] := by
  simp only [tableBusList, rowBusList_nil is tr t _ pub b s h]
  induction List.range (tr.height t) with
  | nil => rfl
  | cons _ _ ih => rw [List.flatMap_cons, ih]; rfl

/-- An interaction with a single multiplicity bit. -/
theorem multNat_one (bus : Nat) (m : Expr) (msg : List Expr) (send : Bool) (tr : Trace F) (t r : Nat)
    (pub : List F) : ({ bus, mult := [m], msg, send } : Interaction).multNat tr t r pub =
      if m.eval tr t r pub = 1 then 1 else 0 := by
  simp only [Interaction.multNat, Interaction.multNat.go]
  split <;> rfl

/-- **One interaction on `(b, s)` with one multiplicity bit**: a row sends its message once when
the bit is `1`. -/
theorem rowBusList_one (is : List Interaction) (m : Expr) (msg : List Expr) (tr : Trace F)
    (t r : Nat) (pub : List F) (b : Nat) (s : Bool)
    (h : is.filter (fun i => decide (i.bus = b ∧ i.send = s)) = [{ bus := b, mult := [m], msg, send := s }]) :
    rowBusList is tr t r pub b s =
      if m.eval tr t r pub = 1 then [msg.map fun e => e.eval tr t r pub] else [] := by
  rw [rowBusList_filter, h]
  simp only [rowBusList, List.flatMap_cons, List.flatMap_nil, List.append_nil, and_self, ↓reduceIte,
    multNat_one, Interaction.msgVal]
  split <;> rfl

theorem tableBusList_one (is : List Interaction) (m : Expr) (msg : List Expr) (tr : Trace F)
    (t : Nat) (pub : List F) (b : Nat) (s : Bool)
    (h : is.filter (fun i => decide (i.bus = b ∧ i.send = s)) = [{ bus := b, mult := [m], msg, send := s }]) :
    tableBusList is tr t pub b s =
      (List.range (tr.height t)).filterMap fun r =>
        if m.eval tr t r pub = 1 then some (msg.map fun e => e.eval tr t r pub) else none := by
  simp only [tableBusList]
  induction List.range (tr.height t) with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons, ih, rowBusList_one is m msg tr t r pub b s h, List.filterMap_cons]
    split <;> rfl

/-- **Two interactions on `(b, s)`, one bit each** (the `WSB` INTAKE and FINAL roots). -/
theorem rowBusList_two (is : List Interaction) (m₁ m₂ : Expr) (msg₁ msg₂ : List Expr) (tr : Trace F)
    (t r : Nat) (pub : List F) (b : Nat) (s : Bool)
    (h : is.filter (fun i => decide (i.bus = b ∧ i.send = s)) =
      [{ bus := b, mult := [m₁], msg := msg₁, send := s }, { bus := b, mult := [m₂], msg := msg₂, send := s }]) :
    rowBusList is tr t r pub b s =
      (if m₁.eval tr t r pub = 1 then [msg₁.map fun e => e.eval tr t r pub] else []) ++
      (if m₂.eval tr t r pub = 1 then [msg₂.map fun e => e.eval tr t r pub] else []) := by
  rw [rowBusList_filter, h]
  simp only [rowBusList, List.flatMap_cons, List.flatMap_nil, List.append_nil, and_self, ↓reduceIte,
    multNat_one, Interaction.msgVal]
  split <;> split <;> rfl

/-! ## Tables appended after the Lean AIR -/

theorem busList_go_nil (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) :
    ∀ (Ts : List Table) (t : Nat), (∀ T ∈ Ts, ∀ i ∈ T.interactions, ¬ (i.bus = b ∧ i.send = s)) →
      busList.go tr pub b s Ts t = []
  | [], _, _ => rfl
  | T :: Ts, t, h => by
    simp only [busList.go]
    rw [tableBusList_nil _ tr t pub b s (h T (List.mem_cons_self ..)),
      busList_go_nil tr pub b s Ts (t + 1) (fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))]
    rfl

theorem busList_go_append (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) :
    ∀ (Ts Us : List Table) (t : Nat),
      busList.go tr pub b s (Ts ++ Us) t = busList.go tr pub b s Ts t ++ busList.go tr pub b s Us (t + Ts.length)
  | [], Us, t => by simp [busList.go]
  | T :: Ts, Us, t => by
    simp only [List.cons_append, busList.go, List.append_assoc, List.length_cons]
    rw [busList_go_append tr pub b s Ts Us (t + 1), show t + 1 + Ts.length = t + (Ts.length + 1) by omega]

/-- **Extra tables that do not use `(b, s)` do not change the bus list.** -/
theorem busList_extend (A : Air) (extra : List Table) (nb np : Nat) (tr : Trace F) (pub : List F)
    (b : Nat) (s : Bool) (h : ∀ T ∈ extra, ∀ i ∈ T.interactions, ¬ (i.bus = b ∧ i.send = s)) :
    busList { tables := A.tables ++ extra, numBuses := nb, numPub := np } tr pub b s = busList A tr pub b s := by
  simp only [busList]
  rw [busList_go_append, busList_go_nil tr pub b s extra _ h, List.append_nil]

end

end StateM5a.DecodeBus
