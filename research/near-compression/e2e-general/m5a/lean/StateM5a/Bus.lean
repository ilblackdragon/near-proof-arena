import ZkFormal.Air.Basic

/-!
# StateM5a.Bus — bus balance as a permutation of message lists (the LogUp predicate, list form)

`ZkFormal.Air.Holds` states bus balance as count equality: for every bus `b` and message `m`,
`busCount A tr pub b true m = busCount A tr pub b false m` (natural multiplicities, no
wrap-around; the IOP's grand-product / LogUp argument enforces exactly this).  This file turns
that into a statement about *lists*: `busList A tr pub b s` is the list of messages sent
(`s = true`) or received on bus `b`, each repeated by its multiplicity, and

* `count_busList`: its count of `m` is `busCount … m`;
* `holds_perm`: `Holds A pub tr → (busList … b true).Perm (busList … b false)`;
* `perm_of_map_inj`: a permutation of encodings under an injective encoding is a permutation of
  the decoded messages, so the record-level traffic (`StateM5a.Traffic`) inherits balance from
  the field-level one once every message on the bus is the encoding of a decoded message.

Nothing here is specific to M5a.
-/

namespace StateM5a.Bus

open ZkFormal.Air

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

/-- Messages of interactions `is` on bus `b`, side `s`, row `r` (repeated by multiplicity). -/
def rowBusList (is : List Interaction) (tr : Trace F) (t r : Nat) (pub : List F) (b : Nat)
    (s : Bool) : List (List F) :=
  is.flatMap fun i =>
    if i.bus = b ∧ i.send = s then List.replicate (i.multNat tr t r pub) (i.msgVal tr t r pub) else []

/-- Messages of table `t` on bus `b`, side `s`, all rows. -/
def tableBusList (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F) (b : Nat)
    (s : Bool) : List (List F) :=
  (List.range (tr.height t)).flatMap fun r => rowBusList is tr t r pub b s

/-- Messages of all tables on bus `b`, side `s`. -/
def busList (A : Air) (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) : List (List F) :=
  go A.tables 0
where
  go : List Table → Nat → List (List F)
    | [], _ => []
    | T :: Ts, t => tableBusList T.interactions tr t pub b s ++ go Ts (t + 1)

theorem count_rowBusList (is : List Interaction) (tr : Trace F) (t r : Nat) (pub : List F)
    (b : Nat) (s : Bool) (m : List F) (acc : Nat) :
    (rowBusList is tr t r pub b s).count m + acc =
      is.foldr (fun i acc' =>
        (if i.bus = b ∧ i.send = s ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub else 0)
          + acc') acc := by
  induction is with
  | nil => simp [rowBusList]
  | cons i is ih =>
    simp only [rowBusList, List.flatMap_cons, List.count_append, List.foldr_cons] at ih ⊢
    rw [← ih]
    by_cases h1 : i.bus = b <;> by_cases h2 : i.send = s <;>
      by_cases h3 : i.msgVal tr t r pub = m <;> simp [h1, h2, h3, List.count_replicate] <;> omega

theorem count_tableBusList (is : List Interaction) (tr : Trace F) (t : Nat) (pub : List F)
    (b : Nat) (s : Bool) (m : List F) :
    (tableBusList is tr t pub b s).count m = tableBusCount is tr t pub b s m := by
  simp only [tableBusList, tableBusCount]
  induction List.range (tr.height t) with
  | nil => simp
  | cons r rs ih =>
    rw [List.flatMap_cons, List.count_append, List.foldr_cons, ih]
    exact count_rowBusList is tr t r pub b s m _

theorem count_busList (A : Air) (tr : Trace F) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    (busList A tr pub b s).count m = busCount A tr pub b s m := by
  simp only [busList, busCount]
  generalize 0 = t
  induction A.tables generalizing t with
  | nil => rfl
  | cons T Ts ih =>
    simp only [busList.go, busCount.go, List.count_append, count_tableBusList, ih]

/-- **Bus balance as a permutation**: in a trace satisfying the AIR, on every bus the sent
messages are a permutation of the received ones (with multiplicities). -/
theorem holds_perm {A : Air} {pub : List F} {tr : Trace F} (h : Holds A pub tr) (b : Nat) :
    (busList A tr pub b true).Perm (busList A tr pub b false) := by
  rw [List.perm_iff_count]
  intro m
  rw [count_busList, count_busList]
  exact h.balance b m

end

/-! ## Decoding -/

theorem count_map_inj {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (a : α) :
    ∀ l : List α, (l.map f).count (f a) = l.count a
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.count_cons, count_map_inj f hf a xs]
    by_cases h : x = a
    · subst h; simp
    · have : f x ≠ f a := fun e => h (hf _ _ e)
      simp [h, this]

/-- A permutation of encodings under an injective encoding is a permutation of the decoded
messages. -/
theorem perm_of_map_inj {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) {l₁ l₂ : List α} (h : (l₁.map f).Perm (l₂.map f)) :
    l₁.Perm l₂ := by
  rw [List.perm_iff_count] at h ⊢
  intro a
  rw [← count_map_inj f hf a l₁, ← count_map_inj f hf a l₂]
  exact h (f a)

/-- The same, for lists that *are* encodings (every field message on the bus decodes). -/
theorem perm_decode {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) {l₁ l₂ : List β} {L₁ L₂ : List α} (e₁ : l₁ = L₁.map f)
    (e₂ : l₂ = L₂.map f) (h : l₁.Perm l₂) : L₁.Perm L₂ := by
  subst e₁ e₂; exact perm_of_map_inj f hf h

end StateM5a.Bus
