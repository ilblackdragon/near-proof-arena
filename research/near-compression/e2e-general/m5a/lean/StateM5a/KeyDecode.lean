import StateM5a.DecodeM5a
import StateM5a.KeyField

/-!
# StateM5a.KeyDecode — the `KEY` table as a function `keyOf`, and the `NIB` / `KLEN` lookups

The `KEY` table (table 1) holds one row per key byte: the active rows form a prefix, the first
row starts key `kid = 0` at byte `j = 0`, and each transition either continues the key
(`last = 0`: `kid' = kid`, `j' = j + 1`) or starts the next one (`last = 1`: `kid' = kid + 1`,
`j' = 0`).  From the constraints over BabyBear (heights `≤ 2^20`, so no value wraps):

* **`key_inv`**: on an active row `r`, `kid ≤ r`, `j ≤ r`, every earlier active row has a
  smaller-or-equal `kid`, and exactly `j` earlier active rows share this row's `kid`.
* **`keyRows tr K`** (the active rows with `kid = K`, in row order), **`keyBytes tr K`** (their
  bytes `16·hi + lo`) and **`keyOf tr K`** (their nibbles `hi, lo`): functions of the trace,
  `keyOf_eq_nibbles` — `keyOf tr K = NearSpec.nibbles (keyBytes tr K)`.  An active row is the
  `j`-th row of its key (`keyRows_get`), and a `last` row closes it (`keyRows_length`).

Bus level (`Bus.holds_perm`, for the AIR the prover runs, `fullAir D extra`, with `extra` tables
that send nothing on `NIB` / `KLEN`): only `KEY` sends on `NIB` and `KLEN` (`sender_m5a`,
`decide` per table), so

* **`nib_recv`**: every message received on `NIB` (by any table) is `[x, i, n]` with
  `(keyOf tr x)[i]? = some n` (as naturals) and `i < 2^21`;
* **`klen_recv`**: every message received on `KLEN` is `[x, l]` with `(keyOf tr x).length = l`;
* **`nib_of_rcv` / `klen_of_rcv`**: the row form — a row `r` of table `t < 12` whose one-bit
  receive `rcv B_NIB g [e₀, e₁, e₂]` fires (`g = 1`) has
  `(keyOf tr (ev e₀))[ev e₁]? = some (ev e₂) ∧ ev e₁ < 2^21`; instances for the `BR`, `SN`,
  `SNC` and `KCMP` lookups follow (`br_nib`, `sn_nib`, …).

Multiplicities: `KEY` provides with 4 bits (`sndBits`), receivers with one bit (`rcv`); the
statement needs only membership (a received message is sent by someone), not the counts.
-/

namespace StateM5a.KeyDecode

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.FieldRows
open StateM5a.DecodeM5a

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Bus membership (generic) -/

/-- Does an interaction list send on bus `b`? -/
def sendsOn (is : List Interaction) (b : Nat) : Bool := is.any fun i => i.bus == b && i.send

/-- Decidable membership of an interaction (the derived `BEq` is not lawful). -/
def memD (x : Interaction) (l : List Interaction) : Bool := l.any fun y => decide (y = x)

theorem memD_mem {x : Interaction} {l : List Interaction} (h : memD x l = true) : x ∈ l := by
  obtain ⟨y, hy, e⟩ := List.any_eq_true.1 h
  rw [← of_decide_eq_true e]; exact hy

theorem not_sends {is : List Interaction} {b : Nat} (h : sendsOn is b = false) {i : Interaction}
    (hi : i ∈ is) (hb : i.bus = b) (hs : i.send = true) : False := by
  have := List.any_eq_false.1 h i hi
  simp [hb, hs] at this

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

theorem multNat_go_pos {tr : Trace F} {t r : Nat} {pub : List F} : ∀ (bs : List Expr) (k : Nat),
    0 < Interaction.multNat.go tr t r pub bs k → ∃ b ∈ bs, b.eval tr t r pub = 1
  | [], _, h => by simp [Interaction.multNat.go] at h
  | b :: bs, k, h => by
    simp only [Interaction.multNat.go] at h
    by_cases hb : b.eval tr t r pub = 1
    · exact ⟨b, List.mem_cons_self .., hb⟩
    · simp only [hb, ↓reduceIte, Nat.zero_add] at h
      obtain ⟨b', hb', e⟩ := multNat_go_pos bs (k + 1) h
      exact ⟨b', List.mem_cons_of_mem _ hb', e⟩

theorem multNat_pos {tr : Trace F} {t r : Nat} {pub : List F} (i : Interaction)
    (h : 0 < i.multNat tr t r pub) : ∃ b ∈ i.mult, b.eval tr t r pub = 1 :=
  multNat_go_pos i.mult 0 h

theorem multNat_one_pos {tr : Trace F} {t r : Nat} {pub : List F} (i : Interaction) {g : Expr}
    (hm : i.mult = [g]) (hg : g.eval tr t r pub = 1) : 0 < i.multNat tr t r pub := by
  simp [Interaction.multNat, hm, Interaction.multNat.go, hg]

theorem mem_rowBusList {is : List Interaction} {tr : Trace F} {t r : Nat} {pub : List F} {b : Nat}
    {s : Bool} {m : List F} : m ∈ rowBusList is tr t r pub b s ↔
      ∃ i ∈ is, i.bus = b ∧ i.send = s ∧ 0 < i.multNat tr t r pub ∧ m = i.msgVal tr t r pub := by
  simp only [rowBusList, List.mem_flatMap]
  constructor
  · rintro ⟨i, hi, hm⟩
    split at hm
    · rename_i h
      obtain ⟨hp, rfl⟩ := List.mem_replicate.1 hm
      exact ⟨i, hi, h.1, h.2, by omega, rfl⟩
    · simp at hm
  · rintro ⟨i, hi, hb, hs, hp, rfl⟩
    exact ⟨i, hi, by rw [if_pos ⟨hb, hs⟩]; exact List.mem_replicate.2 ⟨by omega, rfl⟩⟩

theorem mem_tableBusList {is : List Interaction} {tr : Trace F} {t : Nat} {pub : List F} {b : Nat}
    {s : Bool} {m : List F} : m ∈ tableBusList is tr t pub b s ↔
      ∃ r, r < tr.height t ∧ m ∈ rowBusList is tr t r pub b s := by
  simp only [tableBusList, List.mem_flatMap, List.mem_range]

theorem mem_busList_go {tr : Trace F} {pub : List F} {b : Nat} {s : Bool} {m : List F} :
    ∀ (Ts : List Table) (t0 : Nat), m ∈ busList.go tr pub b s Ts t0 ↔
      ∃ k, ∃ hk : k < Ts.length, m ∈ tableBusList Ts[k].interactions tr (t0 + k) pub b s
  | [], t0 => by simp [busList.go]
  | T :: Ts, t0 => by
    simp only [busList.go, List.mem_append, mem_busList_go Ts (t0 + 1)]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨0, by simp, by simpa using h⟩
      · refine ⟨k + 1, by simp; omega, ?_⟩
        rw [show t0 + (k + 1) = t0 + 1 + k by omega]
        simpa using h
    · rintro ⟨k, hk, h⟩
      cases k with
      | zero => left; simpa using h
      | succ k =>
        right
        refine ⟨k, by simp at hk; omega, ?_⟩
        rw [show t0 + 1 + k = t0 + (k + 1) by omega]
        simpa using h

/-- **A message on a bus is some row's interaction message with a positive multiplicity.** -/
theorem mem_busList {A : Air} {tr : Trace F} {pub : List F} {b : Nat} {s : Bool} {m : List F} :
    m ∈ busList A tr pub b s ↔ ∃ t, ∃ ht : t < A.tables.length, ∃ r, r < tr.height t ∧
      ∃ i ∈ A.tables[t].interactions, i.bus = b ∧ i.send = s ∧ 0 < i.multNat tr t r pub ∧
        m = i.msgVal tr t r pub := by
  unfold busList
  rw [mem_busList_go]
  simp only [Nat.zero_add, mem_tableBusList, mem_rowBusList]

/-- A one-bit interaction that fires puts its message on the bus. -/
theorem msg_mem_busList {A : Air} {tr : Trace F} {pub : List F} {t : Nat} (ht : t < A.tables.length)
    {i : Interaction} (hi : i ∈ A.tables[t].interactions) {r : Nat} (hr : r < tr.height t) {g : Expr}
    (hm : i.mult = [g]) (hg : g.eval tr t r pub = 1) :
    i.msgVal tr t r pub ∈ busList A tr pub i.bus i.send :=
  mem_busList.2 ⟨t, ht, r, hr, i, hi, rfl, rfl, multNat_one_pos i hm hg, rfl⟩

end

/-! ## The AIR the prover runs: who sends on a bus -/

section
variable {tr : Trace Fp} {pub : List Fp}

theorem fullAir_get {D : Nat} {extra : List Table} {nb np t : Nat} (ht : t < (m5aAir D).tables.length)
    (ht' : t < (fullAir D extra nb np).tables.length) :
    (fullAir D extra nb np).tables[t] = (m5aAir D).tables[t] := by
  simp only [fullAir]
  exact List.getElem_append_left ht

theorem fullAir_len (D : Nat) (extra : List Table) (nb np : Nat) :
    (fullAir D extra nb np).tables.length = 12 + extra.length := by
  simp [fullAir, m5aAir]; omega

/-- **Single sender.**  If table `t0` is the only table of the Lean AIR sending on `b` and the
extra tables do not send on `b`, every message sent on `b` is a row message of table `t0`. -/
theorem sender_m5a {D : Nat} {extra : List Table} {nb np : Nat} (b t0 : Nat)
    (ht0 : t0 < (m5aAir D).tables.length)
    (hS : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ t0 →
      sendsOn ((m5aAir D).tables[t]).interactions b = false)
    (hx : ∀ T ∈ extra, sendsOn T.interactions b = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub b true) :
    ∃ r, r < tr.height t0 ∧ ∃ i ∈ ((m5aAir D).tables[t0]).interactions, i.bus = b ∧ i.send = true ∧
      0 < i.multNat tr t0 r pub ∧ m = i.msgVal tr t0 r pub := by
  obtain ⟨t, ht, r, hr, i, hi, hb, hs, hp, rfl⟩ := mem_busList.1 hm
  by_cases hlt : t < (m5aAir D).tables.length
  · rw [fullAir_get hlt ht] at hi
    by_cases e : t = t0
    · subst e; exact ⟨r, hr, i, hi, hb, hs, hp, rfl⟩
    · exact (not_sends (hS t hlt e) hi hb hs).elim
  · have hmem : (fullAir D extra nb np).tables[t] ∈ extra := by
      simp only [fullAir]
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem ..
    exact (not_sends (hx _ hmem) hi hb hs).elim

/-- Messages received on `b` are sent on `b` (bus balance). -/
theorem recv_sent {A : Air} (hH : Holds A pub tr) {b : Nat} {m : List Fp}
    (hm : m ∈ busList A tr pub b false) : m ∈ busList A tr pub b true :=
  (holds_perm hH b).mem_iff.2 hm

end

/-! ## The `KEY` layout -/

section Layout
variable {tr : Trace Fp} {pub : List Fp}

/-- Column `s` of `KEY` row `r` (table 1), as a natural. -/
abbrev kc (tr : Trace Fp) (r : Nat) (s : String) (j : Nat := 0) : Nat := KeyField.cv tr 1 r s j

theorem ev_kc (r : Nat) (s : String) (j : Nat := 0) : ev tr 1 r pub (Key.c s j) = kc tr r s j := rfl

theorem m_first_kid : Expr.isFirst * Key.c "kid" ∈ Key.constraints := by unfold Key.constraints; simp
theorem m_first_j : Expr.isFirst * Key.c "j" ∈ Key.constraints := by unfold Key.constraints; simp
theorem m_first_act : Expr.isFirst * (Key.c "act" - 1) ∈ Key.constraints := by unfold Key.constraints; simp
theorem m_tr_act : Expr.isTransition * Key.nx "act" * (1 - Key.c "act") ∈ Key.constraints := by
  unfold Key.constraints; simp
theorem m_tr_kid : Expr.isTransition * Key.nx "act" * (Key.nx "kid" - Key.c "kid" - Key.c "last") ∈
    Key.constraints := by unfold Key.constraints; simp
theorem m_tr_j : Expr.isTransition * Key.nx "act" *
    (Key.nx "j" - Key.c "j" - 1 + Key.c "last" * (Key.c "j" + 1)) ∈ Key.constraints := by
  unfold Key.constraints; simp
theorem m_bool_act : bool (Key.c "act") ∈ Key.constraints := by unfold Key.constraints; simp
theorem m_bool_last : bool (Key.c "last") ∈ Key.constraints := by unfold Key.constraints; simp
theorem m_last_act : (1 - Key.c "act") * Key.c "last" ∈ Key.constraints := by unfold Key.constraints; simp
theorem m_mh (k : Nat) (hk : k < 4) : (1 - Key.c "act") * Key.c "mh" k ∈ Key.constraints := by
  unfold Key.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨k, hk, by simp⟩
theorem m_ml (k : Nat) (hk : k < 4) : (1 - Key.c "act") * Key.c "ml" k ∈ Key.constraints := by
  unfold Key.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨k, hk, by simp⟩
theorem m_mlen (k : Nat) (hk : k < 4) : (1 - Key.c "last") * Key.c "mlen" k ∈ Key.constraints := by
  unfold Key.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨k, hk, by simp⟩
theorem m_mdig (k : Nat) (hk : k < 4) : (1 - Key.c "last") * Key.c "mdig" k ∈ Key.constraints := by
  unfold Key.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨k, hk, by simp⟩

theorem ev_gate {g x : Expr} {t r : Nat} (hg : ev tr t r pub g = 1) (h : ev tr t r pub (g * x) = 0) :
    ev tr t r pub x = 0 := FieldWsb.wsb_gate hg h

theorem ev_one_minus {x : Expr} {t r : Nat} (h : ev tr t r pub (1 - x) = 0) : ev tr t r pub x = 1 := by
  have hx := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) x
  rw [ev_sub, ev_one] at h
  omega

/-- A flag gate `(1 − g)·x` with `x = 1` forces `g = 1`. -/
theorem gate_of_one {g x : Expr} {t r : Nat} (h : ev tr t r pub ((1 - g) * x) = 0)
    (hx : ev tr t r pub x = 1) : ev tr t r pub g = 1 := by
  rw [ev_hmul, hx, Nat.mul_one, Nat.mod_eq_of_lt (ev_lt _)] at h
  exact ev_one_minus h

theorem sub_val {a b : Expr} {t r v : Nat} (h : ev tr t r pub (a - b) = v) :
    ev tr t r pub a = (ev tr t r pub b + v) % P := by
  rw [ev_sub] at h
  have ha := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) a
  have hb := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) b
  omega

theorem add_zero_val {a b : Expr} {t r : Nat} (h : ev tr t r pub (a + b) = 0) :
    ev tr t r pub a = (P - ev tr t r pub b) % P := by
  rw [ev_hadd] at h
  have ha := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) a
  have hb := ev_lt (tr := tr) (t := t) (r := r) (pub := pub) b
  omega

theorem arith_j (j : Nat) (hj : j < P) : (j + (1 + (P - (j + 1) % P) % P) % P) % P = 0 := by omega

variable (hc : ∀ r, r < tr.height 1 → ∀ e ∈ Key.table.constraints, e.eval tr 1 r pub = 0)
include hc

theorem key_h {r : Nat} (hr : r < tr.height 1) {e : Expr} (he : e ∈ Key.constraints) :
    ev tr 1 r pub e = 0 := hold rfl (hc r hr) he

theorem key_bool {r : Nat} (hr : r < tr.height 1) {s : String} (hs : bool (Key.c s) ∈ Key.constraints) :
    kc tr r s = 0 ∨ kc tr r s = 1 :=
  FieldRows2.ev_bool (key_h hc hr hs)

theorem key_first : kc tr 0 "kid" = 0 ∧ kc tr 0 "j" = 0 ∧ kc tr 0 "act" = 1 := by
  have h0 : 0 < tr.height 1 := Nat.two_pow_pos _
  have g : ev tr 1 0 pub .isFirst = 1 := by rw [FieldWsb.ev_isFirst]; rfl
  refine ⟨ev_gate g (key_h hc h0 m_first_kid), ev_gate g (key_h hc h0 m_first_j), ?_⟩
  have := ev_gate g (key_h hc h0 m_first_act)
  have hx := ev_lt (tr := tr) (t := 1) (r := 0) (pub := pub) (Key.c "act")
  rw [ev_sub, ev_one] at this
  change ev tr 1 0 pub (Key.c "act") = 1
  omega

/-- One transition into an active row. -/
theorem key_step {r : Nat} (hr : r + 1 < tr.height 1) (ha : kc tr (r + 1) "act" = 1) :
    kc tr r "act" = 1 ∧ kc tr (r + 1) "kid" = (kc tr r "kid" + kc tr r "last") % P ∧
      (kc tr r "last" = 0 → kc tr (r + 1) "j" = (kc tr r "j" + 1) % P) ∧
      (kc tr r "last" = 1 → kc tr (r + 1) "j" = 0) := by
  have hr' : r < tr.height 1 := by omega
  have gT : ev tr 1 r pub .isTransition = 1 := by
    rw [FieldWsb.ev_isTransition]; split
    · omega
    · rfl
  have nx : ∀ s, ev tr 1 r pub (Key.nx s) = kc tr (r + 1) s := fun s => FieldWsb.ev_next r _ hr
  have gA : ev tr 1 r pub (Key.nx "act") = 1 := (nx "act").trans ha
  have g : ev tr 1 r pub (Expr.isTransition * Key.nx "act") = 1 := by
    rw [ev_hmul, gT, gA]
  have e1 := ev_gate g (key_h hc hr' m_tr_act)
  have e2 := sub_val (eq_of_sub (ev_gate g (key_h hc hr' m_tr_kid)))
  have e3 := add_zero_val (ev_gate g (key_h hc hr' m_tr_j))
  rw [nx, ev_kc, ev_kc] at e2
  refine ⟨ev_one_minus e1, e2, fun h0 => ?_, fun h1 => ?_⟩
  · rw [ev_hmul, ev_kc, h0, Nat.zero_mul, Nat.zero_mod, Nat.sub_zero, Nat.mod_self] at e3
    have e4 := sub_val (eq_of_sub e3)
    rw [nx, ev_kc, ev_one] at e4
    exact e4
  · have hj := ev_lt (tr := tr) (t := 1) (r := r) (pub := pub) (Key.c "j")
    rw [ev_hmul, ev_kc, h1, Nat.one_mul, ev_hadd, ev_one, ev_kc, Nat.mod_mod] at e3
    have e4 := sub_val e3
    have e5 := sub_val e4
    rw [nx, ev_kc] at e5
    rw [ev_one] at e5
    rw [ev_kc] at hj
    rw [e5]; exact arith_j _ hj

/-- Active rows form a prefix. -/
theorem key_act_prefix : ∀ {r r' : Nat}, r < tr.height 1 → r' ≤ r → kc tr r "act" = 1 → kc tr r' "act" = 1
  | 0, r', _, h, ha => by rw [Nat.le_zero.1 h]; exact ha
  | r + 1, r', hr, h, ha => by
    rcases Nat.lt_or_ge r' (r + 1) with h' | h'
    · exact key_act_prefix (by omega) (by omega) (key_step hc hr ha).1
    · rw [show r' = r + 1 by omega]; exact ha

/-- The rows of key `K` before row `r`. -/
def before (tr : Trace Fp) (K r : Nat) : List Nat :=
  (List.range r).filter fun r' => decide (kc tr r' "act" = 1 ∧ kc tr r' "kid" = K)

/-- **The `KEY` invariant.** -/
theorem key_inv (hlog : tr.log 1 ≤ 20) : ∀ r, r < tr.height 1 → kc tr r "act" = 1 →
    kc tr r "kid" ≤ r ∧ kc tr r "j" ≤ r ∧
      (∀ r', r' ≤ r → kc tr r' "act" = 1 → kc tr r' "kid" ≤ kc tr r "kid") ∧
      (before tr (kc tr r "kid") r).length = kc tr r "j" := by
  have hH : tr.height 1 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  intro r
  induction r with
  | zero =>
    intro _ _
    obtain ⟨h1, h2, -⟩ := key_first hc
    refine ⟨by omega, by omega, fun r' h _ => ?_, by simp [before, h2]⟩
    rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ r ih =>
    intro hr ha
    obtain ⟨har, hkid, hj0, hj1⟩ := key_step hc hr ha
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega) har
    have hb : before tr (kc tr (r + 1) "kid") (r + 1) =
        before tr (kc tr (r + 1) "kid") r ++
          (if kc tr r "act" = 1 ∧ kc tr r "kid" = kc tr (r + 1) "kid" then [r] else []) := by
      simp only [before, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
      by_cases h : kc tr r "act" = 1 ∧ kc tr r "kid" = kc tr (r + 1) "kid"
      · rw [if_pos (decide_eq_true h), if_pos h]
      · rw [if_neg (by simpa using h), if_neg h]
    rcases key_bool hc (by omega : r < tr.height 1) m_bool_last with hl | hl
    · simp only [hl, Nat.add_zero] at hkid
      rw [Nat.mod_eq_of_lt (by omega)] at hkid
      have hj := hj0 hl
      rw [Nat.mod_eq_of_lt (by omega)] at hj
      refine ⟨by omega, by omega, fun r' h hr' => ?_, ?_⟩
      · rcases Nat.lt_or_ge r' (r + 1) with h' | h'
        · rw [hkid]; exact i3 r' (by omega) hr'
        · rw [show r' = r + 1 by omega]; exact Nat.le_refl _
      · rw [hb, hkid, if_pos ⟨har, rfl⟩, List.length_append, i4, hj]; rfl
    · rw [hl, Nat.mod_eq_of_lt (by omega)] at hkid
      have hj := hj1 hl
      refine ⟨by omega, by omega, fun r' h hr' => ?_, ?_⟩
      · rcases Nat.lt_or_ge r' (r + 1) with h' | h'
        · have := i3 r' (by omega) hr'; omega
        · rw [show r' = r + 1 by omega]; exact Nat.le_refl _
      · rw [hj, List.length_eq_zero_iff]
        unfold before
        rw [List.filter_eq_nil_iff]
        intro r' hr'
        have hr'' := List.mem_range.1 hr'
        simp only [decide_eq_true_eq, not_and]
        intro hact
        have := i3 r' (by omega) hact
        omega

end Layout

/-! ## Keys as functions of the trace -/

/-- The active `KEY` rows of key `K`, in row order. -/
def keyRows (tr : Trace Fp) (K : Nat) : List Nat :=
  (List.range (tr.height 1)).filter fun r => decide (kc tr r "act" = 1 ∧ kc tr r "kid" = K)

/-- The nibbles of key `K` (each row's `hi`, `lo`). -/
def keyOf (tr : Trace Fp) (K : Nat) : List Nat :=
  (keyRows tr K).flatMap fun r => [kc tr r "hi", kc tr r "lo"]

/-- The bytes of key `K` (the bytes the rows hash: `16·hi + lo`). -/
def keyBytes (tr : Trace Fp) (K : Nat) : List UInt8 :=
  (keyRows tr K).map fun r => UInt8.ofNat (16 * kc tr r "hi" + kc tr r "lo")

theorem flatMap_pair_get {α : Type} (f g : α → Nat) :
    ∀ (l : List α) (i : Nat), (l.flatMap fun x => [f x, g x])[2 * i]? = (l[i]?).map f ∧
      (l.flatMap fun x => [f x, g x])[2 * i + 1]? = (l[i]?).map g
  | [], i => by simp
  | x :: xs, 0 => by simp
  | x :: xs, i + 1 => by
    have := flatMap_pair_get f g xs i
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, show 2 * i + 1 + 1 + 1 = (2 * i + 1) + 1 + 1 by omega]
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem?_cons_succ]
    exact this

theorem flatMap_pair_len {α : Type} (f g : α → Nat) (l : List α) :
    (l.flatMap fun x => [f x, g x]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]; omega

section Keys
variable {tr : Trace Fp} {pub : List Fp}
  (hc : ∀ r, r < tr.height 1 → ∀ e ∈ Key.table.constraints, e.eval tr 1 r pub = 0)
include hc

theorem keyRows_split {r : Nat} (hr : r < tr.height 1) (K : Nat) :
    keyRows tr K = before tr K r ++ (if kc tr r "act" = 1 ∧ kc tr r "kid" = K then [r] else []) ++
      ((List.range (tr.height 1 - (r + 1))).map (r + 1 + ·)).filter
        (fun r => decide (kc tr r "act" = 1 ∧ kc tr r "kid" = K)) := by
  unfold keyRows before
  rw [show tr.height 1 = r + 1 + (tr.height 1 - (r + 1)) by omega, List.range_add, List.range_succ]
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [show r + 1 + (tr.height 1 - (r + 1)) - (r + 1) = tr.height 1 - (r + 1) by omega]
  by_cases h : kc tr r "act" = 1 ∧ kc tr r "kid" = K
  · rw [if_pos (decide_eq_true h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h]

/-- **An active row is the `j`-th row of its key.** -/
theorem keyRows_get (hlog : tr.log 1 ≤ 20) {r : Nat} (hr : r < tr.height 1) (ha : kc tr r "act" = 1) :
    (keyRows tr (kc tr r "kid"))[kc tr r "j"]? = some r := by
  obtain ⟨-, -, -, h4⟩ := key_inv hc hlog r hr ha
  rw [keyRows_split hc hr, if_pos ⟨ha, rfl⟩, List.append_assoc, List.getElem?_append_right (by omega),
    h4, Nat.sub_self]
  rfl

/-- **A `last` row closes its key.** -/
theorem keyRows_length (hlog : tr.log 1 ≤ 20) {r : Nat} (hr : r < tr.height 1) (ha : kc tr r "act" = 1)
    (hl : kc tr r "last" = 1) : (keyRows tr (kc tr r "kid")).length = kc tr r "j" + 1 := by
  have hH : tr.height 1 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  obtain ⟨i1, -, -, h4⟩ := key_inv hc hlog r hr ha
  rw [keyRows_split hc hr, if_pos ⟨ha, rfl⟩]
  have hnil : ((List.range (tr.height 1 - (r + 1))).map (r + 1 + ·)).filter
      (fun r' => decide (kc tr r' "act" = 1 ∧ kc tr r' "kid" = kc tr r "kid")) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r'' hr''
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr''
    have hk' := List.mem_range.1 hk
    simp only [decide_eq_true_eq, not_and]
    intro hact
    have hr2 : r + 1 + k < tr.height 1 := by omega
    obtain ⟨-, -, i3, -⟩ := key_inv hc hlog _ hr2 hact
    have ha1 : kc tr (r + 1) "act" = 1 := key_act_prefix hc hr2 (by omega) hact
    have h1 := i3 (r + 1) (by omega) ha1
    obtain ⟨-, hkid, -, -⟩ := key_step hc (by omega : r + 1 < tr.height 1) ha1
    rw [hl, Nat.mod_eq_of_lt (by omega)] at hkid
    omega
  rw [hnil, List.append_nil, List.length_append, h4]
  rfl

theorem keyRows_lt {K r : Nat} (h : r ∈ keyRows tr K) : r < tr.height 1 :=
  List.mem_range.1 (List.mem_filter.1 h).1

/-- **`keyOf` is `NearSpec.nibbles` of `keyBytes`.** -/
theorem keyOf_eq_nibbles (K : Nat) : keyOf tr K = NearSpec.nibbles (keyBytes tr K) := by
  unfold keyOf keyBytes
  have hrows : ∀ r ∈ keyRows tr K, r < tr.height 1 := fun r h => keyRows_lt hc h
  revert hrows
  induction keyRows tr K with
  | nil => intro _; rfl
  | cons r rs ih =>
    intro hrows
    simp only [List.flatMap_cons, List.map_cons, NearSpec.nibbles]
    rw [ih (fun r' h => hrows r' (List.mem_cons_of_mem _ h))]
    obtain ⟨-, -, -, hn⟩ := KeyField.key_row_nibbles (hc r (hrows r (List.mem_cons_self ..)))
    simp only [NearSpec.nibbles, List.cons.injEq] at hn
    have e1 : (UInt8.ofNat (16 * kc tr r "hi" + kc tr r "lo")).toNat / 16 = kc tr r "hi" := hn.1
    have e2 : (UInt8.ofNat (16 * kc tr r "hi" + kc tr r "lo")).toNat % 16 = kc tr r "lo" := hn.2.1
    rw [e1, e2]
    rfl

/-- **`KEY` row facts**: an active row's nibbles are entries `2j`, `2j+1` of its key; a `last` row
gives the key's length. -/
theorem key_row_get (hlog : tr.log 1 ≤ 20) {r : Nat} (hr : r < tr.height 1) (ha : kc tr r "act" = 1) :
    (keyOf tr (kc tr r "kid"))[2 * kc tr r "j"]? = some (kc tr r "hi") ∧
      (keyOf tr (kc tr r "kid"))[2 * kc tr r "j" + 1]? = some (kc tr r "lo") := by
  have h := keyRows_get hc hlog hr ha
  obtain ⟨e1, e2⟩ := flatMap_pair_get (fun r => kc tr r "hi") (fun r => kc tr r "lo")
    (keyRows tr (kc tr r "kid")) (kc tr r "j")
  unfold keyOf
  rw [e1, e2, h]
  exact ⟨rfl, rfl⟩

theorem key_row_len (hlog : tr.log 1 ≤ 20) {r : Nat} (hr : r < tr.height 1) (ha : kc tr r "act" = 1)
    (hl : kc tr r "last" = 1) : (keyOf tr (kc tr r "kid")).length = 2 * (kc tr r "j" + 1) := by
  unfold keyOf
  rw [flatMap_pair_len, keyRows_length hc hlog hr ha hl]

end Keys

/-! ## `NIB` / `KLEN` from `Holds` -/

/-- Only `KEY` sends on `NIB`, `KLEN`, `KDIG` (per table, `decide`). -/
theorem key_only (D b : Nat) (hb : b = B_NIB ∨ b = B_KLEN ∨ b = B_KDIG) :
    ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 1 → sendsOn ((m5aAir D).tables[t]).interactions b = false
  | 0, _, _ => by show sendsOn shaTable.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 1, _, h => absurd rfl h
  | 2, _, _ => by show sendsOn Br.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 3, _, _ => by show sendsOn Sn.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 4, _, _ => by show sendsOn Kcmp.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 5, _, _ => by show sendsOn Wsb.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 6, _, _ => by show sendsOn Wsn.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 7, _, _ => by show sendsOn Wsa.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 8, _, _ => by show sendsOn Snc.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 9, _, _ => by show sendsOn Rng.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 10, _, _ => by show sendsOn Wsl.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | 11, _, _ => by show sendsOn Wsp.interactions b = false; rcases hb with rfl | rfl | rfl <;> decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

theorem key_nib_iface {i : Interaction} (hi : i ∈ Key.interactions) (hb : i.bus = B_NIB)
    (hs : i.send = true) :
    i = sndBits B_NIB (Key.bits "mh") [Key.c "kid", sm 2 (Key.c "j"), Key.c "hi"] ∨
      i = sndBits B_NIB (Key.bits "ml") [Key.c "kid", sm 2 (Key.c "j") + 1, Key.c "lo"] := by
  simp only [Key.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)
  · exact .inl rfl
  · exact .inr rfl
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)

theorem key_klen_iface {i : Interaction} (hi : i ∈ Key.interactions) (hb : i.bus = B_KLEN)
    (hs : i.send = true) :
    i = sndBits B_KLEN (Key.bits "mlen") [Key.c "kid", sm 2 (Key.c "j" + 1)] := by
  simp only [Key.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)
  · rfl
  · exact absurd hb (by decide)

theorem mem_bits {s : String} {b : Expr} (h : b ∈ Key.bits s) : ∃ k, k < 4 ∧ b = Key.c s k := by
  simp only [Key.bits, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, hk, rfl⟩

section Bus
variable {tr : Trace Fp} {pub : List Fp}

theorem ev_sm2 {t r : Nat} (x : Expr) (hx : ev tr t r pub x < 2 ^ 21) :
    ev tr t r pub (sm 2 x) = 2 * ev tr t r pub x := by
  change ev tr t r pub (Expr.mul (.const 2) x) = _
  rw [ev_mul, ev_const, show 2 % P = 2 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem ev_succ_small {t r : Nat} (x : Expr) (hx : ev tr t r pub x < 2 ^ 21) :
    ev tr t r pub (x + 1) = ev tr t r pub x + 1 := by
  rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)]

theorem key_hc {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr) :
    ∀ r, r < tr.height 1 → ∀ e ∈ Key.table.constraints, e.eval tr 1 r pub = 0 :=
  fun r hr => hH.constr 1 (by rw [fullAir_len]; omega) r hr

theorem key_log {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr) :
    tr.log 1 ≤ 20 := (hH.logBound 1 (by rw [fullAir_len]; omega)).2

/-- **Every `NIB` message sent is a key nibble.** -/
theorem nib_sent {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_NIB true) :
    ∃ x i n : Fp, m = [x, i, n] ∧ (keyOf tr x.toNat)[i.toNat]? = some n.toNat ∧ i.toNat < 2 ^ 21 := by
  have hc := key_hc hH
  have hlog := key_log hH
  have hH20 : tr.height 1 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  obtain ⟨r, hr, i, hi, hb, hs, hp, rfl⟩ :=
    sender_m5a B_NIB 1 (by simp [m5aAir]) (key_only D B_NIB (.inl rfl)) hx hm
  change i ∈ Key.interactions at hi
  obtain ⟨b, hbm, hbe⟩ := multNat_pos i hp
  rcases key_nib_iface hi hb hs with rfl | rfl
  · obtain ⟨k, hk, rfl⟩ := mem_bits hbm
    have ha : kc tr r "act" = 1 := gate_of_one (key_h hc hr (m_mh k hk)) (eval_one_ev hbe)
    obtain ⟨-, hj, -, -⟩ := key_inv hc hlog r hr ha
    obtain ⟨e1, -⟩ := key_row_get hc hlog hr ha
    have e : ev tr 1 r pub (sm 2 (Key.c "j")) = 2 * kc tr r "j" := by
      rw [ev_sm2 _ (by rw [ev_kc]; omega), ev_kc]
    refine ⟨_, _, _, rfl, ?_, ?_⟩
    · change (keyOf tr (kc tr r "kid"))[ev tr 1 r pub (sm 2 (Key.c "j"))]? = some (kc tr r "hi")
      rw [e]; exact e1
    · change ev tr 1 r pub (sm 2 (Key.c "j")) < _
      rw [e]; omega
  · obtain ⟨k, hk, rfl⟩ := mem_bits hbm
    have ha : kc tr r "act" = 1 := gate_of_one (key_h hc hr (m_ml k hk)) (eval_one_ev hbe)
    obtain ⟨-, hj, -, -⟩ := key_inv hc hlog r hr ha
    obtain ⟨-, e1⟩ := key_row_get hc hlog hr ha
    have e : ev tr 1 r pub (sm 2 (Key.c "j") + 1) = 2 * kc tr r "j" + 1 := by
      rw [ev_succ_small _ (by rw [ev_sm2 _ (by rw [ev_kc]; omega), ev_kc]; omega),
        ev_sm2 _ (by rw [ev_kc]; omega), ev_kc]
    refine ⟨_, _, _, rfl, ?_, ?_⟩
    · change (keyOf tr (kc tr r "kid"))[ev tr 1 r pub (sm 2 (Key.c "j") + 1)]? = some (kc tr r "lo")
      rw [e]; exact e1
    · change ev tr 1 r pub (sm 2 (Key.c "j") + 1) < _
      rw [e]; omega

/-- **Every `KLEN` message sent is a key length.** -/
theorem klen_sent {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_KLEN true) :
    ∃ x l : Fp, m = [x, l] ∧ (keyOf tr x.toNat).length = l.toNat := by
  have hc := key_hc hH
  have hlog := key_log hH
  have hH20 : tr.height 1 ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hlog
  obtain ⟨r, hr, i, hi, hb, hs, hp, rfl⟩ :=
    sender_m5a B_KLEN 1 (by simp [m5aAir]) (key_only D B_KLEN (.inr (.inl rfl))) hx hm
  change i ∈ Key.interactions at hi
  obtain ⟨b, hbm, hbe⟩ := multNat_pos i hp
  obtain rfl := key_klen_iface hi hb hs
  obtain ⟨k, hk, rfl⟩ := mem_bits hbm
  have hl : kc tr r "last" = 1 := gate_of_one (key_h hc hr (m_mlen k hk)) (eval_one_ev hbe)
  have ha : kc tr r "act" = 1 := gate_of_one (key_h hc hr m_last_act) hl
  obtain ⟨-, hj, -, -⟩ := key_inv hc hlog r hr ha
  have e : ev tr 1 r pub (sm 2 (Key.c "j" + 1)) = 2 * (kc tr r "j" + 1) := by
    rw [ev_sm2 _ (by rw [ev_succ_small _ (by rw [ev_kc]; omega), ev_kc]; omega),
      ev_succ_small _ (by rw [ev_kc]; omega), ev_kc]
  refine ⟨_, _, rfl, ?_⟩
  change (keyOf tr (kc tr r "kid")).length = ev tr 1 r pub (sm 2 (Key.c "j" + 1))
  rw [e]; exact key_row_len hc hlog hr ha hl

/-- **`NIB` lookups** (any receiving table): a received message is a key nibble. -/
theorem nib_recv {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_NIB false) :
    ∃ x i n : Fp, m = [x, i, n] ∧ (keyOf tr x.toNat)[i.toNat]? = some n.toNat ∧ i.toNat < 2 ^ 21 :=
  nib_sent hH hx (recv_sent hH hm)

/-- **`KLEN` lookups**: a received message is a key length. -/
theorem klen_recv {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_KLEN false) :
    ∃ x l : Fp, m = [x, l] ∧ (keyOf tr x.toNat).length = l.toNat :=
  klen_sent hH hx (recv_sent hH hm)

/-- **Row form of a `NIB` lookup**: a firing one-bit receive `rcv B_NIB g [e₀, e₁, e₂]` of row `r`
of table `t` of the Lean AIR. -/
theorem nib_of_rcv {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) {t : Nat}
    (ht : t < (m5aAir D).tables.length) {g e₀ e₁ e₂ : Expr}
    (hi : rcv B_NIB g [e₀, e₁, e₂] ∈ ((m5aAir D).tables[t]).interactions) {r : Nat}
    (hr : r < tr.height t) (hg : g.eval tr t r pub = 1) :
    (keyOf tr (ev tr t r pub e₀))[ev tr t r pub e₁]? = some (ev tr t r pub e₂) ∧
      ev tr t r pub e₁ < 2 ^ 21 := by
  have ht' : t < (fullAir D extra nb np).tables.length := by
    have := fullAir_len D extra nb np; have h12 : (m5aAir D).tables.length = 12 := rfl; omega
  have hm := msg_mem_busList (A := fullAir D extra nb np) ht' (by rw [fullAir_get ht ht']; exact hi) hr
    rfl hg
  obtain ⟨x, i, n, he, h1, h2⟩ := nib_recv hH hx hm
  simp only [rcv, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
  obtain ⟨rfl, rfl, rfl, -⟩ := he
  exact ⟨h1, h2⟩

/-- **Row form of a `KLEN` lookup.** -/
theorem klen_of_rcv {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) {t : Nat}
    (ht : t < (m5aAir D).tables.length) {g e₀ e₁ : Expr}
    (hi : rcv B_KLEN g [e₀, e₁] ∈ ((m5aAir D).tables[t]).interactions) {r : Nat}
    (hr : r < tr.height t) (hg : g.eval tr t r pub = 1) :
    (keyOf tr (ev tr t r pub e₀)).length = ev tr t r pub e₁ := by
  have ht' : t < (fullAir D extra nb np).tables.length := by
    have := fullAir_len D extra nb np; have h12 : (m5aAir D).tables.length = 12 := rfl; omega
  have hm := msg_mem_busList (A := fullAir D extra nb np) ht' (by rw [fullAir_get ht ht']; exact hi) hr
    rfl hg
  obtain ⟨x, l, he, h1⟩ := klen_recv hH hx hm
  simp only [rcv, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he
  obtain ⟨rfl, rfl, -⟩ := he
  exact h1

end Bus

end StateM5a.KeyDecode
