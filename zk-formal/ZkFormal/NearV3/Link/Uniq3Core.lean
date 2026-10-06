import ZkFormal.NearV3.Link.Uniq

/-!
# ZkFormal.NearV3.Link.Uniq3Core — weak uniqueness of `uniqV3` without a bound on `τ`

`Link/Uniq.lean` (`uniq_functional`) needs `e.tau + 1 < P` for every entry, so that the
instance step `τ' = (τ + st) mod P` never wraps.  The `uniqV3` view does not bound the first
`τ`, and neither do the other views (a head's `τ` is any canonical value), so here the step
chain is unwrapped instead: with `U 0 = τ₀`, `U (t+1) = U t + st_{t+1}` (in `ℕ`), every entry
has `τ_t = U t mod P`, and `U` grows by at most one per entry.  Hence, for a table of at most
`P` entries, equal `τ` (mod `P`) means equal `U`, and the sort key `U t · 2^256 + le256 bytes`
is weakly monotone along the table (strictly, unless the entry is a duplicate).

* `uniq_functional3` — equal instance and digest ⇒ equal message bytes, given `|es| ≤ P`;
* `storeOf_hashFunctional3` — the store version (as `storeOf_hashFunctional`).
-/

namespace ZkFormal.NearV3

open ZkFormal.Near ZkFormal.Algebra NearSpec

/-- Unwrapped instance numbers of the entries. -/
def uU (es : List UniqE) : Nat → Nat
  | 0 => (es.getD 0 default).tau
  | t + 1 => uU es t + (es.getD (t + 1) default).st

theorem uU_mod (es : List UniqE) (hwf : UniqWf es) :
    ∀ t (ht : t < es.length), es[t].tau = uU es t % P := by
  intro t
  induction t with
  | zero =>
    intro ht
    have := (hwf.canon _ (List.getElem_mem ht)).2.2.1
    simp only [uU, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact (Nat.mod_eq_of_lt this).symm
  | succ t ih =>
    intro ht
    obtain ⟨-, hta, -, -⟩ := hwf.link t ht
    rw [hta, ih (by omega)]
    simp only [uU, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    rw [Nat.mod_add_mod]

theorem uU_mono (es : List UniqE) (hwf : UniqWf es) :
    ∀ t d, t + d < es.length → uU es t ≤ uU es (t + d) ∧ uU es (t + d) ≤ uU es t + d := by
  intro t d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hm : es[t + d + 1] ∈ es := List.getElem_mem h
    have hst := (hwf.canon _ hm).2.2.2.1
    have e : uU es (t + (d + 1)) = uU es (t + d) + es[t + d + 1].st := by
      have h' : t + d + 1 < es.length := by omega
      rw [show t + (d + 1) = t + d + 1 by omega]
      simp only [uU, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h', Option.getD_some]
    rw [e]; omega

theorem uU_eq (es : List UniqE) (hwf : UniqWf es) (hlen : es.length ≤ P) {t t' : Nat}
    (ht : t < es.length) (ht' : t' < es.length) (he : es[t].tau = es[t'].tau) : uU es t = uU es t' := by
  rw [uU_mod es hwf t ht, uU_mod es hwf t' ht'] at he
  have key : ∀ a b, a < es.length → b < es.length → a ≤ b → uU es a % P = uU es b % P →
      uU es a = uU es b := by
    intro a b ha hb hab hm
    obtain ⟨h1, h2⟩ := uU_mono es hwf a (b - a) (by omega)
    rw [show a + (b - a) = b by omega] at h1 h2
    have := Nat.sub_mod_eq_zero_of_mod_eq hm.symm
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
    rcases k with _ | k
    · omega
    · have : P ≤ uU es b - uU es a := by rw [hk]; exact Nat.le_mul_of_pos_right _ (by omega)
      omega
  rcases Nat.le_total t t' with h | h
  · exact key t t' ht ht' h he
  · exact (key t' t ht' ht h he.symm).symm

/-- Unwrapped sort key of entry `t`. -/
def uK (es : List UniqE) (t : Nat) : Nat := uU es t * 2 ^ 256 + le256 (es.getD t default).bytes

theorem uniq_weak3 (es : List UniqE) (hwf : UniqWf es) (B : Nat → Bytes)
    (hdup : ∀ t (ht : t + 1 < es.length), es[t + 1].eq = 1 → B es[t + 1].eid = B es[t].eid)
    (hbytes : ∀ e ∈ es, ∀ y ∈ e.bytes, y < 256) :
    WeakUniq (uK es) (fun t => B (es.getD t default).eid) (List.range es.length) := by
  have step : ∀ t (ht : t + 1 < es.length),
      WeakStep (uK es) (fun t => B (es.getD t default).eid) t (t + 1) := by
    intro t ht
    have h0 : es[t] ∈ es := List.getElem_mem (by omega)
    have h1 : es[t + 1] ∈ es := List.getElem_mem ht
    obtain ⟨-, -, heq1, heq0⟩ := hwf.link t ht
    obtain ⟨-, -, -, hst, heqb, -⟩ := hwf.canon _ h1
    have hb0 := hbytes _ h0
    have hb1 := hbytes _ h1
    have hlt0 := le256_lt32 (hwf.len _ h0) hb0
    have hlt1 := le256_lt32 (hwf.len _ h1) hb1
    have hbb : ∀ y ∈ es[t].bytes ++ es[t + 1].bytes, y < 256 := by
      intro y hy; rcases List.mem_append.1 hy with hy | hy
      · exact hb0 y hy
      · exact hb1 y hy
    have g0 : es.getD t default = es[t] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < es.length by omega)]
    have g1 : es.getD (t + 1) default = es[t + 1] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    have hU : uU es (t + 1) = uU es t + es[t + 1].st := by
      simp only [uU, g1]
    unfold WeakStep uK
    simp only [g0, g1, hU]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hst with hs | hs
    · rw [hs, Nat.add_zero]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 heqb with he | he
      · left; have := heq0 he hs hbb; omega
      · right
        have hbe := (heq1 he).2 hbb
        exact ⟨by rw [hbe], (hdup t ht he).symm⟩
    · rw [hs]; left; rw [Nat.add_mul, Nat.one_mul]; omega
  have key : ∀ (l : List Nat), (∀ t (ht : t + 1 < l.length),
      WeakStep (uK es) (fun t => B (es.getD t default).eid) l[t] l[t + 1]) →
      WeakUniq (uK es) (fun t => B (es.getD t default).eid) l := by
    intro l
    induction l with
    | nil => intro _; trivial
    | cons a l ih =>
      intro h
      cases l with
      | nil => trivial
      | cons b r =>
        exact ⟨h 0 (by simp), ih (fun t ht => h (t + 1) (by simp at ht ⊢; omega))⟩
  apply key
  intro t ht
  simp only [List.length_range] at ht
  simp only [List.getElem_range]
  exact step t ht

/-- **Equal instance and digest ⇒ equal message bytes** (no bound on `τ`; `|es| ≤ P`). -/
theorem uniq_functional3 (es : List UniqE) (hwf : UniqWf es) (B : Nat → Bytes)
    (hdup : ∀ t (ht : t + 1 < es.length), es[t + 1].eq = 1 → B es[t + 1].eid = B es[t].eid)
    (hbytes : ∀ e ∈ es, ∀ y ∈ e.bytes, y < 256) (hlen : es.length ≤ P) :
    ∀ e ∈ es, ∀ e' ∈ es, e.tau = e'.tau → e.bytes = e'.bytes → B e.eid = B e'.eid := by
  intro e he e' he' ht hb
  obtain ⟨t, htl, rfl⟩ := List.getElem_of_mem he
  obtain ⟨t', htl', rfl⟩ := List.getElem_of_mem he'
  have g0 : es.getD t default = es[t] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl]
  have g1 : es.getD t' default = es[t'] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl']
  have := weakUniq_functional (uniq_weak3 es hwf B hdup hbytes) t (List.mem_range.2 htl) t'
    (List.mem_range.2 htl') (by unfold uK; rw [g0, g1, uU_eq es hwf hlen htl htl' ht, hb])
  simpa only [g0, g1] using this

/-- **A store covered by `uniq` entries is hash-functional** (`|es| ≤ P`, no bound on `τ`). -/
theorem storeOf_hashFunctional3 (es : List UniqE) (hwf : UniqWf es) (B : Nat → Bytes)
    (hdup : ∀ t (ht : t + 1 < es.length), es[t + 1].eq = 1 → B es[t + 1].eid = B es[t].eid)
    (hbytes : ∀ e ∈ es, ∀ y ∈ e.bytes, y < 256) (hlen : es.length ≤ P)
    (τ : Nat) (st : List Bytes)
    (hcov : ∀ x ∈ st, ∃ e ∈ es, e.tau = τ ∧ B e.eid = x ∧ e.bytes = digNat x) : HashFunctional st := by
  intro x hx y hy hxy
  obtain ⟨e, he, het, hex, heb⟩ := hcov x hx
  obtain ⟨e', he', het', hey, heb'⟩ := hcov y hy
  rw [← hex, ← hey]
  apply uniq_functional3 es hwf B hdup hbytes hlen e he e' he' (by rw [het, het'])
  rw [heb, heb', digNat, digNat, hxy]

end ZkFormal.NearV3
