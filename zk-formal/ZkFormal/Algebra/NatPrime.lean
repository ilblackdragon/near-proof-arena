/-!
# ZkFormal.Algebra.NatPrime — primes, trial division, Euclid, Fermat (on `Nat`)

Mathlib-free elementary number theory for the base field (DESIGN.md R5):

* `IsPrime n` — the textbook definition;
* `isPrime_of_trialDiv` — a kernel-reducible trial-division certificate
  (`trialDiv n fuel d = true` checks every `d ≤ k ≤ √n`);
* `euclid` — a prime dividing a product divides a factor (from core's
  `Nat.Coprime`);
* `fermat` — `a^(p-1) ≡ 1 (mod p)` for `p ∤ a`, by the classical
  permutation argument: `x ↦ a·x mod p` permutes `[1, p)`.
* `powMod` — square-and-multiply modular exponentiation, `powMod_eq`.
-/

namespace ZkFormal.Algebra

/-- `n` is prime. -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

/-- Trial division: no `k` with `d ≤ k`, `k·k ≤ n` (within `fuel` steps)
divides `n`.  Runs out of fuel as `false`. -/
def trialDiv (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else (n % d != 0) && trialDiv n fuel (d + 1)

theorem trialDiv_spec (n : Nat) : ∀ fuel d, trialDiv n fuel d = true →
    ∀ k, d ≤ k → k * k ≤ n → n % k ≠ 0
  | 0, _, h => by simp [trialDiv] at h
  | fuel + 1, d, h => by
    intro k hdk hk
    simp only [trialDiv] at h
    split at h
    · have : d * d ≤ k * k := Nat.mul_le_mul hdk hdk
      omega
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      by_cases hkd : k = d
      · subst hkd; exact h.1
      · exact trialDiv_spec n fuel (d + 1) h.2 k (by omega) hk

/-- Trial division up to `√n` certifies primality. -/
theorem isPrime_of_trialDiv {n fuel : Nat} (h2 : 2 ≤ n) (h : trialDiv n fuel 2 = true) :
    IsPrime n := by
  refine ⟨h2, fun d hd => ?_⟩
  obtain ⟨m, rfl⟩ := hd
  have hspec := trialDiv_spec _ fuel 2 h
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · have : d ≠ 0 := by rintro rfl; simp at h2
    left; omega
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have : m ≠ 0 := by rintro rfl; simp at h2
    have : m = 1 := by omega
    subst this; right; simp
  exfalso
  rcases Nat.le_total d m with hdm | hmd
  · exact hspec d hd2 (Nat.mul_le_mul_left d hdm) (by simp [Nat.mul_mod_right])
  · exact hspec m hm2 (Nat.mul_le_mul_right m hmd) (by simp [Nat.mul_mod_left])

/-! ## Euclid's lemma -/

theorem IsPrime.two_le {p : Nat} (hp : IsPrime p) : 2 ≤ p := hp.1

theorem IsPrime.pos {p : Nat} (hp : IsPrime p) : 0 < p := by have := hp.1; omega

theorem coprime_of_not_dvd {p a : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) : Nat.Coprime p a := by
  rcases hp.2 _ (Nat.gcd_dvd_left p a) with h | h
  · exact h
  · exact absurd (h ▸ Nat.gcd_dvd_right p a) ha

theorem euclid {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · exact Or.inr ((coprime_of_not_dvd hp ha).dvd_of_dvd_mul_left h)

theorem mul_mod_ne_zero {p a b : Nat} (hp : IsPrime p) (ha : a % p ≠ 0) (hb : b % p ≠ 0) :
    (a * b) % p ≠ 0 := by
  intro h
  rcases euclid hp (Nat.dvd_of_mod_eq_zero h) with h' | h'
  · exact ha (Nat.mod_eq_zero_of_dvd h')
  · exact hb (Nat.mod_eq_zero_of_dvd h')

theorem pow_mod_ne_zero {p a : Nat} (hp : IsPrime p) (ha : a % p ≠ 0) :
    ∀ n, (a ^ n) % p ≠ 0
  | 0 => by have := hp.1; rw [Nat.pow_zero, Nat.mod_eq_of_lt (by omega)]; omega
  | n + 1 => by rw [Nat.pow_succ]; exact mul_mod_ne_zero hp (pow_mod_ne_zero hp ha n) ha

theorem mod_eq_of_dvd_sub {p x y : Nat} (hxy : y ≤ x) (h : p ∣ x - y) : x % p = y % p := by
  obtain ⟨k, hk⟩ := h
  have : x = y + p * k := by omega
  rw [this, Nat.add_mul_mod_self_left]

/-- Cancellation: `p ∤ c` and `a·c ≡ b·c` give `a ≡ b`. -/
theorem mod_cancel {p a b c : Nat} (hp : IsPrime p) (hc : c % p ≠ 0)
    (h : (a * c) % p = (b * c) % p) : a % p = b % p := by
  have key : ∀ x y : Nat, y ≤ x → (x * c) % p = (y * c) % p → x % p = y % p := by
    intro x y hxy hxy'
    have h1 : p ∣ x * c - y * c := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxy')
    rw [← Nat.sub_mul] at h1
    rcases euclid hp h1 with h2 | h2
    · exact mod_eq_of_dvd_sub hxy h2
    · exact absurd (Nat.mod_eq_zero_of_dvd h2) hc
  rcases Nat.le_total b a with hab | hab
  · exact key a b hab h
  · exact (key b a hab h.symm).symm

/-! ## Fermat's little theorem -/

theorem prod_map_mulmod (p a : Nat) : ∀ l : List Nat,
    ((l.map fun x => a * x % p).prod) % p = (a ^ l.length * l.prod) % p
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Nat.mul_mod, prod_map_mulmod p a l, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ]
    congr 1
    ac_rfl

theorem prod_mod_ne_zero {p : Nat} (hp : IsPrime p) : ∀ l : List Nat,
    (∀ x ∈ l, x % p ≠ 0) → l.prod % p ≠ 0
  | [], _ => by have := hp.1; simp; omega
  | x :: l, h => by
    simp only [List.prod_cons]
    exact mul_mod_ne_zero hp (h x (by simp)) (prod_mod_ne_zero hp l fun y hy => h y (by simp [hy]))

theorem nodup_map_on {α β : Type} {f : α → β} : ∀ {l : List α},
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on (fun x hx y hy => h x (by simp [hx]) y (by simp [hy])) hl.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    exact hl.1 (h b (by simp [hb]) a (by simp) hfb ▸ hb)

/-- Pigeonhole for duplicate-free lists of equal length. -/
theorem subset_of_nodup_subset {α : Type} [DecidableEq α] {l l' : List α} (hl' : l'.Nodup)
    (hsub : l' ⊆ l) (hlen : l.length ≤ l'.length) : l ⊆ l' := by
  intro x hx
  refine Classical.byContradiction fun hnx => ?_
  have hn : (x :: l').Nodup := List.nodup_cons.mpr ⟨hnx, hl'⟩
  have hs : x :: l' ⊆ l := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hsub hy
  have := hn.length_le_of_subset hs
  simp at this; omega

/-- **Fermat's little theorem.** -/
theorem fermat {p a : Nat} (hp : IsPrime p) (ha : a % p ≠ 0) : a ^ (p - 1) % p = 1 := by
  have hp2 := hp.1
  let l := List.range' 1 (p - 1)
  let l' := l.map fun x => a * x % p
  have hmem : ∀ x, x ∈ l ↔ 1 ≤ x ∧ x < p := by
    intro x; simp only [l, List.mem_range'_1]; omega
  have hnz : ∀ x ∈ l, x % p ≠ 0 := by
    intro x hx; have := (hmem x).mp hx; rw [Nat.mod_eq_of_lt this.2]; omega
  have hl : l.Nodup := List.nodup_range'
  have hinj : ∀ x ∈ l, ∀ y ∈ l, a * x % p = a * y % p → x = y := by
    intro x hx y hy hxy
    have h1 := mod_cancel (a := x) (b := y) (c := a) hp ha (by rw [Nat.mul_comm x, Nat.mul_comm y]; exact hxy)
    rw [Nat.mod_eq_of_lt ((hmem x).mp hx).2, Nat.mod_eq_of_lt ((hmem y).mp hy).2] at h1
    exact h1
  have hl' : l'.Nodup := nodup_map_on hinj hl
  have hsub : l' ⊆ l := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    refine (hmem _).mpr ⟨?_, Nat.mod_lt _ hp.pos⟩
    have := mul_mod_ne_zero hp ha (hnz x hx)
    omega
  have hsub' : l ⊆ l' := subset_of_nodup_subset hl' hsub (by simp [l'])
  have hperm : List.Perm l' l := (List.perm_ext_iff_of_nodup hl' hl).mpr fun x => ⟨fun h => hsub h, fun h => hsub' h⟩
  have hprod : l'.prod = l.prod := List.Perm.prod_nat hperm
  have key := prod_map_mulmod p a l
  rw [show (l.map fun x => a * x % p) = l' from rfl, hprod] at key
  have hlen : l.length = p - 1 := by simp [l]
  rw [hlen] at key
  have hP := prod_mod_ne_zero hp l hnz
  have hc := mod_cancel (a := 1) (b := a ^ (p - 1)) hp hP (by rw [Nat.one_mul]; exact key)
  rw [Nat.mod_eq_of_lt (by omega)] at hc
  exact hc.symm

end ZkFormal.Algebra
