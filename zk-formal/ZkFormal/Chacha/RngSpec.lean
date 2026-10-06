import ZkFormal.Chacha.Spec

/-!
# ZkFormal.Chacha.RngSpec — the `Rng` word stream and `genIndex` (Lemire), spec side

* `streamWord key k` is word `k` of the stream: `(chachaBlock key (k / 16))[k % 16]`.
* `rngAt key k` is the canonical `Rng` state after `k` draws (`Rng.ofSeed seed = rngAt
  (leWords seed) 0`), and `nextU32 (rngAt key k) = (streamWord key k, rngAt key (k+1))`.
* `genIndex fuel n (rngAt key k)` is `genAt fuel n key k` (draws at `k, k+1, …`).
* For `2^i ≤ n < 2^(i+1)` (`i < 16`): `zone = 2^16·(n·2^(15-i)) - 1`, and a draw `v`
  is accepted iff the middle limb `⌊v·n / 2^16⌋ mod 2^16` is below `n·2^(15-i)`.
-/

namespace ZkFormal.Chacha

open NearSpecV3

/-- Word `k` of the ChaCha20 stream with key `key`. -/
def streamWord (key : List Nat) (k : Nat) : Nat := (chachaBlock key (k / 16)).getD (k % 16) 0

/-- Canonical RNG state after `k` draws. -/
def rngAt (key : List Nat) (k : Nat) : Rng :=
  if k % 16 = 0 then ⟨key, k / 16, []⟩
  else ⟨key, k / 16 + 1, (chachaBlock key (k / 16)).drop (k % 16)⟩

theorem chachaBlock_mem_lt {key : List Nat} {ctr w : Nat} (h : w ∈ chachaBlock key ctr) :
    w < 2 ^ 32 := by
  simp only [chachaBlock, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  exact add32_lt _ _

theorem streamWord_lt (key : List Nat) (k : Nat) : streamWord key k < 2 ^ 32 := by
  unfold streamWord
  rw [List.getD_eq_getElem?_getD]
  cases h : (chachaBlock key (k / 16))[k % 16]? with
  | none => simp
  | some w => exact chachaBlock_mem_lt (List.mem_of_getElem? h)

theorem nextU32_nil (key : List Nat) (ctr : Nat) :
    Rng.nextU32 ⟨key, ctr, []⟩ =
      ((chachaBlock key ctr).getD 0 0, ⟨key, ctr + 1, (chachaBlock key ctr).drop 1⟩) := by
  have hl := chachaBlock_length key ctr
  unfold Rng.nextU32
  dsimp only
  split
  · rename_i w rest heq
    simp [heq]
  · rename_i heq
    rw [heq] at hl; simp at hl

theorem nextU32_cons (key : List Nat) (ctr w : Nat) (rest : List Nat) :
    Rng.nextU32 ⟨key, ctr, w :: rest⟩ = (w, ⟨key, ctr, rest⟩) := rfl

theorem nextU32_rngAt (key : List Nat) (k : Nat) :
    (rngAt key k).nextU32 = (streamWord key k, rngAt key (k + 1)) := by
  have hlen := chachaBlock_length key (k / 16)
  unfold rngAt streamWord
  by_cases h0 : k % 16 = 0
  · have h1 : (k + 1) % 16 = 1 := by omega
    have h2 : (k + 1) / 16 = k / 16 := by omega
    simp only [h0, h1, h2, ite_true, nextU32_nil]
    simp
  · have hi : k % 16 < (chachaBlock key (k / 16)).length := by omega
    simp only [h0, ite_false]
    rw [List.drop_eq_getElem_cons hi, nextU32_cons]
    by_cases h15 : k % 16 = 15
    · have h1 : (k + 1) % 16 = 0 := by omega
      have h2 : (k + 1) / 16 = k / 16 + 1 := by omega
      simp only [h1, h2, ite_true]
      rw [List.drop_eq_nil_of_le (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · have h1 : (k + 1) % 16 = k % 16 + 1 := by omega
      have h2 : (k + 1) / 16 = k / 16 := by omega
      simp only [h1, h2, Nat.add_one_ne_zero, ite_false]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem ofSeed_eq (seed : List UInt8) : Rng.ofSeed seed = rngAt (leWords seed) 0 := by
  simp [rngAt, Rng.ofSeed]

/-- `n` consecutive draws. -/
def draws : Nat → Rng → List Nat × Rng
  | 0, r => ([], r)
  | n + 1, r =>
    let p := r.nextU32
    let q := draws n p.2
    (p.1 :: q.1, q.2)

theorem draws_rngAt (key : List Nat) (k n : Nat) :
    draws n (rngAt key k) =
      ((List.range n).map (fun i => streamWord key (k + i)), rngAt key (k + n)) := by
  induction n generalizing k with
  | zero => simp [draws]
  | succ n ih =>
    simp only [draws, nextU32_rngAt, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    have hf : ((fun i => streamWord key (k + 1 + i)) : Nat → Nat) =
        (fun i => streamWord key (k + i)) ∘ Nat.succ := by
      funext i; simp only [Function.comp]; congr 1; omega
    rw [hf, show k + 1 + n = k + (n + 1) by omega]; rfl

/-- **Spec side of `rng_contract`**: the words drawn from `Rng.ofSeed seed` are the stream. -/
theorem rng_stream (seed : List UInt8) (n : Nat) :
    draws n (Rng.ofSeed seed) =
      ((List.range n).map (streamWord (leWords seed)), rngAt (leWords seed) n) := by
  rw [ofSeed_eq, draws_rngAt]
  simp

/-- The Lemire zone of `gen_range(0..n)`. -/
def zoneOf (n : Nat) : Nat := ((n <<< lz32 n) % M32 + M32 - 1) % M32

def accepts (n v : Nat) : Bool := decide ((v * n) % M32 ≤ zoneOf n)

/-- `genIndex` on the stream: draws at `k, k+1, …`; returns `(index, position after)`. -/
def genAt : Nat → Nat → List Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _ => none
  | f + 1, n, key, k =>
    if accepts n (streamWord key k) then some (streamWord key k * n / M32, k + 1)
    else genAt f n key (k + 1)

theorem genIndex_rngAt (fuel n : Nat) (key : List Nat) (k : Nat) :
    genIndex fuel n (rngAt key k) = (genAt fuel n key k).map (fun p => (p.1, rngAt key p.2)) := by
  induction fuel generalizing k with
  | zero => rfl
  | succ f ih =>
    simp only [genIndex, nextU32_rngAt, genAt, accepts, zoneOf]
    by_cases h : streamWord key k * n % M32 ≤ ((n <<< lz32 n) % M32 + M32 - 1) % M32
    · simp [h]
    · simp [h, ih]

theorem genAt_some_iff (fuel n : Nat) (key : List Nat) (k j k' : Nat) :
    genAt fuel n key k = some (j, k') ↔
      ∃ t, t < fuel ∧ k' = k + t + 1 ∧
        (∀ i, i < t → accepts n (streamWord key (k + i)) = false) ∧
        accepts n (streamWord key (k + t)) = true ∧
        j = streamWord key (k + t) * n / M32 := by
  induction fuel generalizing k with
  | zero => simp [genAt]
  | succ f ih =>
    by_cases ha : accepts n (streamWord key k) = true
    · simp only [genAt, ha, ite_true]
      constructor
      · intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨0, by omega, by omega, fun i hi => by omega, by simpa using ha, by simp [h.1]⟩
      · rintro ⟨t, ht, hk', hrej, hacc, hj⟩
        cases t with
        | zero => simp_all
        | succ t =>
          have := hrej 0 (by omega)
          simp_all
    · have ha' : accepts n (streamWord key k) = false := by simpa using ha
      simp only [genAt, ha', Bool.false_eq_true, ite_false]
      rw [ih]
      constructor
      · rintro ⟨t, ht, hk', hrej, hacc, hj⟩
        refine ⟨t + 1, by omega, by omega, ?_, ?_, ?_⟩
        · intro i hi
          cases i with
          | zero => simpa using ha'
          | succ i =>
            have := hrej i (by omega)
            rwa [show k + 1 + i = k + (i + 1) by omega] at this
        · rwa [show k + 1 + t = k + (t + 1) by omega] at hacc
        · rw [hj, show k + 1 + t = k + (t + 1) by omega]
      · rintro ⟨t, ht, hk', hrej, hacc, hj⟩
        cases t with
        | zero => simp_all
        | succ t =>
          refine ⟨t, by omega, by omega, ?_, ?_, ?_⟩
          · intro i hi
            have := hrej (i + 1) (by omega)
            rwa [show k + (i + 1) = k + 1 + i by omega] at this
          · rwa [show k + (t + 1) = k + 1 + t by omega] at hacc
          · rw [hj, show k + (t + 1) = k + 1 + t by omega]

theorem genAt_lt {fuel n : Nat} {key : List Nat} {k j k' : Nat}
    (h : genAt fuel n key k = some (j, k')) (hn : n < 2 ^ 32) (hn0 : 0 < n) : j < n := by
  obtain ⟨t, _, _, _, _, hj⟩ := (genAt_some_iff fuel n key k j k').1 h
  have hw := streamWord_lt key (k + t)
  rw [hj, Nat.div_lt_iff_lt_mul (by decide : 0 < M32)]
  have : streamWord key (k + t) * n < 2 ^ 32 * n := Nat.mul_lt_mul_of_pos_right hw hn0
  rw [Nat.mul_comm n]; exact this

theorem bitLen_succ_succ (f m : Nat) : bitLen (f + 1) (m + 1) = 1 + bitLen f ((m + 1) / 2) := rfl

theorem bitLen_eq : ∀ (i fuel n : Nat), 2 ^ i ≤ n → n < 2 ^ (i + 1) → i < fuel →
    bitLen fuel n = i + 1
  | 0, fuel, n, h1, h2, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have : n = 1 := by simp at h1 h2; omega
    subst this
    cases f <;> rfl
  | i + 1, fuel, n, h1, h2, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := Nat.one_le_two_pow (n := i + 1); omega⟩
    rw [bitLen_succ_succ, bitLen_eq i f ((m + 1) / 2) ?_ ?_ (by omega)]
    · omega
    · rw [Nat.pow_succ] at h1; omega
    · rw [Nat.pow_succ] at h2; omega

theorem zoneOf_eq {n i : Nat} (h1 : 2 ^ i ≤ n) (h2 : n < 2 ^ (i + 1)) (hi : i < 16) :
    zoneOf n = 65536 * (n * 2 ^ (15 - i)) - 1 := by
  have hb : bitLen 64 n = i + 1 := bitLen_eq i 64 n h1 h2 (by omega)
  have hl : lz32 n = 31 - i := by unfold lz32; omega
  unfold zoneOf
  rw [hl, Nat.shiftLeft_eq]
  have hp : 2 ^ (31 - i) = 65536 * 2 ^ (15 - i) := by
    rw [show 31 - i = 16 + (15 - i) by omega, Nat.pow_add]
  have hlt : n * 2 ^ (31 - i) < 2 ^ 32 := by
    calc n * 2 ^ (31 - i) < 2 ^ (i + 1) * 2 ^ (31 - i) :=
          Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
      _ = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < n * 2 ^ (15 - i) :=
    Nat.mul_pos (by have := Nat.one_le_two_pow (n := i); omega) (Nat.two_pow_pos _)
  rw [hp, Nat.mul_left_comm] at hlt
  rw [hp, Nat.mul_left_comm]
  generalize n * 2 ^ (15 - i) = P at *
  unfold M32
  omega

theorem accepts_iff {n i v : Nat} (h1 : 2 ^ i ≤ n) (h2 : n < 2 ^ (i + 1)) (hi : i < 16)
    (hv : v < 2 ^ 32) :
    accepts n v = true ↔ (v * n / 65536) % 65536 < n * 2 ^ (15 - i) := by
  have hpos : 0 < n * 2 ^ (15 - i) :=
    Nat.mul_pos (by have := Nat.one_le_two_pow (n := i); omega) (Nat.two_pow_pos _)
  simp only [accepts, decide_eq_true_eq, zoneOf_eq h1 h2 hi]
  unfold M32
  generalize v * n = q
  generalize n * 2 ^ (15 - i) = Z at *
  omega

end ZkFormal.Chacha
