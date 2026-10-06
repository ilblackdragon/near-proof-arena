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

theorem streamWord_lt (key : List Nat) (k : Nat) : streamWord key k < 2 ^ 32 := by
  sorry

theorem nextU32_rngAt (key : List Nat) (k : Nat) :
    (rngAt key k).nextU32 = (streamWord key k, rngAt key (k + 1)) := by
  sorry

theorem ofSeed_eq (seed : List UInt8) : Rng.ofSeed seed = rngAt (leWords seed) 0 := by
  sorry

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
  sorry

/-- **Spec side of `rng_contract`**: the words drawn from `Rng.ofSeed seed` are the stream. -/
theorem rng_stream (seed : List UInt8) (n : Nat) :
    draws n (Rng.ofSeed seed) =
      ((List.range n).map (streamWord (leWords seed)), rngAt (leWords seed) n) := by
  sorry

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
  sorry

theorem genAt_some_iff (fuel n : Nat) (key : List Nat) (k j k' : Nat) :
    genAt fuel n key k = some (j, k') ↔
      ∃ t, t < fuel ∧ k' = k + t + 1 ∧
        (∀ i, i < t → accepts n (streamWord key (k + i)) = false) ∧
        accepts n (streamWord key (k + t)) = true ∧
        j = streamWord key (k + t) * n / M32 := by
  sorry

theorem genAt_lt {fuel n : Nat} {key : List Nat} {k j k' : Nat}
    (h : genAt fuel n key k = some (j, k')) (hn : n < 2 ^ 32) : j < n := by
  sorry

theorem zoneOf_eq {n i : Nat} (h1 : 2 ^ i ≤ n) (h2 : n < 2 ^ (i + 1)) (hi : i < 16) :
    zoneOf n = 65536 * (n * 2 ^ (15 - i)) - 1 := by
  sorry

theorem accepts_iff {n i v : Nat} (h1 : 2 ^ i ≤ n) (h2 : n < 2 ^ (i + 1)) (hi : i < 16)
    (hv : v < 2 ^ 32) :
    accepts n v = true ↔ (v * n / 65536) % 65536 < n * 2 ^ (15 - i) := by
  sorry

end ZkFormal.Chacha
