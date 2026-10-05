/-!
# ChaCha20 RNG (rand_chacha 0.3.1) and rand 0.8.5 `SliceRandom::shuffle`

Leaf module of `near/pv86/chunk-validation/v0`. Used by
* `shuffle_receipt_proofs` (`chain/chain/src/sharding.rs:9-21`):
  `ChaCha20Rng::from_seed(prev_hash)` then `receipt_proofs.shuffle(&mut rng)`;
* the bandwidth scheduler's tie-break (`runtime/runtime/src/bandwidth_scheduler/scheduler.rs:291, 347-388`):
  one `ChaCha20Rng::from_seed(prev_block_hash)` for the whole run.

Source facts (docs/research/chunk-validation-boundary.md §5):
* rand_chacha 0.3.1 `ChaCha20Rng`: 20 rounds; state = constants ‖ key (seed as 8 LE
  words) ‖ 64-bit block counter starting at 0 (words 12–13) ‖ 64-bit stream id 0
  (words 14–15); output words of consecutive blocks in order (`next_u32`), i.e.
  RFC 8439 with a zero nonce for counters < 2³².
* rand 0.8.5 `shuffle`: `for i in (1..len).rev() { swap(i, gen_index(i + 1)) }`
  (`src/seq/mod.rs:586-592`); `gen_index(n)` = `gen_range(0..n as u32)` =
  Lemire widening multiply with rejection: `zone = (n << lz(n)) − 1` (as u32),
  `v = next_u32`, `m = v·n`, accept iff `m mod 2³² ≤ zone`, result `m >> 32`
  (`src/distributions/uniform.rs:507-554`).

Everything is over `Nat` with explicit `mod 2³²` (kernel-reducible: `Nat`
arithmetic and bitwise operations are GMP-accelerated in the kernel).

**Fuel.** The rejection loop is unbounded in principle; we allow 64 draws per
`gen_index`. For `n ≤ 2¹⁶` a draw is rejected with probability `< 2⁻¹⁶`, so
running out of fuel (`none`, i.e. the relation rejects) has probability
`< 2⁻¹⁰²⁴` per call. This is the only place where the Lean model can deviate
from nearcore, and only on that event.
-/

namespace NearSpecV3

def M32 : Nat := 4294967296

def add32 (a b : Nat) : Nat := (a + b) % M32
def rotl32 (a n : Nat) : Nat := ((a <<< n) % M32) ||| (a >>> (32 - n))

/-- little-endian 32-bit words of a byte list (length multiple of 4) -/
def leWords : List UInt8 → List Nat
  | a :: b :: c :: d :: rest => (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat) :: leWords rest
  | _ => []

def qr (s : Array Nat) (a b c d : Nat) : Array Nat :=
  let s := s.set! a (add32 s[a]! s[b]!)
  let s := s.set! d (rotl32 (s[d]! ^^^ s[a]!) 16)
  let s := s.set! c (add32 s[c]! s[d]!)
  let s := s.set! b (rotl32 (s[b]! ^^^ s[c]!) 12)
  let s := s.set! a (add32 s[a]! s[b]!)
  let s := s.set! d (rotl32 (s[d]! ^^^ s[a]!) 8)
  let s := s.set! c (add32 s[c]! s[d]!)
  s.set! b (rotl32 (s[b]! ^^^ s[c]!) 7)

def doubleRound (s : Array Nat) : Array Nat :=
  let s := qr s 0 4 8 12
  let s := qr s 1 5 9 13
  let s := qr s 2 6 10 14
  let s := qr s 3 7 11 15
  let s := qr s 0 5 10 15
  let s := qr s 1 6 11 12
  let s := qr s 2 7 8 13
  qr s 3 4 9 14

def rounds : Nat → Array Nat → Array Nat
  | 0, s => s
  | n + 1, s => rounds n (doubleRound s)

/-- One ChaCha20 block: 16 output words for `key` (8 words) and 64-bit block counter. -/
def chachaBlock (key : List Nat) (ctr : Nat) : List Nat :=
  let init : Array Nat :=
    #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++ key.toArray ++
      #[ctr % M32, (ctr / M32) % M32, 0, 0]
  let out := rounds 10 init
  (List.range 16).map fun i => add32 out[i]! init[i]!

/-- RNG state: key, next block counter, buffered words. -/
structure Rng where
  key : List Nat
  ctr : Nat
  buf : List Nat
  deriving Repr

def Rng.ofSeed (seed : List UInt8) : Rng := ⟨leWords seed, 0, []⟩

def Rng.nextU32 (r : Rng) : Nat × Rng :=
  match r.buf with
  | w :: rest => (w, { r with buf := rest })
  | [] =>
    match chachaBlock r.key r.ctr with
    | w :: rest => (w, { r with ctr := r.ctr + 1, buf := rest })
    | [] => (0, r) -- unreachable: a block has 16 words

/-- `u32` leading zeros of `n` (`n < 2³²`). -/
def lz32 (n : Nat) : Nat := 32 - n.log2 - 1

/-- `gen_range(0..n as u32)`, `1 ≤ n < 2³²`, with `fuel` draws. -/
def genIndex : Nat → Nat → Rng → Option (Nat × Rng)
  | 0, _, _ => none
  | fuel + 1, n, r =>
    let zone := ((n <<< lz32 n) % M32 + M32 - 1) % M32
    let (v, r) := r.nextU32
    let m := v * n
    if m % M32 ≤ zone then some (m / M32, r) else genIndex fuel n r

def swapAt {α : Type} (l : List α) (i j : Nat) : List α :=
  match l[i]?, l[j]? with
  | some a, some b => (l.set i b).set j a
  | _, _ => l

/-- `SliceRandom::shuffle`: `for i in (1..len).rev() { swap(i, gen_index(i+1)) }`. -/
def shuffleLoop {α : Type} : Nat → List α → Rng → Option (List α × Rng)
  | 0, l, r => some (l, r)
  | i + 1, l, r =>
    match genIndex 64 (i + 2) r with
    | none => none
    | some (j, r) => shuffleLoop i (swapAt l (i + 1) j) r

/-- Shuffle `l` with `r`; returns the permuted list and the advanced RNG. -/
def shuffle {α : Type} (l : List α) (r : Rng) : Option (List α × Rng) :=
  shuffleLoop (l.length - 1) l r

/-- nearcore `shuffle_receipt_proofs(l, salt)`: fresh RNG seeded with `salt`. -/
def shuffleWithSeed {α : Type} (l : List α) (seed : List UInt8) : Option (List α) :=
  (shuffle l (Rng.ofSeed seed)).map Prod.fst

end NearSpecV3
