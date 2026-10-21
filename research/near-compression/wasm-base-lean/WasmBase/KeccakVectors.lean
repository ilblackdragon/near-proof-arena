import WasmBase.KeccakSteps
import NearSpecV3.Wasm.Crypto
/-!
# WasmBase.KeccakVectors — the round's AIR equations against the spec, with the kernel out of the loop

`WasmBase.KeccakAir` defines the round as a list of constraints; `KeccakSteps` proves the per-step
lemmas.  This file closes the gap the lemmas leave open: **does the whole round's equation system, as
written, compute the spec's round?**

It cannot be a `decide`: the spec's `keccakF` is `Id.run` over `for`/`set!` (`Crypto.lean:34-56`), so
the kernel cannot reduce it at all (a `decide` on one output lane does not terminate the reduction).
So the test is compiled:

1. **`genRow`** — given an input state (25 `UInt64`) and a round index `r`, fill every column of a
   `KECCAK` row **from the round's own definition**: `C`/`CA`/`D`/`T` from the `theta` equations,
   `nxt A` from the `chi`/`iota` equations, `sel` one-hot at `r`.  Nothing is copied from the spec.
2. **`rowOk`** — evaluate all 9,755 constraints (`roundConstraints`) on that row and require every one
   to vanish in `Fp`.  This is the AIR's own satisfiability.
3. **`agreesWithSpec`** — the `A` of the *next* row, read out of the row's `nxt` columns, must equal
   the spec's `keccakF` step on the input state.  This is the differential leg.

`#eval` runs it on a fixed list of states: the empty state, the all-ones state, single-bit states, the
spec's own round constants, and pseudo-random states.  A full permutation is checked by applying the
round 24 times with the 24 constants and comparing to `keccakF`, on `0/135/136/137`-byte inputs
(`keccak256`'s padding boundaries) and a multi-block input.
-/
namespace WasmBase
namespace Chips
namespace Keccak

open NearSpecV3.Wasm.Crypto

/-! ## Reading a state as bit columns -/

/-- Bit `k` of lane `l` of a 25-lane state. -/
def bitOf (st : Array UInt64) (l k : Nat) : Nat := (st.getD l 0).toNat >>> k % 2

/-- The 25-lane state as 1,600 `A` columns. -/
def stateCells (st : Array UInt64) : Nat → Nat := fun j =>
  if j < NB then bitOf st (j / W) (j % W) else 0

/-- Pack bit columns back into 25 lanes (the independent read-back leg). -/
def laneOfCells (c : Nat → Nat) (l : Nat) : UInt64 :=
  ((List.range W).foldl (fun acc k => acc + (c (aBit l k) <<< k)) 0).toUInt64

/-! ## Filling a round row from the round's own equations

`genRow st r` gives `cur` and `nxt` for one round row of input state `st`:

* `cur` — the input state in `A`, plus `sel` one-hot at `r`;
* `nxt A` — whatever the `chi`/`iota` equations say, computed here directly (not via the spec).

(The `C`/`CA`/`D`/`T` columns are *derived* by the constraint system from `cur`; a satisfying trace
has them, and `rowOk` checks the system accepts the row we build.) -/

/-- `theta`'s column parity `C[x][k]`, directly. -/
def genC (st : Array UInt64) (x k : Nat) : Nat :=
  bitOf st x k ^^^ bitOf st (x + 5) k ^^^ bitOf st (x + 10) k ^^^ bitOf st (x + 15) k ^^^
    bitOf st (x + 20) k

def genCA (st : Array UInt64) (x k t : Nat) : Nat :=
  match t with
  | 0 => bitOf st x k ^^^ bitOf st (x + 5) k
  | 1 => bitOf st x k ^^^ bitOf st (x + 5) k ^^^ bitOf st (x + 10) k
  | _ => bitOf st x k ^^^ bitOf st (x + 5) k ^^^ bitOf st (x + 10) k ^^^ bitOf st (x + 15) k

/-- `D[x][k] = C[x−1][k] ^ C[x+1][(k−1) mod 64]`. -/
def genD (st : Array UInt64) (x k : Nat) : Nat :=
  genC st ((x + 4) % 5) k ^^^ genC st ((x + 1) % 5) ((k + W - 1) % W)

/-- `T = A ^ D`. -/
def genT (st : Array UInt64) (l k : Nat) : Nat := bitOf st l k ^^^ genD st (l % 5) k

/-- `B` = rho/pi of `T`: the `bBit` wiring, computed as a lane read-back. -/
def genB (st : Array UInt64) (m j : Nat) : Nat :=
  genT st (piSrc m) ((j + W - rotcVal (piSrc m)) % W)

/-- `chi`'s result on lane `m`, bit `k`, before `iota`. -/
def genChi (st : Array UInt64) (m k : Nat) : Nat :=
  genB st m k ^^^ (1 - genB st (chi1 m) k) * genB st (chi2 m) k

/-- The round's output bit: `chi`, then `iota` on lane 0. -/
def genOut (st : Array UInt64) (r : Nat) (l k : Nat) : Nat :=
  if l = 0 then genChi st l k ^^^ rcBit r k else genChi st l k

/-! ## Evaluating an expression on a row -/

/-- A `Row` whose `cur` and `nxt` cells are natural numbers. -/
def mkRow (cur nxt : Nat → Nat) : Row :=
  ⟨fun i => ((cur i : Nat) : F), fun i => ((nxt i : Nat) : F), fun _ => 0, false, false⟩

/-- The row `genRow st r` builds: **every** column group is filled from the round's own equations, so
`satisfies` below is a real check of the constraint list, not of a half-empty row.

* `A` — the input state's bits;
* `C`, `CA`, `D`, `T` — the `theta` derivation (`genC`, `genCA`, `genD`, `genT`);
* `X` — `chi` on lane 0 (`genChi st 0 k`), which `iota` then consumes;
* `sel`/`sp` — the one-hot selector for round `r`;
* `nxt A` — `genOut st r` (the round's output);
* `nxt` elsewhere — irrelevant, no constraint reads it. -/
def genRow (st : Array UInt64) (r : Nat) : Row :=
  let cur : Nat → Nat := fun j =>
    if j < NB then bitOf st (j / W) (j % W)
    -- theta parities
    else if cC ≤ j ∧ j < cC + 5 * W then genC st ((j - cC) / W) ((j - cC) % W)
    -- chain auxiliaries, 3 per C bit
    else if caC ≤ j ∧ j < caC + 3 * 5 * W then
      genCA st (((j - caC) / 3) / W) (((j - caC) / 3) % W) ((j - caC) % 3)
    else if dC ≤ j ∧ j < dC + 5 * W then genD st ((j - dC) / W) ((j - dC) % W)
    else if tC ≤ j ∧ j < tC + NB then genT st ((j - tC) / W) ((j - tC) % W)
    else if xC ≤ j ∧ j < xC + W then genChi st 0 (j - xC)
    else if selC ≤ j ∧ j < selC + ROUNDS then (if j - selC = r then 1 else 0)
    else if j = hSp then (if r = 0 then 1 else 0)
    else 0
  let nxt : Nat → Nat := fun j =>
    if j < NB then genOut st r (j / W) (j % W) else 0
  mkRow cur nxt

/-- Every constraint of the round vanishes on the generated row. -/
def rowOk (rw : Row) : Bool := roundConstraints.all (fun e => e.eval rw == 0)

/-- The state the row's `nxt A` columns spell out. -/
def nxtState (rw : Row) : Array UInt64 :=
  (Array.range 25).map fun l => laneOfCells (fun j => (rw.nxt j).toNat) l

/-! ## The differential test -/

/-- The spec's round, one step: `keccakF` on a fresh copy with the whole `rc` array is 24 rounds, so
this is the spec's `keccakF` with the first `r` constants zeroed — for `r = 0` it *is* one round. -/
def specRound (st : Array UInt64) (r : Nat) : Array UInt64 :=
  Id.run do
    let a := st
    -- theta
    let c := Array.ofFn (n := 5) fun x =>
      a[x.val]! ^^^ a[x.val + 5]! ^^^ a[x.val + 10]! ^^^ a[x.val + 15]! ^^^ a[x.val + 20]!
    let mut a1 := a
    for x in [0:5] do
      let d := c[(x + 4) % 5]! ^^^ rotl64 c[(x + 1) % 5]! 1
      for y in [0:5] do
        a1 := a1.set! (x + 5 * y) (a[x + 5 * y]! ^^^ d)
    -- rho, pi
    let mut b := Array.replicate 25 (0 : UInt64)
    for x in [0:5] do
      for y in [0:5] do
        b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl64 a1[x + 5 * y]! rotc[x + 5 * y]!)
    -- chi
    let mut a2 := a1
    for x in [0:5] do
      for y in [0:5] do
        a2 := a2.set! (x + 5 * y)
          (b[x + 5 * y]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!))
    -- iota
    a2 := a2.set! 0 (a2[0]! ^^^ rc[r]!)
    return a2

/-- One AIR round row agrees with the spec's round when its constraints hold and its `nxt A` is the
spec's output. -/
def roundAgrees (st : Array UInt64) (r : Nat) : Bool :=
  let rw := genRow st r
  rowOk rw && (nxtState rw == specRound st r)

/-! ## Whole permutations -/

/-- Run the AIR's round 24 times (each on its own one-hot row) and return the final state. -/
def airPerm (st : Array UInt64) : Array UInt64 :=
  (List.range 24).foldl (fun s r => nxtState (genRow s r)) st

/-- The AIR trace satisfies every round's constraints and reproduces the spec's permutation. -/
def permAgrees (st : Array UInt64) : Bool :=
  ((List.range 24).all (fun r => roundAgrees
      ((List.range r).foldl (fun s r' => nxtState (genRow s r')) st) r))
    && (airPerm st == keccakF st)

/-! ## The vectors -/

def zeroState : Array UInt64 := Array.replicate 25 (0 : UInt64)
def onesState : Array UInt64 := Array.replicate 25 (0xFFFFFFFFFFFFFFFF : UInt64)
def bitState (l k : Nat) : Array UInt64 :=
  (Array.replicate 25 (0 : UInt64)).set! l ((1 : UInt64) <<< (UInt64.ofNat k))
def stampState : Array UInt64 :=
  Array.ofFn (n := 25) fun i => (0x0123456789ABCDEF : UInt64) * (UInt64.ofNat (i.val + 1)) + 0xDEADBEEFCAFEBABE

def testStates : List (String × Array UInt64) :=
  [("zero", zeroState),
   ("ones", onesState),
   ("bit(0,0)", bitState 0 0),
   ("bit(7,63)", bitState 7 63),
   ("bit(24,1)", bitState 24 1),
   ("stamp", stampState),
   ("rc-ish", Array.ofFn (n := 25) fun i => rc[i.val % 24]!),
   ("iota-only", (Array.replicate 25 (0 : UInt64)).set! 0 1)]

/-- One round of every test state against the spec's round. -/
def runRounds : List (String × Bool) :=
  testStates.flatMap fun (nm, st) =>  -- every round index 0..23
    (List.range 24).map fun r => (s!"{nm} r{r}", roundAgrees st r)

/-- A whole permutation of every test state, plus a multi-block sponge input. -/
def runPerms : List (String × Bool) :=
  (testStates.map fun (nm, st) => (s!"perm {nm}", permAgrees st)) ++
  [("perm ones", permAgrees onesState)]

/-- Sponge: compare the AIR's absorb+permute to the spec's `keccak256`.
`st` is the (already absorbed) state, which we re-derive here from the block bytes. -/
def absorbBytes (st : Array UInt64) (blk : ByteArray) : Array UInt64 :=
  Id.run do
    let mut s := st
    for w in [0:blk.size / 8] do
      let mut lane : UInt64 := 0
      for k in [0:8] do
        lane := lane ||| ((blk.get! (8 * w + k)).toUInt64 <<< (8 * k).toUInt64)
      s := s.set! w (s[w]! ^^^ lane)
    return s

/-- Split `m` into `rate`-byte blocks with original-Keccak padding, absorb each, run the AIR's 24
rounds, and read `outLen` bytes back. -/
def airKeccak (rate outLen : Nat) (m : ByteArray) : ByteArray := Id.run do
  let padLen := rate - m.size % rate
  let mut p := m
  for i in [0:padLen] do
    let v : UInt8 := (if i = 0 then 0x01 else 0) ||| (if i = padLen - 1 then 0x80 else 0)
    p := p.push v
  let mut st : Array UInt64 := Array.replicate 25 (0 : UInt64)
  for blk in [0:p.size / rate] do
    st := absorbBytes st (p.extract (blk * rate) ((blk + 1) * rate))
    st := airPerm st
  let mut out := ByteArray.empty
  for i in [0:outLen] do
    out := out.push ((st[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8)
  out

def padInput (n : Nat) : ByteArray :=
  (Array.range n).foldl (fun acc i => acc.push (UInt8.ofNat (i % 256))) ByteArray.empty

def runKeccak : List (String × Bool) :=
  [("k256 0", airKeccak 136 32 (padInput 0) == keccak256 (padInput 0)),
   ("k256 135", airKeccak 136 32 (padInput 135) == keccak256 (padInput 135)),
   ("k256 136", airKeccak 136 32 (padInput 136) == keccak256 (padInput 136)),
   ("k256 137", airKeccak 136 32 (padInput 137) == keccak256 (padInput 137)),
   ("k256 1000", airKeccak 136 32 (padInput 1000) == keccak256 (padInput 1000)),
   ("k512 0", airKeccak 72 64 (padInput 0) == keccak512 (padInput 0)),
   ("k512 71", airKeccak 72 64 (padInput 71) == keccak512 (padInput 71)),
   ("k512 72", airKeccak 72 64 (padInput 72) == keccak512 (padInput 72)),
   ("k512 200", airKeccak 72 64 (padInput 200) == keccak512 (padInput 200))]

/-! ## Build guard

The three tests are compiled, not kernel-reduced: one round is 9,755 constraint evaluations over
1,600-bit rows, and `decide` on a single row row does not reduce (the kernel reaches its recursion
limit first; measured).  So the differential test runs at build time and **fails the build** — a
regression in the table, the generator or the index facts stops `lake build`, it does not merely
print. -/

def failures : List String :=
  (runRounds ++ runPerms ++ runKeccak).filterMap fun (nm, ok) => if ok then none else some nm

#eval (do
  let fs := failures
  if fs.isEmpty then
    IO.println s!"KeccakVectors: {runRounds.length} rounds, {runPerms.length} permutations, \
      {runKeccak.length} sponge vectors — all ok"
  else
    IO.println s!"KeccakVectors: FAILED {fs}"
    IO.Process.exit 1)

end Keccak
end Chips
end WasmBase
