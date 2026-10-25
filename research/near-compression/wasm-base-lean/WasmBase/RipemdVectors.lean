import WasmBase.RipemdAir
import NearSpecV3.Wasm.Crypto
/-!
# WasmBase.RipemdVectors — the RIPEMD-160 step equations against the spec, kernel out of the loop

`WasmBase.RipemdAir` defines the step row; `formBit_is_spec` pins the five `f` forms to
`NearSpecV3.Wasm.Crypto.rf` on all bit triples, and `majE_is_carry` pins the adder's carry.  What that
leaves open is the *composition*: do the adder chain, the selector-gated message word, the
selector-gated rotation and the shift, taken together, compute the spec's step?  It cannot be a
`decide` — the spec's `ripemd160` is `Id.run` over `while`/`for`, so the kernel cannot reduce it.

So the test is compiled (the `KeccakVectors` pattern):

1. **`genRow st x j`** — fill every column of a `RIPEMD160` row **from the step's own equations**:
   `f` from the spec's `rf`, the selected word from `rl`/`rr`, the chained sums from `kl`/`kr`, the
   rotation from `sl`/`sr`, the carries from the ripple addition, `sel` one-hot at `j`.  Nothing is
   copied from the constraint list.
2. **`nxtState cur`** — the row's `nxt` columns, **defined by the shift equations alone** (read the
   row's own `el`, `t3`, `bl`, `rotl cl 10`, `dl`).  So the traced state is read out of the AIR's
   columns, not out of the generator's variables.
3. **`rowOk`** — evaluate all 2,625 constraints on the row and require every one to vanish in `Fp`.
4. **`tampers`** — flip one column and require `rowOk` to fail, so a constraint list that collapsed
   to `0 = 0` could not pass.
5. **`airDigest`** — 80 rows per block chained through `nxtState`, then the spec's feed-forward
   (`Crypto.lean:134-135`) and little-endian output (`:136-138`); compare with
   `NearSpecV3.Wasm.Crypto.ripemd160`, plus the published RIPEMD-160("") known answer as the leg
   that does not go through the spec's own code.

`#eval` runs all of it at build time and **fails the build**: a regression in the table, the
generator or an index fact stops `lake build` instead of printing.
-/
set_option maxRecDepth 1000000

namespace WasmBase
namespace Chips
namespace Ripemd

open NearSpecV3.Wasm.Crypto

/-! ## Word arithmetic at the generator's level

The spec works in `UInt32`; the generator works in `Nat` mod 2³² so the bit decomposition is
explicit.  `rotl32n x n` writes `rot32 x n` (`Crypto.lean:108`) as the wiring the AIR's `rotAux`
constrains: bit `k` of the result is bit `(k + 32 − n) mod 32` of `x`. -/

def mod32 (x : Nat) : Nat := x % 4294967296
def add32 (a b : Nat) : Nat := mod32 (a + b)

/-- `rotl32 x n` as a Nat, by the index map (no shift primitive). -/
def rotl32n (x n : Nat) : Nat :=
  (List.range 32).foldl (fun acc k => acc + bitOf x ((k + 32 - n % 32) % 32) * 2 ^ k) 0

/-- `rotl32n` **is** the spec's `rot32`, on every offset the table uses and a spread of values. -/
theorem rotl32n_is_rot :
    (List.range 80).all (fun j => (List.range 8).all (fun i =>
      let v := i * 0x1234567 + 0x89ABCDEF
      rotl32n v (slVal j) == (rot32 (UInt32.ofNat v) (UInt32.ofNat (slVal j))).toNat
      && rotl32n v (srVal j) == (rot32 (UInt32.ofNat v) (UInt32.ofNat (srVal j))).toNat)) = true := by
  decide

/-- The spec's `rf` at step `j`, as a natural. -/
def rfNat (j b c d : Nat) : Nat :=
  (rf j (UInt32.ofNat b) (UInt32.ofNat c) (UInt32.ofNat d)).toNat

/-! ## Reading and writing the state's ten words -/

/-- The state as the AIR orders it: `al bl cl dl el ar br cr dr er`. -/
abbrev St10 := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

def stWord (st : St10) (w : Nat) : Nat :=
  match w with
  | 0 => st.1
  | 1 => st.2.1
  | 2 => st.2.2.1
  | 3 => st.2.2.2.1
  | 4 => st.2.2.2.2.1
  | 5 => st.2.2.2.2.2.1
  | 6 => st.2.2.2.2.2.2.1
  | 7 => st.2.2.2.2.2.2.2.1
  | 8 => st.2.2.2.2.2.2.2.2.1
  | _ => st.2.2.2.2.2.2.2.2.2

/-- Column of state word `w` bit `k`: words `0..4` are the `L` group, `5..9` the `R` group. -/
def swCol (w k : Nat) : Nat := if w < 5 then lBit w k else rBit (w - 5) k

/-- **Read a state out of a row's columns** (the AIR's own layout). -/
def stateOf (f : Nat → Nat) : St10 :=
  ((List.range 32).foldl (fun a k => a + f (swCol 0 k) * 2 ^ k) 0,
   (List.range 32).foldl (fun a k => a + f (swCol 1 k) * 2 ^ k) 0,
   (List.range 32).foldl (fun a k => a + f (swCol 2 k) * 2 ^ k) 0,
   (List.range 32).foldl (fun a k => a + f (swCol 3 k) * 2 ^ k) 0,
   (List.range 32).foldl (fun a k => a + f (swCol 4 k) * 2 ^ k) 0,
   (List.range 32).foldl (fun a k => a + f (swCol 5 k) * 2 ^ k) 0,
   (List.range 32).foldl (fun a k => a + f (swCol 6 k) * 2 ^ k) 0,
   (List.range 32).foldl (fun a k => a + f (swCol 7 k) * 2 ^ k) 0,
   (List.range 32).foldl (fun a k => a + f (swCol 8 k) * 2 ^ k) 0,
   (List.range 32).foldl (fun a k => a + f (swCol 9 k) * 2 ^ k) 0)

/-! ## The row's columns, from the step's equations -/

/-- The carry bits of `x + y` over 32 bits: entry `k` is the carry **out** of bit `k`. -/
def carries (x y : Nat) : List Nat :=
  (List.range 31).foldl (fun (acc : List Nat × Nat) k =>
      let cyOut := (bitOf x k + bitOf y k + acc.2) / 2
      (acc.1 ++ [cyOut], cyOut)) ([], 0) |>.1

/-- The ten carry lists of a row, in the `cy` group's order. -/
def allCarries (al fl t0 xl t1 kl rot el ar fr t4 xr t5 kr rotR er : Nat) : List (List Nat) :=
  [carries al fl, carries t0 xl, carries t1 kl, carries rot el,
   carries ar fr, carries t4 xr, carries t5 kr, carries rotR er]

/-- **The row's `cur` columns, from the step's equations.** -/
def genRow (st : St10) (x : Array Nat) (j : Nat) : Nat → Nat := fun c =>
  let g := j / 16
  let al := stWord st 0; let bl := stWord st 1; let cl := stWord st 2
  let dl := stWord st 3; let el := stWord st 4
  let ar := stWord st 5; let br := stWord st 6; let cr := stWord st 7
  let dr := stWord st 8; let er := stWord st 9
  let fl := rfNat j bl cl dl
  let fr := rfNat (79 - j) br cr dr
  let xl := x.getD (rlVal j) 0
  let xr := x.getD (rrVal j) 0
  let kl := klVal g; let kr := krVal g
  let t0 := add32 al fl
  let t1 := add32 t0 xl
  let t2 := add32 t1 kl
  let rotL := rotl32n t2 (slVal j)
  let t3 := add32 rotL el
  let t4 := add32 ar fr
  let t5 := add32 t4 xr
  let t6 := add32 t5 kr
  let rotR := rotl32n t6 (srVal j)
  let t7 := add32 rotR er
  let cys := allCarries al fl t0 xl t1 kl rotL el ar fr t4 xr t5 kr rotR er
  if c < rC then bitOf (stWord st (c / W)) (c % W)
  else if c < xC then bitOf (stWord st (5 + (c - rC) / W)) ((c - rC) % W)
  else if c < xC + W * NWORDS then bitOf (x.getD ((c - xC) / W) 0) ((c - xC) % W)
  else if c < flC + W then bitOf fl (c - flC)
  else if c < frC + W then bitOf fr (c - frC)
  else if c < xlC + W then bitOf xl (c - xlC)
  else if c < xrC + W then bitOf xr (c - xrC)
  else if c < tC + W * 8 then
    bitOf ([t0, t1, t2, t3, t4, t5, t6, t7].getD ((c - tC) / W) 0) ((c - tC) % W)
  else if c < rotC + W * 2 then
    bitOf (if (c - rotC) / W = 0 then rotL else rotR) ((c - rotC) % W)
  else if c < cyC + 31 * 8 then
    (cys.getD ((c - cyC) / 31) []).getD ((c - cyC) % 31) 0
  else if c = selC + j then 1 else 0

/-- **The row's `nxt` columns, from the shift equations alone** (`RipemdAir.shiftConstraints`):
`al' = el`, `bl' = tf`, `cl' = bl`, `dl' = rotl32 cl 10`, `el' = dl`; mirrored on the right.  Reading
the state back through this function is what makes the digest a property of the AIR's columns. -/
def nxtState (cur : Nat → Nat) : Nat → Nat := fun c =>
  if c < rC then
    let w := c / W; let k := c % W
    if w = 0 then cur (lBit 4 k)
    else if w = 1 then cur (tBit 3 k)
    else if w = 2 then cur (lBit 1 k)
    else if w = 3 then cur (lBit 2 ((k + W - 10) % W))
    else cur (lBit 3 k)
  else if c < xC then
    let w := (c - rC) / W; let k := (c - rC) % W
    if w = 0 then cur (rBit 4 k)
    else if w = 1 then cur (tBit 7 k)
    else if w = 2 then cur (rBit 1 k)
    else if w = 3 then cur (rBit 2 ((k + W - 10) % W))
    else cur (rBit 3 k)
  else 0

/-! ## Satisfiability, and the check's teeth -/

def mkRow (cur nxt : Nat → Nat) : Row :=
  ⟨fun i => ((cur i : Nat) : F), fun i => ((nxt i : Nat) : F), fun _ => 0, false, false⟩

def rowOk' (cur nxt : Nat → Nat) : Bool :=
  constraints.all (fun e => e.eval (mkRow cur nxt) == 0)

def rowOk (st : St10) (x : Array Nat) (j : Nat) : Bool :=
  rowOk' (genRow st x j) (nxtState (genRow st x j))

/-- Flip column `c` (a bit) in a row. -/
def flipCol (f : Nat → Nat) (c : Nat) : Nat → Nat := fun i => if i = c then 1 - f i else f i

/-- The initial chaining value (`Crypto.lean:122`). -/
def iv : St10 := (0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0,
                  0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0)

def sampleX : Array Nat := Array.ofFn (n := 16) fun i => (0x01234567 * (i.val + 1) + 0x89ABCDEF) % 4294967296

def sampleStates : List (String × St10) :=
  [("iv", iv),
   ("zero", (0, 0, 0, 0, 0, 0, 0, 0, 0, 0)),
   ("ones", (4294967295, 4294967295, 4294967295, 4294967295, 4294967295,
             4294967295, 4294967295, 4294967295, 4294967295, 4294967295)),
   ("mixed", (4294967295, 2147483648, 2147483647, 1, 0, 0, 1, 0xDEADBEEF, 0xCAFEBABE, 0x12345678))]

def rowOkSample : List (String × Bool) :=
  sampleStates.flatMap fun (nm, st) =>
    (List.range 80).map fun j => (s!"{nm} j{j}", rowOk st sampleX j)

/-- Every single-column flip **of a constrained column** must be rejected.  A constraint list that
had degenerated to `0 = 0` (or a generator that hard-coded the expected value) would let one
through.  The message words `X` are deliberately *not* here — see `freeInputs`. -/
def tampers : List (String × Bool) :=
  let st : St10 := iv
  let cur := genRow st sampleX 0
  let nx := nxtState cur
  let cases : List (String × Nat) :=
    [("fL0", flBit 0), ("fR0", frBit 0), ("xL0", xlBit 0), ("xR0", xrBit 0),
     ("rotL0", rotBit 0 0), ("rotR0", rotBit 1 0), ("t0_0", tBit 0 0), ("t3_0", tBit 3 0),
     ("t7_0", tBit 7 0), ("cy0_0", cyBit 0 0), ("cy7_30", cyBit 7 30),
     ("al0", lBit 0 0), ("er31", rBit 4 31),
     ("selSwap", selE 1), ("selOff", selE 0),
     -- the two message words step 0 actually selects (`rl[0] = 0`, `rr[0] = 5`)
     ("XselL", xBit 0 0), ("XselR", xBit 5 31)]
  cases.map fun (nm, c) => (nm, rowOk' (flipCol cur c) nx)

def tampersRejected : Bool := tampers.all fun (_, stillOk) => !stillOk

/-- **A named gap, not a bug.**  A message word that step `j` does not select is a *free row input*:
flipping it leaves every constraint of row `j` satisfied, because the AIR's only link from the block
to the row is `xselConstr`, which reads just the selected word.  The AIR therefore proves "the digest
follows from the message columns", not "the message columns are the padded block" — the second half
is the `HOSTB → MEMIO` binding, which this AIR does not carry (`inters = []`).  These two flips are
expected to stay satisfied, and asserting that keeps the gap visible instead of silently absent. -/
def freeInputs : List (String × Bool) :=
  let st : St10 := iv
  let cur := genRow st sampleX 0
  let nx := nxtState cur
  [("X15_31", rowOk' (flipCol cur (xBit 15 31)) nx),
   ("X9_0", rowOk' (flipCol cur (xBit 9 0)) nx)]

def freeInputsStillOk : Bool := freeInputs.all fun (_, stillOk) => stillOk

/-! ## The digest, read out of the AIR's columns

Per block: 80 rows chained through `nxtState`; then the spec's feed-forward
(`Crypto.lean:134-135`) on the final working variables; then little-endian output (`:136-138`),
which is what a joined proof's `regSetH reg d` receives. -/

def runBlock (st : St10) (x : Array Nat) : St10 :=
  (List.range 80).foldl (fun s j => stateOf (nxtState (genRow s x j))) st

/-- **Both lines start from the same five words.**  `Crypto.lean:127-128` initialises
`ar br cr dr er := h[0..4]`, i.e. the AIR's ten columns are the chaining value written twice.
The row family is one *compression*, so this is also how each new block restarts. -/
def bothLines (h : St10) : St10 :=
  (stWord h 0, stWord h 1, stWord h 2, stWord h 3, stWord h 4,
   stWord h 0, stWord h 1, stWord h 2, stWord h 3, stWord h 4)

def feedForward (h st : St10) : St10 :=
  bothLines
    ((add32 (add32 (stWord h 1) (stWord st 2)) (stWord st 8),
      add32 (add32 (stWord h 2) (stWord st 3)) (stWord st 9),
      add32 (add32 (stWord h 3) (stWord st 4)) (stWord st 5),
      add32 (add32 (stWord h 4) (stWord st 0)) (stWord st 6),
      add32 (add32 (stWord h 0) (stWord st 1)) (stWord st 7), 0, 0, 0, 0, 0))

def padBytes (m : ByteArray) : ByteArray := Id.run do
  let bitLen := 8 * m.size
  let mut p := m.push 0x80
  while p.size % 64 ≠ 56 do p := p.push 0
  for i in [0:8] do p := p.push (UInt8.ofNat ((bitLen / 256 ^ i) % 256))
  p

def blockWords (p : ByteArray) (blk : Nat) : Array Nat :=
  Array.ofFn (n := 16) fun i =>
    (p.get! (blk * 64 + 4 * i.val)).toNat
    ||| ((p.get! (blk * 64 + 4 * i.val + 1)).toNat <<< 8)
    ||| ((p.get! (blk * 64 + 4 * i.val + 2)).toNat <<< 16)
    ||| ((p.get! (blk * 64 + 4 * i.val + 3)).toNat <<< 24)

/-- **The AIR's digest**: per block, 80 rows chained through the shift wiring from the ten-word start
state, then the feed-forward; the next block restarts from the five-word result on **both** lines. -/
def airDigest (m : List UInt8) : List Nat := Id.run do
  let b := padBytes ⟨m.toArray⟩
  let mut h := bothLines iv
  for blk in [0:b.size / 64] do
    h := feedForward h (runBlock h (blockWords b blk))
  return (List.range 5).flatMap fun w => (List.range 4).map fun k => stWord h w >>> (8 * k) % 256

def specDigest (m : List UInt8) : List Nat :=
  (ripemd160 ⟨m.toArray⟩).toList.map (·.toNat)

def padInput (n : Nat) : List UInt8 := (List.range n).map (fun i => UInt8.ofNat (i % 256))

def testVectors : List (String × List UInt8) :=
  [("0", padInput 0), ("1", padInput 1), ("abc", [97, 98, 99]), ("3", padInput 3),
   ("55", padInput 55), ("56", padInput 56), ("63", padInput 63), ("64", padInput 64),
   ("65", padInput 65), ("100", padInput 100), ("119", padInput 119), ("120", padInput 120),
   ("200", padInput 200)]

def diffs : List String :=
  testVectors.filterMap fun (nm, m) =>
    if airDigest m == specDigest m then none else some s!"{nm}: AIR {airDigest m} ≠ spec {specDigest m}"

/-- RIPEMD-160("") from the published test vectors.  The one leg that does *not* go through the
spec's own code, so it catches a shared bug between generator and spec (wrong IV, wrong byte order). -/
def emptyKat : List Nat :=
  [0x9c, 0x11, 0x85, 0xa5, 0xc5, 0xe9, 0xfc, 0x54, 0x61, 0x28, 0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48,
   0xb2, 0x25, 0x8d, 0x31]

/-- RIPEMD-160("abc") from the published test vectors. -/
def abcKat : List Nat :=
  [0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b, 0x04, 0x4a, 0x8e, 0x98, 0xc6, 0xb0, 0x87,
   0xf1, 0x5a, 0x0b, 0xfc]

def katOk : Bool :=
  airDigest [] == emptyKat ∧ specDigest [] == emptyKat ∧
  airDigest [97, 98, 99] == abcKat ∧ specDigest [97, 98, 99] == abcKat

/-! ## Build guard

Compiled, not kernel-reduced (one row is 2,625 constraint evaluations, and the selector sums are 80
terms each).  The differential runs at build time and **fails the build**. -/

#eval (do
  let fs := diffs
  let bad := rowOkSample.filterMap fun (nm, ok) => if ok then none else some nm
  let tampered := tampers.filterMap fun (nm, stillOk) => if stillOk then some nm else none
  let leaked := freeInputs.filterMap fun (nm, stillOk) => if stillOk then none else some nm
  let msg :=
    if fs.isEmpty && bad.isEmpty && tampered.isEmpty && leaked.isEmpty && katOk then
      s!"RipemdVectors: {rowOkSample.length} rows satisfy all {constraints.length} constraints, \
        {tampers.length} tampers rejected, {testVectors.length} digests == spec, \
        {freeInputs.length} message-columns confirmed free (named gap), RIPEMD-160 KATs ok"
    else
      s!"RipemdVectors: FAILED rows {bad} digests {fs} tampers {tampered} \
        freeInputsNowConstrained {leaked} kat {katOk}"
  IO.println msg
  if !(fs.isEmpty && bad.isEmpty && tampered.isEmpty && leaked.isEmpty && katOk) then
    IO.Process.exit 1)
