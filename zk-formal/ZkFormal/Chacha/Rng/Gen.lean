import ZkFormal.Chacha.Rng.Sound
import ZkFormal.Chacha.Gen

/-!
# ZkFormal.Chacha.Rng.Gen — the honest trace of the stream / `gen_index` table `genV3`

One call `(key, kstart, n)` is `gen_index(n)` on the stream of `key` from position `kstart`
(`genAt 64 n key kstart = some (j, kend)`).  It is laid out as `nd C = kend − kstart` draw rows
`d = 0 … nd−1` (stream word `k = kstart + d`; all rejected but the last), calls in list
order, then all-zero padding up to `2^honestLog` rows.

Every honest cell is a `Nat < 2^30` (`kstart < kend < 2^30` by `CallOk`), so the field
embedding `Fp.ofNat` is injective on honest cells.  The cell formulas below are the
specification of a Rust trace generator, column by column (layout in
ZkFormal.Chacha.Rng.Table):

| columns | value on draw row `d` of call `C` (`k = kstart + d`, `v = streamWord key k`) |
|---|---|
| `K j l = 2j+l` | limb `l` of `key[j]` |
| `16` | `ctr = k / 16` |
| `17 + b` | bit `b` of `k % 16` |
| `21, 22` | `vlo = v % 2^16`, `vhi = v / 2^16` |
| `23 + b` | bit `b` of `n` |
| `37 + i` | `[i = log2 n]` |
| `51+b`, `67+b`, `81+b`, `97+b` | bits of `m0 = (vlo·n) % 2^16`, `c0 = vlo·n / 2^16`, `m1 = (vhi·n + c0) % 2^16`, `m2 = (vhi·n + c0) / 2^16` |
| `111 + b` | bits of `δ = Z−1−m1` (last row) / `m1−Z` (other rows), `Z = n·2^(15−log2 n)` |
| `127, 128, 129` | `acc = [d = nd−1]`, `st = [d = 0]`, `a = 1` |
| `130 + b` | bit `b` of `d` |
| `136` | `kstart` |

Padding rows are all zero.
-/

namespace ZkFormal.Chacha.Rng.Gen

open NearSpecV3 ZkFormal.Chacha

/-- One `gen_index(n)` call on the stream of `key`, starting at stream position `kstart`. -/
structure Call where
  key : List Nat
  kstart : Nat
  n : Nat

/-- Calls the generator supports: a ChaCha key, `1 ≤ n < 2^14`, the call succeeds within
64 draws and stream positions stay `< 2^30` (so `ctr < 2^26`). -/
def CallOk (C : Call) : Prop :=
  C.key.length = 8 ∧ (∀ x ∈ C.key, x < 2 ^ 32) ∧ 1 ≤ C.n ∧ C.n < 2 ^ 14 ∧
    ∃ j kend, genAt 64 C.n C.key C.kstart = some (j, kend) ∧ kend < 2 ^ 30

/-- `(j, kend)` of the call (a default if it fails, never used for supported calls). -/
def result (C : Call) : Nat × Nat := (genAt 64 C.n C.key C.kstart).getD (0, C.kstart + 1)

/-- Number of draws of the call. -/
def nd (C : Call) : Nat := (result C).2 - C.kstart

/-- Row descriptors: draw `d` of call `C`, or padding. -/
inductive Row where
  | draw (C : Call) (d : Nat)
  | pad

/-! ## Cell values -/

/-- 16-bit limb `l` of `x`. -/
def limbN (x l : Nat) : Nat := x / 2 ^ (16 * l) % 65536

/-- Leading bit position of `n`. -/
def topBit (n : Nat) : Nat := n.log2

/-- `Z = n·2^(15 − topBit n)` (the Lemire zone is `2^16·Z − 1`). -/
def zOf (n : Nat) : Nat := n * 2 ^ (15 - topBit n)

/-- Stream position of draw `d`. -/
def kOf (C : Call) (d : Nat) : Nat := C.kstart + d
/-- The drawn word. -/
def vOf (C : Call) (d : Nat) : Nat := streamWord C.key (kOf C d)
def vlo (C : Call) (d : Nat) : Nat := vOf C d % 65536
def vhi (C : Call) (d : Nat) : Nat := vOf C d / 65536 % 65536
def m0 (C : Call) (d : Nat) : Nat := vlo C d * C.n % 65536
def c0 (C : Call) (d : Nat) : Nat := vlo C d * C.n / 65536
def m1 (C : Call) (d : Nat) : Nat := (vhi C d * C.n + c0 C d) % 65536
def m2 (C : Call) (d : Nat) : Nat := (vhi C d * C.n + c0 C d) / 65536
/-- `acc`: the last draw of the call. -/
def accOf (C : Call) (d : Nat) : Nat := if d + 1 = nd C then 1 else 0
/-- `δ`: `Z − 1 − m1` on the accepting row, `m1 − Z` on rejected rows. -/
def dlOf (C : Call) (d : Nat) : Nat :=
  if d + 1 = nd C then zOf C.n - 1 - m1 C d else m1 C d - zOf C.n
/-- `st`: the first draw. -/
def stOf (d : Nat) : Nat := if d = 0 then 1 else 0

/-- Cell `c` of draw row `d` of call `C`. -/
def drawCell (C : Call) (d c : Nat) : Nat :=
  if c < 16 then limbN (C.key.getD (c / 2) 0) (c % 2)
  else if c = 16 then kOf C d / 16
  else if c < 21 then bt (kOf C d % 16) (c - 17)
  else if c = 21 then vlo C d
  else if c = 22 then vhi C d
  else if c < 37 then bt C.n (c - 23)
  else if c < 51 then (if c - 37 = topBit C.n then 1 else 0)
  else if c < 67 then bt (m0 C d) (c - 51)
  else if c < 81 then bt (c0 C d) (c - 67)
  else if c < 97 then bt (m1 C d) (c - 81)
  else if c < 111 then bt (m2 C d) (c - 97)
  else if c < 127 then bt (dlOf C d) (c - 111)
  else if c = 127 then accOf C d
  else if c = 128 then stOf d
  else if c = 129 then 1
  else if c < 136 then bt d (c - 130)
  else if c = 136 then C.kstart
  else 0

/-- **Cell `c` of a row.** -/
def rowCell : Row → Nat → Nat
  | .draw C d, c => drawCell C d c
  | .pad, _ => 0

/-! ## Rows -/

def callRows (C : Call) : List Row := (List.range (nd C)).map (Row.draw C)

def honestRows (calls : List Call) : List Row := calls.flatMap callRows

def honestLog (calls : List Call) : Nat := max 1 (ZkFormal.Chacha.Gen.clog2 (honestRows calls).length)

def honestCell (calls : List Call) (r c : Nat) : Nat := rowCell ((honestRows calls).getD r .pad) c

def honestTrace (calls : List Call) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  ⟨fun _ => honestLog calls, fun _ r c => ZkFormal.Algebra.Fp.ofNat (honestCell calls r c)⟩

/-! ## Expected bus traffic -/

/-- The `busChacha` message received by draw `d` of `C`. -/
def wordMsg (C : Call) (d : Nat) : List ZkFormal.Algebra.Fp :=
  Sound.chachaMsg C.key (kOf C d / 16) (kOf C d % 16) (streamWord C.key (kOf C d))

/-- All received `busChacha` messages (multiplicity one each), in row order. -/
def expectedWords (calls : List Call) : List (List ZkFormal.Algebra.Fp) :=
  calls.flatMap fun C => (List.range (nd C)).map (wordMsg C)

/-- The `busGen` message provided by call `C`. -/
def genOut (C : Call) : List ZkFormal.Algebra.Fp :=
  Rng.genMsg C.key C.kstart C.n (result C).1 (result C).2

/-- All provided `busGen` messages (multiplicity one each), one per call. -/
def expectedGen (calls : List Call) : List (List ZkFormal.Algebra.Fp) := calls.map genOut

end ZkFormal.Chacha.Rng.Gen
