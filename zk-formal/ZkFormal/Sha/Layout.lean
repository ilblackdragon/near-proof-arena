import ArenaCore

/-!
# ZkFormal.Sha.Layout — column layout of the SHA-256 block table

OpenVM-style block hasher (DESIGN.md §5.2): one compression occupies 16
round rows `R0..R15` (4 rounds each) followed by one digest row `D`; every
message is preceded by one start row `S`.  A message of `k` blocks therefore
takes `1 + 17·k` rows; the table is padded with all-zero rows.

Columns (544 in total):

| columns | name | meaning |
|---|---|---|
| `[0,128)` | `A i b` | bit `b` of the `a`-word in slot `i` |
| `[128,256)` | `E i b` | bit `b` of the `e`-word in slot `i` |
| `[256,384)` | `W i b` | bit `b` of schedule word `W_{4j+i}` (round row `Rj`) |
| `[384,408)` | `CA i l k` | bit `k` of the carry of `a`-limb `l` (round `i`) |
| `[408,432)` | `CE i l k` | same for `e` |
| `[432,456)` | `CW i l k` | same for the schedule word |
| `[456,480)` | `I4/I8/I12 i l` | schedule helper `σ₀(W_{t-15}) + W_{t-16}` and two delayed copies |
| `[480,486)` | `W3 i l` | delayed copy of `W` limbs (`W_{t-7}`) |
| `[486,502)` | `Hin w l` | chaining value of the block (16-bit limbs) |
| `[502,520)` | `R j`, `D`, `S` | one-hot row kind (padding = none set) |
| `[520,536)` | `F k` | byte `k` of this row is message data |
| `536…543` | `Fprev, Nd, Id, Last, P80, Seen, Pn, Dmult` | framing |

A state row (`S` or `D`) and every round row hold four `a` words and four
`e` words.  Round row `Rj` slot `i` holds the `a`/`e` created by round
`4j+i`; a state row holds the chaining value as `(d,c,b,a)` in `A` slots
`0..3` and `(h,g,f,e)` in `E` slots `0..3`.  Thus the eight-slot window
(previous row, current row) at round `t` is `As t … As (t+7)`
(ZkFormal.Sha.Spec).
-/

namespace ZkFormal.Sha.Layout

def colA (i b : Nat) : Nat := 32 * i + b
def colE (i b : Nat) : Nat := 128 + 32 * i + b
def colW (i b : Nat) : Nat := 256 + 32 * i + b
def colCA (i l k : Nat) : Nat := 384 + 6 * i + 3 * l + k
def colCE (i l k : Nat) : Nat := 408 + 6 * i + 3 * l + k
def colCW (i l k : Nat) : Nat := 432 + 6 * i + 3 * l + k
def colI4 (i l : Nat) : Nat := 456 + 2 * i + l
def colI8 (i l : Nat) : Nat := 464 + 2 * i + l
def colI12 (i l : Nat) : Nat := 472 + 2 * i + l
def colW3 (i l : Nat) : Nat := 480 + 2 * i + l
def colHin (w l : Nat) : Nat := 486 + 2 * w + l
def colR (j : Nat) : Nat := 502 + j
def colD : Nat := 518
def colS : Nat := 519
def colF (k : Nat) : Nat := 520 + k
def colFprev : Nat := 536
def colNd : Nat := 537
def colId : Nat := 538
def colLast : Nat := 539
def colP80 : Nat := 540
def colSeen : Nat := 541
def colPn : Nat := 542
def colDmult : Nat := 543
def width : Nat := 544

/-- State word `w` (`a..h`) of a state row or of the last round row: words
`0..3` (`a,b,c,d`) are `A` slots `3..0`, words `4..7` are `E` slots `3..0`. -/
def colSt (w b : Nat) : Nat := if w < 4 then colA (3 - w) b else colE (7 - w) b

/-- Carry column used by the digest row for word `w`, limb `l`, bit `k`. -/
def colCSt (w l k : Nat) : Nat := if w < 4 then colCA (3 - w) l k else colCE (7 - w) l k

/-- Boolean columns. -/
def boolCols : List Nat :=
  List.range 456 ++ List.range' 502 34 ++ [colFprev, colLast, colP80, colSeen]

end ZkFormal.Sha.Layout
