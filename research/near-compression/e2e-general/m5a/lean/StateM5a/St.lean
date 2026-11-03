import StateM5a.Air
import ZkFormal.Sha.Table

/-!
# StateM5a.St — M5b: the first STATE rows (`STB` message bytes, `STW` writes)

In M5a the working-set writes `WRITE(seg, t, kd16, present, len, vh16)` (received by `WSA`) came
from the public tape.  M5b produces them from **execution-side messages carrying the raw trie key
and value bytes**, so the key digest `kd = sha256 key` and the value digest `vh = sha256 value` are
computed in-circuit (a second instance `SHAS` of the unchanged SHA-256 table on its own bus pair
`SB2`/`SD2`, message ids `ID_ST + m`), and the write time `t` is the
request's timestamp (chosen by the execution side, range-checked by `WSA`: `t < 2^24`, and ordered
per entry by the `WM` gap).

Execution-side interface (the shape of lane A's host buses, plan §3.3):
* `SREQ [ts, pr, seg, klen, kptr, vlen, vptr]` — a `storage_write` (`pr = 1`) / `storage_remove`
  (`pr = 0`) request at time `ts` (NEAR's argument order: key length / pointer, value length /
  pointer); in lane A's form `HOSTQ [ts, hid, S, args…]` with `pr` from `hid`;
* `HB [ts, pos, byte]` — a byte the call read at linear-memory address `pos` (lane A's `HOSTB`).

On T1 (no Wasm yet) the public tape sends both.  The state side:
* **`STB`** (one row per message byte): runs of rows, one per message `m = 0, 1, …` (consecutive,
  so each `m` has exactly one run), `j = 0, 1, …` within a run, `ts`/`base` constant on a run.  A
  row sends the byte to the SHA-256 instance `SB2(ID_ST + m, j, b)` and receives it from the
  execution side `HB(ts, base + j, b)`; the run's last row sends the descriptor
  `DESC(m, ts, base, len = j + 1)`.
* **`STW`** (one row per write): receives `SREQ`, the key run's descriptor `DESC(mk, ts, kptr, klen)`
  and digest `SD2(ID_ST + mk, klen, dk)`, for a non-empty value the value run's
  `DESC(mv, ts, vptr, vlen)` and `SD2(ID_ST + mv, vlen, dv)` (an empty value: `ve = 1`,
  `dv = sha256 []`; a remove: `pr = 0`, `vlen = 0`, `dv = 0`), and sends
  `WRITE(seg, ts, pack2 dk, pr, vlen, pack2 dv)`.

The tables are not part of `m5aAir`: `m5bAir D` is `(m5aAir D).tables ++ m5bExtra`, i.e.
`fullAir D m5bExtra …`.  None of them sends on a bus the M5a theorems restrict for extra tables
(`SHA_BYTES`, `SHA_DIGEST`, `NIB`, `KLEN`, `ORD`, `KC`, `KDIG`; no interaction on `WM`, `PT`,
`RCH`, `RNG`, `TREE`, `DOWN`, `UP`, `TCH`, `VER`) — the reason for the second SHA-256 instance
instead of a new id space in the first (`M5b.lean`).
-/

namespace StateM5a

open ZkFormal.Air

/-- `(ts, pr, seg, klen, kptr, vlen, vptr)`: an execution-side storage request (M5b). -/
def B_SREQ : Nat := NUM_BUSES_WS
/-- `(ts, pos, byte)`: a byte an execution-side call read (lane A's `HOSTB`). -/
def B_HB : Nat := NUM_BUSES_WS + 1
/-- `(m, ts, base, len)`: `STB` message `m` is the `len` bytes at `base, …` of call `ts`. -/
def B_DESC : Nat := NUM_BUSES_WS + 2
/-- The second SHA-256 instance's byte / digest buses (the `SHA_BYTES` / `SHA_DIGEST` of `SHAS`). -/
def B_SB2 : Nat := NUM_BUSES_WS + 3
def B_SD2 : Nat := NUM_BUSES_WS + 4
def NUM_BUSES_ST : Nat := NUM_BUSES_WS + 5

/-- The second SHA-256 table (`ZkFormal.Sha.Table`, unchanged) for the STATE messages. -/
def shaTableS : Table := ZkFormal.Sha.Table.table B_SB2 B_SD2

/-- SHA-256 message ids of the `STB` messages: `ID_ST + m` (disjoint from `KEY`/`BR`/`SN`, so the
two instances can later be merged). -/
def ID_ST : Nat := 4 * 2 ^ 24

/-- `sha256 []`. -/
def SHA256_EMPTY : List Nat :=
  [0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
   0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55]

namespace Stb
def L : Layout := [("act", 1), ("m", 1), ("j", 1), ("b", 1), ("ts", 1), ("base", 1), ("last", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j
def nx (s : String) (j : Nat := 0) : Expr := T.n s j

def constraints : List Expr :=
  let act := c "act"; let last := c "last"; let na := nx "act"
  [bool act, bool last, (1 - act) * last,
   -- message 0 starts at row 0; active rows first, then padding
   .isFirst * c "m", .isFirst * c "j",
   .isTransition * na * (1 - act),
   .isTransition * act * (1 - na) * (1 - last),
   .isLast * act * (1 - last),
   -- a run: `j` counts from 0, `m` steps by one between runs, `ts`/`base` constant
   .isTransition * na * (nx "m" - c "m" - last),
   .isTransition * na * (nx "j" - (1 - last) * (c "j" + 1)),
   .isTransition * na * (1 - last) * (nx "ts" - c "ts"),
   .isTransition * na * (1 - last) * (nx "base" - c "base")]

def interactions : List Interaction :=
  let A := c "act"
  [snd B_SB2 A [K ID_ST + c "m", c "j", c "b"],
   rcv B_HB A [c "ts", c "base" + c "j", c "b"],
   snd B_DESC (c "last") [c "m", c "ts", c "base", c "j" + 1]]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Stb

namespace Stw
def L : Layout :=
  [("act", 1), ("seg", 1), ("ts", 1), ("pr", 1), ("ve", 1), ("klen", 1), ("kptr", 1), ("vlen", 1),
   ("vptr", 1), ("mk", 1), ("mv", 1), ("dk", 32), ("dv", 32), ("ke", 1)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j

def constraints : List Expr :=
  let pr := c "pr"; let ve := c "ve"
  [bool (c "act"), bool pr, bool ve, (1 - c "act") * pr, (1 - pr) * ve, (1 - pr) * c "vlen",
   ve * c "vlen"] ++
  ((List.range 32).flatMap fun b =>
    [(1 - pr) * c "dv" b, ve * (c "dv" b - K (SHA256_EMPTY.getD b 0))]) ++
  -- M5a-8: an empty key (`ke = 1`: `klen = 0`, `dk = sha256 []`, no `STB` run)
  [bool (c "ke"), (1 - c "act") * c "ke", c "ke" * c "klen"] ++
  (List.range 32).map fun b => c "ke" * (c "dk" b - K (SHA256_EMPTY.getD b 0))

def interactions : List Interaction :=
  let A := c "act"; let gv := c "pr" - c "ve"; let gk := c "act" - c "ke"
  [rcv B_SREQ A [c "ts", c "pr", c "seg", c "klen", c "kptr", c "vlen", c "vptr"],
   rcv B_DESC gk [c "mk", c "ts", c "kptr", c "klen"],
   rcv B_SD2 gk ([K ID_ST + c "mk", c "klen"] ++ (List.range 32).map fun b => c "dk" b),
   rcv B_DESC gv [c "mv", c "ts", c "vptr", c "vlen"],
   rcv B_SD2 gv ([K ID_ST + c "mv", c "vlen"] ++ (List.range 32).map fun b => c "dv" b),
   snd B_WRITE A ([c "seg", c "ts"] ++ pack2 (fun b => c "dk" b) ++ [c "pr", c "vlen"] ++
     pack2 (fun b => c "dv" b))]

def table : Table := { width := L.width, constraints, interactions, maxLog := 20 }
end Stw

/-- The M5b tables, after `m5aAir`'s. -/
def m5bExtra : List Table := [shaTableS, Stb.table, Stw.table]

def m5bAir (D : Nat) : Air :=
  { tables := (m5aAir D).tables ++ m5bExtra, numBuses := NUM_BUSES_ST, numPub := 17 }

def tableNamesB : List String := tableNames ++ ["SHAS", "STB", "STW"]

def layoutsB (D : Nat) : List (String × Layout) := layouts D ++ [("STB", Stb.L), ("STW", Stw.L)]

def namesJsonB (D : Nat) : String :=
  let q (s : String) := "\"" ++ s ++ "\""
  "{" ++ ",".intercalate ((layoutsB D).map fun (t, L) =>
    q t ++ ":[" ++ ",".intercalate (L.names.map q) ++ "]") ++
  s!",\"D\":{D},\"tables\":[" ++ ",".intercalate (tableNamesB.map q) ++ "]}"

end StateM5a
