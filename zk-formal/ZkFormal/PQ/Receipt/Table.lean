import ZkFormal.PQ.Receipt.Ids

/-!
# `ZkFormal.PQ.Receipt.Table` — `PBC`: the `promise_*` bookkeeping call row

One row per `promise_*` host call, in `HOSTQ` (`ts`) order.  The row is the *state side* of a
HOST row: it consumes the call's request, records what the call did to the receipt/promise
bookkeeping, and produces the response.  This is DESIGN.md §3.1 made an AIR.

## Columns, and the division between *static* and *dynamic*

The class of a call — everything `Host.lean` decides from the function *name* — is a row of a
**cached** table `PBK` (`Ids.promiseClasses`), consumed on a bus.  A `PBC` row copies it into
its own columns (so the constraints can read it without a per-row bus walk) but the copy is
*pinned by the bus receive*: a prover cannot invent a class.

| columns | static? | meaning |
|---|---|---|
| `act` | dyn | row is a call (0 = padding) |
| `hid`, `np`, `ar`, `knd`, `addR`, `addP`, `addA`, `hasTgt`, `hasDep`, `retKind`, `rtag`, `dadd`, `hasBytes`, `nres` | **class** | `Ids.PB`, pinned by `PBK` |
| `ts`, `s` | dyn | the call's clock and instruction gas (the `HOSTQ` request) |
| `dep` | dyn | dependency count (`promise_then` / `batch_then` / `and`) |
| `tgt` | dyn | the receipt index argument 0 resolves to |
| `addD` | dyn | data ids consumed (`thenDataIdsH`, `yield_create`) |
| `rcpt`, `prm` | dyn | the receipt / promise counters **after** this call |
| `prevR`, `prevP` | dyn | the counters **before** this call |
| `rl`, `rh`, `gl`, `gh`, `st` | dyn | the response (`HOSTR`'s limbs/status, 16-bit) |
| `gTgt`, `gDep` | dyn | comparison gaps: `rcpt − tgt − 1`, `128 − dep` |

width 32.

## What the constraints say (every one degree ≤ 2)

1. **Bits.** `act` and `st` are bits.  Every *class* flag is pinned by the `PBK` receive below
   instead of by a local constraint, and `Ids.promiseClasses_flags` kernel-checks the class
   table's own bits — so the state row carries no witness it could misuse.
2. **Class link.** `PBK recv [hid, np, ar, knd, addR, addP, addA, hasTgt, hasDep, retKind,
   rtag, dadd, hasBytes, nres]`, with the row's columns in that order.  This is what makes every
   static column above *not a witness*.
3. **Policy.** `hasDep = 0 → addD = dadd` and `hasDep = 1 → addD = dep` (`cData`), i.e. a call
   consumes exactly its class's static data ids, or its dependency count for the `then` family.
4. **Counters.** `rcpt = prevR + addR`, `prm = prevP + addP` (`cRcpt`, `cPrm`), and they chain
   across consecutive active rows (`cRcptChain`: `next.prevR = rcpt`, `cPrmChain`).  The first
   row's `prevR = prevP = 0` (`cStart`).  So `rcpt` is *the number of receipts the chunk made so
   far* and `prm` *the number of promises*, in `ts` order — no free counter anywhere.
5. **Bounds.** `hasTgt = 1 → tgt + gTgt + 1 = rcpt` (so `tgt < rcpt`: a promise names a receipt
   that exists) and `hasTgt = 0 → tgt = 0`; `hasDep = 1 → dep + gDep = 128` (so
   `dep ≤ maxInputDataDependencies`) and `hasDep = 0 → dep = 0`.
6. **Activity.** The first row is active; an inactive row is followed by one; inactive rows are
   inert (all counts zero).

The two bounds are not polynomial, so they are delegated to the 16-bit lookup `PBR` (`gTgt`,
`gDep`, and the four response limbs) — the `RANGE16` role, a table whose row `r` carries `r`.

## Interactions

```
PBK  recv  [hid, np, ar, knd, addR, addP, addA, hasTgt, hasDep, retKind, rtag, dadd, hasBytes, nres]
PBR  recv  [gTgt] [gDep] [rl] [rh] [gl] [gh]
```

`HOSTQ`/`HOSTR` are **not** here: they are the cross-proof wire and live in `Wire.lean`, so this
table can be checked for its bookkeeping alone.

## What is *stated*, not proved

The link to `Host.lean`'s *sequence* of calls (that a chunk's `PBC` rows are `RunHost`'s calls,
in order, with `promiseReceiptH`'s `tgt` and `thenDataIdsH`'s `addD`) is `HostCallTrace`, a
`Prop` in `Bookkeeping.lean`.  It is an induction over the call log whose state
(`St.promises`, `St.actions`, `St.dataCount`) belongs to the Wasm proof — DESIGN.md §3.1's
"call-log induction", and the honest residue of this lane.
-/

namespace ZkFormal.PQ.Receipt

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-! ## Layout -/

def act : Nat := 0
def hid : Nat := 1
def ts : Nat := 2
def s : Nat := 3
def np : Nat := 4
def ar : Nat := 5
def dep : Nat := 6
def tgt : Nat := 7
def addD : Nat := 8
def knd : Nat := 9
def addR : Nat := 10
def addP : Nat := 11
def addA : Nat := 12
def hasTgt : Nat := 13
def hasDep : Nat := 14
def retKind : Nat := 15
def rtag : Nat := 16
def dadd : Nat := 17
def hasBytes : Nat := 18
def nres : Nat := 19
def rcpt : Nat := 20
def prm : Nat := 21
def prevR : Nat := 22
def prevP : Nat := 23
def rl : Nat := 24
def rh : Nat := 25
def gl : Nat := 26
def gh : Nat := 27
def st : Nat := 28
def gTgt : Nat := 29
def gDep : Nat := 30
/-- The argument window of the `HOSTQ` request: `(aLo j, aHi j)` for `j < 9` (16-bit limbs).
`PBC` only *forwards* them (they are the Wasm side's stack words); `Wire.lean` puts them on
`HOSTQ`.  Keeping them here means the request is a function of the `PBC` row, so a state proof
cannot answer a call it did not see. -/
def aLo (j : Nat) : Nat := 31 + 2 * j
def aHi (j : Nat) : Nat := 32 + 2 * j
def width : Nat := 49

/-- `rcpt`'s slot in the class message.  The class is `PB` plus `nres` (`nres` is static:
`nres = 1 ↔ retKind ≠ 0`, which is `pushRet`'s behaviour for every one of the 23 arms). -/
def classCols : List Nat :=
  [knd, addR, addP, addA, hasTgt, hasDep, retKind, rtag, dadd, hasBytes, nres]

/-- The only *state-side* bits.  Every other flag is a class column: it is pinned by the `PBK`
receive, not by a local constraint (a prover cannot pick it, and `Ids.promiseClasses_flags`
kernel-checks the class table's own bits). -/
def bitCols : List Nat := [act, st]

/-! ## Constraints -/

/-- `nres` is a bit, and the class row's `nres = 1 ↔ retKind ≠ 0` is `Ids.promiseClasses_nres`.
The state constraint only stops an *inactive* row from pushing a word (`act = 0 → nres = 0`).  A
state-side `nres ↔ retKind` law would be degree 2 in two class columns and is already pinned by
`PBK`. -/
def cNres : Expr := .mul (sub (k 1) (c act)) (c nres)

/-- Counter laws: `rcpt = prevR + addR`, `prm = prevP + addP` (degree 2). -/
def cRcpt : Expr := .mul (c act) (sub (c rcpt) (.add (c prevR) (c addR)))
def cPrm : Expr := .mul (c act) (sub (c prm) (.add (c prevP) (c addP)))

/-- The counters chain across consecutive active rows: `isTransition·act·next.act·(next.prevR −
rcpt)`, degree 4. -/
def cRcptChain : Expr :=
  mul3 .isTransition (c act) (.mul (n act) (sub (n prevR) (c rcpt)))
def cPrmChain : Expr :=
  mul3 .isTransition (c act) (.mul (n act) (sub (n prevP) (c prm)))

/-- The first row starts the counters at `0`. -/
def cStart : List Expr := [.mul .isFirst (c prevR), .mul .isFirst (c prevP)]

/-- `hasTgt = 0 → tgt = 0`; `hasTgt = 1 → tgt + gTgt + 1 = rcpt`.  Degree 2. -/
def cTgt : List Expr :=
  [ .mul (sub (k 1) (c hasTgt)) (c tgt),
    .mul (c hasTgt) (sub (.add (c tgt) (.add (c gTgt) (k 1))) (c rcpt)) ]

/-- `hasDep = 0 → dep = 0`; `hasDep = 1 → dep + gDep = 128`.  Degree 2. -/
def cDep : List Expr :=
  [ .mul (sub (k 1) (c hasDep)) (c dep),
    .mul (c hasDep) (sub (.add (c dep) (c gDep)) (k 128)) ]

/-- **The policy link.**  A call consumes exactly its class's static data ids, or its dependency
count for the `then` family.  Degree 2 each. -/
def cData : List Expr :=
  [ .mul (sub (k 1) (c hasDep)) (sub (c addD) (c dadd)),
    .mul (c hasDep) (sub (c addD) (c dep)) ]

/-- Inactive rows are inert (every count zero, and no argument).  Degree 2 each. -/
def cInert : List Expr :=
  ([dep, tgt, addD, rcpt, prm] ++ classCols ++
    (List.range 9).flatMap (fun j => [aLo j, aHi j])).map
      (fun x => .mul (sub (k 1) (c act)) (c x))

/-- The row is a call on row 0. -/
def cFirstAct : Expr := .mul .isFirst (sub (k 1) (c act))
/-- Padding follows padding. -/
def cPadPad : Expr := mul3 .isTransition (sub (k 1) (c act)) (n act)

/-- Grouped so each `mem_*` membership lemma in `Rows.lean` is one `List.mem_append` chain and
each group's content is visible in the definition. -/
def cBits : List Expr := bitCols.map (fun x => bool (c x))
def cState : List Expr := [cNres, cRcpt, cPrm, cRcptChain, cPrmChain, cFirstAct, cPadPad]

def constraints : List Expr :=
  cBits ++ cState ++ cStart ++ cTgt ++ cDep ++ cData ++ cInert

/-! ## Interactions -/

/-- The `PBK` message: the class of `hid` (with the signature, so a class row of a different
arity cannot be spliced on). -/
def pbkMsg : List Expr := [c hid, c np, c ar] ++ classCols.map c

/-- The `HOSTQ`-style request argument window, as `(aLo j, aHi j)` pairs. -/
def argPairs : List Expr :=
  (List.range 9).flatMap fun j => [c (aLo j), c (aHi j)]

/-- The columns `PBC` range-checks through `PBR` (16-bit). -/
def boundedCols : List Nat := [tgt, dep, rcpt, prm, rl, rh, gl, gh, gTgt, gDep] ++
  (List.range 9).flatMap (fun j => [aLo j, aHi j])

def interactions : List Interaction :=
  [ recv B_PBSTAT (c act) pbkMsg ] ++
    boundedCols.map fun x => recv B_PBRANGE (c act) [c x]

/-- One row per `promise_*` host call of a chunk; `2^21` Wasm steps bound the count. -/
def maxLog : Nat := 16

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

/-! ## The table is well formed (kernel-checked)

`Table.wf` is the protocol's own admissibility predicate: every column and public input in range,
every bus id below `numBuses`, at most 25 multiplicity bits, `maxLog ≤ 22`, and every constraint
of degree at most `maxDeg`.  `pbc_wf` checks it at `maxDeg = 8` (the AIR's `maxDeg` is 4, and the
`bbTable` byte table's is 4 too) — so a future edit that made a constraint cubic-by-accident, or
that pushed a bus id out of range, fails the build rather than the prover. -/
theorem pbc_wf : Air.wf ⟨[table], 220, 0⟩ 8 = true := by decide

/-- The `PBC` constraint count and the degree actually used. -/
theorem pbc_shape :
    table.width = 49 ∧ table.constraints.length = 51 ∧ table.interactions.length = 29 ∧
      table.maxLog = 16 ∧ (table.constraints.map Expr.degree).foldr max 0 = 4 := by
  decide +kernel

theorem pbc_degree : ∀ e ∈ table.constraints, e.degree ≤ 4 := by
  intro e he
  have h := pbc_shape.2.2.2.2
  have : e.degree ≤ (table.constraints.map Expr.degree).foldr max 0 := by
    have hle : ∀ (l : List Expr) (x : Expr), x ∈ l → x.degree ≤ (l.map Expr.degree).foldr max 0 := by
      intro l
      induction l with
      | nil => intro x hx; exact absurd hx (by simp)
      | cons a l ih =>
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)
    exact hle _ e he
  omega

end ZkFormal.PQ.Receipt
