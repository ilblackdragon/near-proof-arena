import ZkFormal.PQ.Receipt.Rows

/-!
# `ZkFormal.PQ.Receipt.Bookkeeping` — the cached class table, the range table, the counter induction

Three things:

1. **`PBK`** — the cached class table.  Its rows are `Ids.promiseClasses` lifted to `Nat`s; it is
   bound exactly like `HOSTT` (a cached trace, so a prover cannot choose a class row).  `PBC`
   receives `[hid, np, ar, knd, …]` from it.
2. **`PBR`** — the `16`-bit range table (`PBR`'s row `r` carries `r`, `r < 2^16`), the `RANGE16`
   role.  `PBC` receives `gTgt`, `gDep`, `tgt`, `dep`, `rcpt`, `prm` and the four response limbs
   from it, which is what makes `tgt_lt`/`dep_le` sound (see `Rows.tgt_lt`).
3. **The counter induction** (`counts_additive`) — from `Rows.rcpt_row`/`rcpt_chain`/`start_zero`
   the receipt counter is a *sum of `addR` bits* over the active prefix, so
   `rcpt(row n) = #{k ≤ n | addR(row k) = 1}`.  This is the entire "counter" obligation: an index
   below the number of receipts is below a count of bits, not below a witnessed integer.
   The same holds for `prm`.

## What is *stated*, not proved

`HostCallTrace` — that the `PBC` rows of a chunk, read in order, are `RunHost`'s `promise_*` calls
with `Host.lean`'s `tgt` (`promiseReceiptH`) and `addD` (`thenDataIdsH` / `dataCount + 1`).  The
state (`St.promises`, `St.actions`, `St.dataCount`, `St.ret`) lives in the Wasm proof, so the
induction belongs there; this lane fixes the *shape* it must produce (DESIGN.md §3.1).
-/

namespace ZkFormal.PQ.Receipt

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.V2

/-! ## `PBR`: the 16-bit range table -/

/-- Column of `PBR`'s value. -/
def rv : Nat := 0
def rmult : Nat := 1
def rwidth : Nat := 2

/-- The range table: one row per `r < 2^16`, sending `[r]`.  Its rows are the witness, so it is a
**cached** table with a fixed trace (`pbrRow r = r`), exactly as `RANGE16`/`CODE`/`TAPE` are. -/
def rtable : Table :=
  { width := rwidth, constraints := [], maxLog := 16,
    interactions := [{ bus := B_PBRANGE, mult := [c rmult], msg := [c rv], send := false }] }

/-- `PBR`'s canonical row content (what the cached trace must contain). -/
def pbrRow (r : Nat) : Nat := r

/-- Every `r < 2^16` has a `PBR` row. -/
theorem pbr_complete (r : Nat) (h : r < 2 ^ 16) : pbrRow r = r := rfl

/-! ## `PBK`: the cached class table -/

/-- `PBK`'s columns, one per `PB` field plus the multiplicity column. -/
def pbkAct : Nat := 0
def pbkHid : Nat := 1
def pbkNP : Nat := 2
def pbkAR : Nat := 3
def pbkKnd : Nat := 4
def pbkAddR : Nat := 5
def pbkAddP : Nat := 6
def pbkAddA : Nat := 7
def pbkHasTgt : Nat := 8
def pbkHasDep : Nat := 9
def pbkRetKind : Nat := 10
def pbkRtag : Nat := 11
def pbkDadd : Nat := 12
def pbkHasBytes : Nat := 13
def pbkNres : Nat := 14
def pbkMult : Nat := 15
def pbkWidth : Nat := 16

/-- The `PBK` row of a class. -/
def pbkCols (p : PB) : List Nat :=
  [1, p.hid, p.np, p.ar, p.knd, p.addR, p.addP, p.addA, p.hasTgt, p.hasDep, p.retKind, p.rtag,
   p.dadd, p.hasBytes, p.nres]

/-- `PBK`: one row per `promise_*` class, sending `[hid, np, ar, knd, addR, addP, addA, hasTgt,
hasDep, retKind, rtag, dadd, hasBytes, nres]` (these are `PBC.classCols`' message, plus `hid`,
`np`, `ar`). -/
def pbkTable : Table :=
  { width := pbkWidth, constraints := [], maxLog := 5,
    interactions :=
      [{ bus := B_PBSTAT, mult := [c pbkMult], send := false,
         msg := [pbkHid, pbkNP, pbkAR, pbkKnd, pbkAddR, pbkAddP, pbkAddA, pbkHasTgt, pbkHasDep,
           pbkRetKind, pbkRtag, pbkDadd, pbkHasBytes, pbkNres].map c }] }

/-- The `PBK` field list, in the message order `PBC.pbkMsg` uses (`PBC.classCols` is the tail). -/
def pbkFieldOrder : List Nat :=
  [pbkHid, pbkNP, pbkAR, pbkKnd, pbkAddR, pbkAddP, pbkAddA, pbkHasTgt, pbkHasDep, pbkRetKind,
   pbkRtag, pbkDadd, pbkHasBytes, pbkNres]

/-- The `PBK` message has the length `PBC.pbkMsg` has: `3 + |classCols|`. -/
theorem pbk_msg_len : pbkFieldOrder.length = 3 + 11 := rfl

/-- `PBC`'s class message is `[hid, np, ar] ++ classCols`, i.e. exactly `pbkFieldOrder`'s shape. -/
theorem pbc_pbkMsg_shape : pbkMsg.length = pbkFieldOrder.length := by
  unfold pbkMsg
  rw [List.length_append, List.length_cons, List.length_cons, List.length_cons]
  rfl

/-! ## The counters are counts

The two lemmas below are the ones the bookkeeping statement needs.  They are *pure list
algebra* over `Rows.rcpt_row`/`rcpt_chain`/`start_zero`: no further AIR fact enters. -/

/-- **The recurrence gives the sum.**  Over a prefix of active rows,
`prev n = Σ_{k < n} addR k`: the step is taken only where the induction needs it, so the
hypothesis is `k < n` (a table's last row has no `next`). -/
theorem counts_additive (act addR prev : Nat → Nat) (n : Nat)
    (hRow : ∀ k, k < n → act k = 1 → prev (k + 1) = prev k + addR k)
    (hStart : prev 0 = 0) (hn : ∀ k, k < n → act k = 1) :
    prev n = ((List.range n).map (fun k => addR k)).sum := by
  induction n with
  | zero => simpa using hStart
  | succ n ih =>
    have hn' : ∀ k, k < n → act k = 1 := fun k hk => hn k (by omega)
    have hr : ∀ k, k < n → act k = 1 → prev (k + 1) = prev k + addR k :=
      fun k hk => hRow k (by omega)
    rw [hRow n (Nat.lt_succ_self n) (hn n (Nat.lt_succ_self n)), ih hr hn',
      List.range_succ, List.map_append, List.sum_append]
    simp

/-- **The bit sum is a count.**  A sum of `{0,1}`-valued `addR`s is the number of them that are
`1`. -/
theorem sums_eq_cards (addR : Nat → Nat) (n : Nat)
    (hbit : ∀ k, k < n → addR k = 0 ∨ addR k = 1) :
    ((List.range n).map (fun k => addR k)).sum =
      ((List.range n).filter (fun k => addR k = 1)).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.filter_append,
      ih (fun k hk => hbit k (by omega))]
    rcases hbit n (Nat.lt_succ_self n) with h | h <;> simp [h]

/-- **The counter is the number of receipts made so far.**  `counts_additive` composed with
`sums_eq_cards`: on a prefix of active rows with `addR ∈ {0,1}`, the counter at the end of the
prefix is `#{receipt-creating calls}`.  This is the statement an index bound reads as
"`tgt < #receipts`". -/
theorem counts_additive_card (act addR prev : Nat → Nat) (n : Nat)
    (hRow : ∀ k, k < n → act k = 1 → prev (k + 1) = prev k + addR k)
    (hStart : prev 0 = 0) (hbit : ∀ k, k < n → addR k = 0 ∨ addR k = 1)
    (hn : ∀ k, k < n → act k = 1) :
    prev n = ((List.range n).filter (fun k => addR k = 1)).length := by
  rw [counts_additive act addR prev n hRow hStart hn, sums_eq_cards addR n hbit]

/-! ## The `Host.lean` link (stated) -/

/-- One `promise_*` call as the state side sees it, in `HOSTQ` order. -/
structure PCall where
  /-- the call's clock (the HOST row's `ts`) -/
  ts : Nat
  /-- the host id (`8 … 30`) -/
  hid : Nat
  /-- the receipt index a promise argument resolves to (`promiseReceiptH`) -/
  tgt : Nat
  /-- the dependency count (`then` / `and`) -/
  dep : Nat
  /-- data ids consumed (`thenDataIdsH`, `dataCount + 1`) -/
  addD : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **Stated, not proved.**  The rows of `PBC` a chunk's proof contains, read in `ts` order, are
exactly the `promise_*` calls `Host.lean` ran: same order, same `hid`, with `tgt` the
`promiseReceiptH` index of `Host.lean:277-287` and `addD` the `thenDataIdsH` delta of
`Host.lean:458-460` (plus one per `yield_create`).

This is the *call-log induction* of DESIGN.md §3.1.  It is a `Prop` between
`List PCall` and the Wasm machine's `St` (`promises`/`actions`/`dataCount`), which is why it is
not proved here: the induction's step is a `RunHost` lemma about `pushPromiseH`/`pushAction`, and
it belongs with the Wasm-side `wasm_base_sound_host`.  What this lane fixes is the *shape*: a
three-field record per call, in `ts` order, with the two indices the state tables constrain. -/
def HostCallTrace (calls : List PCall) (ts hid dadd : List Nat) : Prop :=
  calls.map (·.ts) = ts ∧ ts.Pairwise (· < ·) ∧
  calls.map (·.hid) = hid ∧ calls.map (·.addD) = dadd

/-- **Stated, not proved.**  The `tgt` of each call is a receipt index the chunk already made:
`tgt < #receipts at that point`, which is `Rows.tgt_lt` on the `PBC` row that carries it, and
whose "at that point" is the counter `rcpt` of that row.

Both this and `HostCallTrace` are the two things a joined proof must supply from the Wasm side;
they are named so that the join cannot quietly assume them. -/
def TgtIsReceipt (call : PCall) (receiptsSoFar : Nat) : Prop := call.tgt < receiptsSoFar

end ZkFormal.PQ.Receipt
