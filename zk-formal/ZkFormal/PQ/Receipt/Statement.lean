import ZkFormal.PQ.Receipt.Wire

/-!
# `ZkFormal.PQ.Receipt.Statement` — the `PBC` view, its counter theorem, and what is open

This module packages the state side of the promise/receipt family the way
`D3/StateWrite.lean` and `PQ/Join/Statement.lean` do: the proved part is a theorem, the open
part is a named `Prop`.

## The view

`HoldsP`/`TableLocal` at `PBC` gives, row by row, the call record

```
CallRec = (ts, hid, np, ar, tgt, dep, addD, knd, addR, addP, addA, retKind, nres, st)
```

with, by `Rows`:

* the class columns are `PBK`'s row of `hid`, and `PBK`'s rows are `Ids.promiseClasses`
  (the transcribed `Host.lean` table; `Ids.promiseClasses_policy`/`_nres`/`_shape` are the
  kernel checks of the transcription);
* `rcpt`/`prm` are *counters*: `Bookkeeping.counts_additive_card` says the receipt counter at the
  end of a prefix is the number of receipt-creating calls in it, and the same for promises;
* `tgt < rcpt` on a promise-index argument (`Rows.tgt_lt` + the `PBR` 16-bit bounds);
* `dep ≤ 128` on a dependency list (`Rows.dep_le`);
* `addD = dadd` (static classes) or `addD = dep` (the `then` family) — `Rows.data_of`/`data_on`.

## The main theorem

`rcpt_counter_is_count`: at any row `n` of a `PBC` trace whose rows `0 … n−1` are active, the
receipt counter at `n` equals `#{k < n | addR k = 1}`.  It is `Rows.rcpt_row` + `rcpt_chain` +
`start_zero` fed into `Bookkeeping.counts_additive_card`; nothing else enters.  So an index the
Wasm side returns is below a *count of bits*, which is the whole bookkeeping obligation.

## What is open

* `HostCallTrace` (`Bookkeeping.lean`) — the calls are `Host.lean`'s `RunHost` sequence.
* `ActionBytesAreHostBytes` / `ActionEncodingIsBorsh` (`Wire.lean`) — byte provenance and the
  borsh encoding of the action the call appended.
-/

namespace ZkFormal.PQ.Receipt

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.V2

/-- One active `PBC` row, as the state side reads it. -/
structure CallRec where
  ts : Nat
  hid : Nat
  np : Nat
  ar : Nat
  tgt : Nat
  dep : Nat
  addD : Nat
  knd : Nat
  addR : Nat
  addP : Nat
  addA : Nat
  retKind : Nat
  nres : Nat
  st : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The call record of row `r`. -/
def recOf (tr : Trace Fp) (tt r : Nat) : CallRec :=
  { ts := cv tr tt r ts, hid := cv tr tt r hid, np := cv tr tt r np, ar := cv tr tt r ar,
    tgt := cv tr tt r tgt, dep := cv tr tt r dep, addD := cv tr tt r addD,
    knd := cv tr tt r knd, addR := cv tr tt r addR, addP := cv tr tt r addP,
    addA := cv tr tt r addA, retKind := cv tr tt r retKind, nres := cv tr tt r nres,
    st := cv tr tt r st }

/-! ## The counter theorem

The two ingredients are exactly `Rows`' counter lemmas; this module only composes them.  The
statement is in terms of `prevR` (the counter *before* row `n`) because that is the quantity the
recurrence `prev(k+1) = prev(k) + addR(k)` produces; the counter *at* row `n` is then
`rcpt n = prevR n + addR n` (`Rows.rcpt_row`). -/

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The `Nat` image of the `act` cell, as the recurrence's activity predicate. -/
theorem cv_act_of_cell {tr : Trace Fp} {tt r : Nat} (h : tr.cell tt r act = 1) :
    cv tr tt r act = 1 := congrArg Fp.toNat h

/-- `addR` is a bit in `Nat` form.  It is a `PBK` **class** column, and
`Ids.promiseClasses_flags` is the kernel check that every class row's `addR` is a bit; the `PBK`
receive carries that bit to the row. -/
theorem addR_bit_nat {tr : Trace Fp} {tt r : Nat} (h : tr.cell tt r addR = 0 ∨ tr.cell tt r addR = 1) :
    cv tr tt r addR = 0 ∨ cv tr tt r addR = 1 := by
  rcases h with h | h
  · left; rw [cv, h]; rfl
  · right; rw [cv, h]; rfl

/-- **The receipt counter is the number of receipts made so far.**

`Rows.rcpt_row` (`rcpt k = prevR k + addR k`) chained by `Rows.rcpt_chain`
(`prevR(k+1) = rcpt k`), started at `Rows.start_zero`; the composition is
`Bookkeeping.counts_additive_card`.

The conclusion is `prevR`, the counter *before* row `n`.  The counter *at* row `n` is
`rcpt n = prevR n + addR n` (`Rows.rcpt_row`), so it is this count plus one bit: the receipt
index a call returns is below a *count of bits*, which is the whole bookkeeping obligation.

`h16` is the `PBR` 16-bit bound on `prevR` (`PBC` range-checks it, `Table.boundedCols`); it is
what makes the `Fp` addition `prevR + addR` the `Nat` addition. -/
theorem prevR_counter_is_count (hL : TableLocal table tr tt pub) {n : Nat}
    (hn : n < tr.height tt) (hact : ∀ k, k < tr.height tt → tr.cell tt k act = 1)
    (hbit : ∀ k, k < tr.height tt → tr.cell tt k addR = 0 ∨ tr.cell tt k addR = 1)
    (h16 : ∀ k, k < tr.height tt → cv tr tt k prevR + 1 < P) :
    cv tr tt n prevR =
      ((List.range n).filter (fun k => cv tr tt k addR = 1)).length := by
  -- the step, in `Nat`
  have hrow : ∀ k, k < n → cv tr tt k act = 1 →
      cv tr tt (k + 1) prevR = cv tr tt k prevR + cv tr tt k addR := by
    intro k hk hka
    have hka' : tr.cell tt k act = 1 := by
      have h1 : (tr.cell tt k act).toNat = 1 := hka
      calc tr.cell tt k act = ((tr.cell tt k act).toNat : Fp) := (Fp.ofNat_toNat _).symm
        _ = (1 : Fp) := by rw [h1]; rfl
    have hk1 : k + 1 < tr.height tt := by omega
    have hchain := rcpt_chain hL (r := k) hk1 hka' (hact (k + 1) hk1)
    have hrow' := rcpt_row hL (r := k) (by omega) hka'
    show (tr.cell tt (k + 1) prevR).toNat = (tr.cell tt k prevR).toNat + (tr.cell tt k addR).toNat
    rw [hchain, hrow']
    have a : (tr.cell tt k prevR).toNat + 1 < P := h16 k (by omega)
    have b : (tr.cell tt k addR).toNat ≤ 1 := by
      rcases hbit k (by omega) with h | h
      · rw [h]; decide
      · rw [h]; decide
    show (Fp.add (tr.cell tt k prevR) (tr.cell tt k addR)).toNat = _
    rw [Fp.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hstart : cv tr tt 0 prevR = 0 := congrArg Fp.toNat (start_zero hL (by omega)).1
  exact counts_additive_card (fun k => cv tr tt k act) (fun k => cv tr tt k addR)
    (fun k => cv tr tt k prevR) n hrow hstart
    (fun k hk => addR_bit_nat (hbit k (by omega)))
    (fun k hk => cv_act_of_cell (hact k (by omega)))

end ZkFormal.PQ.Receipt
