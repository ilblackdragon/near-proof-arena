# REQUESTS — lane L6 (NEAR AIR), raised by sub-lanes

## R-L6d-1 (L6-link): view values must be canonical naturals (`< p`)  — APPLIED on `lane/zk-L6-link`

**Problem.** The views (`Extract/{NodeView,SmallViews,RcptView}.lean`) keep raw
values as `Nat` and are compared with the trace only through `Fp.ofNat`
(`TableTraffic`).  The `…Wf` predicates bound only some of them (`depth`,
`res`, `uses`, `kslot`, `tprev`, walk `r`/`u`, acct `k`/`tlast`, sort `r`), not
the raw byte lists, window bytes, node references (`cid/clen/cres`), walk edge
components, or mrk references.  `LinkStmt` is then false:

*Counterexample.* Take an honest batch and its honest views, and replace in
receipt 0 the gas-price byte `gp[0] = g` by `g + p`.  Every message is
unchanged as a list of field elements, so `TableTraffic` and bus balance still
hold, and all of `RcptWf` still holds except that the arithmetic clause
`RcptV.Wf.arith` is now vacuous (its hypothesis `Bytes8 x.gp` fails).  So
`burnt` of receipt 0 can be changed to any 16 byte values (again consistently in
the `PEO(0)` messages and the SHA counts) without violating any hypothesis of
`LinkStmt`; the claim's `outcomeRoot` is then the root of the modified
outcomes, and no `Ext` satisfies `Good` (the receipts are pinned by
`receiptsCommitment`, which with `gasPrice` and `blockGasPrice` determine
`tokensBurnt` of the outcome).  The same happens with any other raw value
(e.g. a walk edge component `+ p` makes the walk/edge correspondence fail in
`ℕ`; a `cid + p` breaks `TreeShape`'s range facts).

**Fix (minimal).** Add a `canon` field to each `…Wf`: every raw value of the
view is `< P`.

| structure | new field |
|---|---|
| `NodeWf` | `canon : ∀ s ∈ vs, ∀ x ∈ s.v.raw, x < P` (`NodeV.raw`: key, slot/kid bytes, `cid clen cres`, windows, `memB`) |
| `WalkWf` | `canon : ∀ w ∈ ws, ∀ st ∈ w.steps, ∀ x ∈ st.1, x < P` |
| `RcptWf` | `canon : ∀ x ∈ rs, ∀ y ∈ x.raw, y < P` (`RcptV.raw`: every list field and `kt`) |
| `AcctWf` | `canon : ∀ a ∈ as, ∀ x ∈ a.pre ++ a.post, x < P` |
| `MrkWf` | `canon : v.J < P ∧ v.rootId < P ∧ v.rootLen < P ∧ ∀ nd ∈ v.nodes, ∀ x ∈ nd.raw, x < P` |
| `SortWf` | `canon : ∀ x ∈ ids, ∀ y ∈ x.2, y < P` |

**Why it is provable from the tables.** Every raw value of a view is the
`Fp.toNat` of one trace column at one row (the extraction builds the view from
column values), and `Fp.toNat_lt`.  No constraint is needed.  (Computed
message components such as `depth + 1`, `u + 1`, offsets are *not* required to
be `< P`; only view fields are.)

## R-L6d-2 (L6-link): `RcptV.Wf.arith` must not assume `Bytes8 x.ramt` for refund-free receipts — APPLIED on `lane/zk-L6-link`

**Problem.** `arith` is stated under `Bytes8 x.gp → … → Bytes8 x.burnt →
Bytes8 x.ramt → …`.  Linking discharges each `Bytes8` from the SHA table's
range check of the message the bytes are emitted into.  `ramt` is emitted only
into the refund receipt (`RF`, `encRefund`), i.e. only when `x.hr = true`.  For
a receipt with `hr = false`, nothing range-checks `ramt` (the table's
convolution `ramt = G·sur` with `sur = 0` and 11-bit carries admits
`ramt_0 = −256·c_0 mod p`, not a byte), so `arith` is vacuous for it.

*Counterexample.* Honest views, but in a refund-free receipt `r` set
`ramt[0] := 256` (no message carries `ramt`, so traffic and balance are
unchanged; `RcptWf.canon` holds).  Then `arith` of receipt `r` is vacuous, and
`burnt`, `hr`, `aft`, the running `toks` of `r` are unconstrained by
`RcptWf`; changing `burnt` (consistently in `PEO(r)` and the SHA counts) gives
views satisfying every hypothesis of `LinkStmt` whose outcome root is not the
honest one, so no `Ext` satisfies `Good`.

**Fix (minimal).** In `RcptV.Wf.arith` replace the hypothesis
`Bytes8 x.ramt` by `x.hr = true → Bytes8 x.ramt`.

**Why it is provable from the table.** The only conclusion that mentions
`ramt` is `x.hr = true → leN' x.ramt = G·(gp − min gp bgp)`, which is vacuous
when `hr = false` and has the hypothesis back when `hr = true`; the other
conclusions (amount, storage, `ge`, `burnt`, `hr ↔ surplus ≠ 0`, `tok`) are
derived from columns other than `ramt` (`hr` is `[sur ≠ 0]` by an inverse,
`sur_i = ge·D_i`), so their table proofs do not use the range of `ramt`.

## R-L6e-1 (L6-render): `Good` must bound the number of touched nodes — OPEN

**Problem.** `AcctLocalStmt` (part of `RenderObligations`) is false as stated:
`Good c e` does not bound the number of touched nodes of `e.ns`, but the
`acct` table has one 16-row segment per touched node and `maxLog = 12`
(at most 256 segments).

*Counterexample.* One receipt, and a revealed trie whose root branch has
257 revealed children, each a touched leaf (leaf `k` with a 1-nibble key
under branch slot ... — e.g. a two-level branch tree with 257 leaves), all with
valid 72-byte AccountV1 values; the claim computed from the `Ext` as in
`test/NearRenderTest.lean` (`mkClaim`).  Every field of `Good` holds
(`size`: 257 leaves are far below `maxWitnessBytes`; the receipt's walk reaches
one of the leaves), but the honest `acct` table has `257·16 = 4112 > 2^12`
rows, so `TableLocal.log_le` fails.  (No trace at all is accepted for such an
`Ext`: `VSLOT` forces one `acct` segment per touched node.)

**Fix (minimal).** Add to `Good`

```lean
  touched_le : (e.ns.filter NodeRec.touched).length ≤ Params.maxBatch
```

(`Render.TouchedLe e`, `Render/Proof/AcctFacts.lean`).  The pruning
(`GoodCompleteStmt`) produces exactly the receivers' slots, at most
`receiptCount ≤ maxBatch` of them.  Soundness: from the `acct` view
(`AcctWf`/`acctTraffic`, `≤ 2^12/16 = 256` segments) and `VSLOT` balance
(node sends `VSLOT (k)` once per touched node, acct receives once per segment).

Proved meanwhile: `acctLocal' : AcctLocalStmt'` (= `AcctLocalStmt` with the
extra hypothesis `TouchedLe e`) and `acctLocal_of : (∀ c e, Good c e →
TouchedLe e) → AcctLocalStmt`.

**Related (not yet checked in detail).** The same kind of bound is missing for
the `node` and `sha` tables (`maxLog = 22`): `Good.size` bounds the revealed
*bytes* (`≤ 3·10^6`), but each node costs `node` rows per serialized byte and
`sha` rows per 64-byte block of its two serializations plus `≥ 36` rows per
node (two messages, at least one block of 17 rows each, plus start rows).  A
trie of ~10^6 tiny nodes (e.g. childless, valueless branches of a few bytes)
satisfies `Good.size` but would need `> 2^22` `sha` rows.  Fix: bound the
node count in `Good` (or make `size` count a per-node overhead).
