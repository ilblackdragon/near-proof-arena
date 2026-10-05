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
