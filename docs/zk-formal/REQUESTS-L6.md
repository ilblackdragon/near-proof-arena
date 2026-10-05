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

## R-L6r-1 (L6-rcptview): `RcptV.Wf.tprev_le` is false for the table — OPEN

**Problem.** The table checks the memory-read time only by
`mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 57 9))`, i.e.
`r − tprev ∈ [0, 512)` **in `Fp`**.  Nothing else bounds the column `tprev`
(it is a receipt constant, used only in the `MEM` receive).

*Counterexample.* Receipt `r = 0` with `tprev = P − 1` and `xb 57 = 1`,
`xb 58..65 = 0`: `r − tprev = 1 = bitsX 57 9` in `Fp`; every other constraint is
untouched.  The view must have `tprev = P − 1` (the `MEM` message carries
`Fp.ofNat tprev`, and `small` asks `tprev < P`), so `tprev_le : tprev ≤ r`
fails.

**Fix (minimal).** `tprev_le : x.tprev < P - 512 → x.tprev ≤ r`.
Linking (`Link/Mem.lean` `tprev_eq`) already has `htime` (`tprev = 0` or
`tprev = r' + 1` with `r' < rs.length ≤ 256`) before it uses `hle`, so it can
discharge the new hypothesis there.  (Table side: `tprev + d ≡ r`, `d < 512`,
`tprev + d < P`, `r < P` ⇒ `tprev + d = r`.)

## R-L6r-2 (L6-rcptview): the storage clause of `RcptV.Wf.arith` is false for the table — OPEN

**Problem.** `q = 10^19 · st` is computed in the `DEP` rows by the convolution
`conv S_LE (c st) dl` over the 16 rows only (positions `0..15`, final carry
`bitsX 26 12 = 0`).  With `big = 1` nothing forces the high storage bytes to
vanish (`st_i = 0` for `i ≥ 2` is enforced only when `big = 0`), and the terms
`S_j · st_m` with `m + j ≥ 16` are never added.  Since `S_LE[0] = S_LE[1] = 0`,
`st_14` and `st_15` do not occur in any constraint at all.  What the table
proves is `q = (10^19 · st) mod 2^128` and `q ≤ aft + lk`.

*Counterexample.* An honest receipt with `big = 1` (`10^19 · stor ≤ aft + lk`)
where `st_15 := 1` (in the `DEP` row 15 column `st`, and correspondingly in the
`MEM` messages: they carry `st` unchanged).  All rcpt constraints still hold
(`q` is unchanged).  All `Bytes8` hypotheses of `arith` hold, but
`storageAmountPerByte · leN' st = 10^19 · (2^120 + stor) > aft + lk` and
`leN' st > 770`, so the storage clause is false.

**Fix (minimal).** In `RcptV.Wf.arith` replace
`Params.storageAmountPerByte * leN' x.st ≤ …` by
`(Params.storageAmountPerByte * leN' x.st) % Params.two128 ≤ …`.
Linking (`Link/RunChain.lean`) gets `st_i = 0` for `i ≥ 8` from the acct lanes
(`lanes`), hence `leN' st < 2^64` and `10^19 · leN' st < 2^128`, so the `% two128`
is the identity there.  (Alternative with the same effect: add the hypothesis
`leN' x.st < 2^64 →` to `arith`.)

## R-L6r-3 (L6-rcptview): `RcptV.Wf.arith` needs the block gas price bytes to be bytes — OPEN

**Problem.** `RcptWf.toks` instantiates `Wf` with
`bgp := leN' (pubBytes pub PV_BGP 16)`, which reads each public value mod 256
(`UInt8.ofNat`), while the table compares `gp` with the public field elements
themselves (`loads`: `reg j = pub (PV_BGP + j)` at the `GP` field start; borrow
chain `gp_i − reg0 = c1 + D_i − 256·b_{i+1}`).  The hypothesis
`bgp < Params.two128` of `arith` is always true for a `leN'` of 16 values, so it
does not help.

*Counterexample.* `pub[PV_BGP] = 256`, `pub[PV_BGP + i] = 0` (`i > 0`), a
receipt with `gp = 0`.  The borrow chain is satisfied with `D_0 = 0`,
`D_i = 255` (`i ≥ 1`), all borrows `1`, hence `ge = 0` (`p = gp = 0`,
`burnt = 0`, `sur = 0`, `hr = 0` — all constraints hold).  But
`leN' (pubBytes pub PV_BGP 16) = 0 ≤ leN' gp`, so `arith` claims `ge = true`.

**Fix (minimal).** Let `RcptV.Wf` take the bytes instead of the value:
`RcptV.Wf (x) (r) (bgpB : List Nat) (tok tok')`, in `arith` replace the
hypothesis `bgp < Params.two128` by `Bytes8 bgpB` and `bgp` by `leN' bgpB`; in
`RcptWf.toks` pass `pubBytes pub PV_BGP 16`.  Linking has
`Bytes8 (pubBytes (publicOf c) PV_BGP 16)` (`publicOf` is bytes).
