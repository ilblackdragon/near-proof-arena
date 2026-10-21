# Wasm ↔ state join: the interface the two lanes must agree on

Lane `pq-state-port`, 2026-10-19; host-wire shapes revised 2026-10-21 (lane `pq-actionr`, see §3).

**Status of §3 (2026-10-21):** the message shapes below are now the *current* wire, not a
proposal. `zk-formal/ZkFormal/PQ/Join/Statement.lean` was migrated to them; before that it
declared the pre-widening 8/4-field shapes and the join could not balance. The old shapes survive
as `hostQOld`/`hostBOld`, only to keep `hostQ_no_bridge`/`hostB_no_bridge` meaningful.

Companion to `Join.lean` (the proved bus partition) and to `pq-wasm-base`
`results/pq-wasm-base/README.md` §14 (the design note this narrows to signatures).

Scope: this is the **interface**, not the implementation.  It fixes (a) the bus ids and message
shapes both sides must agree on, (b) the exact Lean signatures each side's theorem must expose, so
the two can be composed without either side re-deriving the other, and (c) the order of work.
Everything below is either already in the tree (cited) or a small, named addition.

## 0. What is proved today

| piece | status | where |
|---|---|---|
| classical buses all `< 128`, Wasm buses `0–6` | **proved** (kernel) | `Join.lean`: `nearAirV3_buses_below_128`, `nearAirV3D1_buses_below_128` |
| the two ranges cannot collide | **proved** | `Join.lean`: `join_partition` |
| SWIRL relation of the classical AIR ⇒ `HoldsP` | **proved** | `Bridge.lean`: `holdsP_of_swirl` |
| D0a/D1 accepted ⇒ `GoodV3` / `RelD1a` | **proved** | `D0a.lean`, `D1.lean` |
| Wasm execution ⇒ spec run | **proved** (other lane) | `pq-wasm-base`: `wasm_base_sound` |
| HOST chip, HOST buses | **not built** | this doc, §2 |

So the join's AIR-side risk is gone.  What is left is one new chip plus two theorem signatures.

## 1. Bus map (fixed)

| family | buses | who fixes it |
|---|---|---|
| Wasm `STATE`/`FETCH`/`STK`/`R16`/`BYTE`/`DATA`/`FUNC` | 0–6 | `WasmBase/Chips.lean:35-41` |
| classical state tables, after the port's `+128` | 128–203 | `Join.lean` (proved `< 128` before the shift) |
| **new** `HOSTQ` (Wasm → state, requests) | **208** | this doc (revised) |
| **new** `HOSTR` (state → Wasm, responses) | **209** | this doc (revised) |
| **new** `HOSTB` (byte payloads, both ways) | **210** | this doc (revised) |
| free | 10–127, 204–207, 211+ | reserved |

**Revision (2026-10-20).** The first version of this table said the classical range was
`128–199` and put the host buses at `200/201/202`.  That was **wrong and unsound**: the 33-table
D1-a7b export uses classical buses **72–75** (`v3-d1-a7b/conformance/out-v2/nearAirV3D1.json`),
so after `+128` the classical range reaches **203**, and `200/201/202` would have collided with
classical buses 72/73/74.  A colliding bus merges two unrelated multiset constraints, which is a
soundness bug.  The 25-table D0a and 30-table D1 exports do stop at bus 71 (range 128–199), which
is why the mistake was not caught here; `pq-d3-join`'s `results/pq-d3-join/BUS-NUMBERING.md`
caught it.  The corrected allocation is **208/209/210**, matching `PQ/Join/Statement.lean`.

`BUS_OFFSET = 128` in the driver and `busOffset` in the Lean tool produce 128–203 across the
variants (a7b reaches bus 75), so the new buses start at 208 and need no change to either family.

**Why one `HOSTB` and not one per direction.**  The bytes of a request (key, value, args) and of a
response (register contents, `storage_read` value) never travel in the same host call, and `ts`
disambiguates them: `(ts, pos)` is unique per direction.  `HOSTB` matches D1's `VBYTES`
`(vid, pos, byte)` shape with `vid := ts`, so the state side can consume it with the trie-walk
machinery it already has (`WalkV3`, `KEYNIB`).  This is the key reuse decision.

## 2. The HOST chip (the one new AIR)

**Built** — `research/near-compression/wasm-base-lean/WasmBase/HostChip.lean`.  One row per host
call, on the Wasm side.  Columns: `act, hid, np, ar, st, nres, ga0..3, r0..3`, the `np` argument
flags `pf j`, and the `nArgs = 9` argument slots `tagP j, P j _0..3, tP j, hP j` (see that file's
`cols`).

Constraints (per row, degree ≤ 4): `act`, `st`, `ar`, `pf j` are bits; `pf` is prefix-closed
(`pf (j+1) · (1 − pf j) = 0`); `np = Σ pf j`; `nres = (1 − st)·ar`; the 16-bit limb pairs are in
range through `RANGE16`; an absent argument's tag and limbs are zero.

1. **request**: send on `HOSTQ` the message
   `[ts, hid, S, np, (aLo j, aHi j) for j < 9]` with count `1`, where `aLo j = P j₀ + 2¹⁶·P j₁`
   and `aHi j = P j₂ + 2¹⁶·P j₃` are the two 16-bit words of argument `j` (`HostChip.lean:305`).
   **22 fields.**
2. **response**: receive on `HOSTR` the message `[ts, st, rLo, rHi, gLo, gHi, ar, 0]`.  **8
   fields.**  The seventh field is the signature's `ar`, not zero.
3. `st = 0` (ok) ⇒ the row after pushes `nres = ar` results and continues at `pc+1`;
   `st = 1` (host abort / gas) ⇒ the run traps with `g := g_after`.
4. the budget register (channel space 6) is `g := gLo + 2¹⁶·gHi` after the row.

Responses are served inside the trace by a witness oracle `HOSTO`; the join replaces it with the
state tables on the same buses.  The Wasm side never learns *how* the host answered; it learns only
`(st, results, gas)`.

## 3. `HOSTQ` / `HOSTR` / `HOSTB` message shapes

**Revised 2026-10-21 (lane `pq-actionr`).** The first version of this section had the narrow
8-field `HOSTQ` and the 4-field `HOSTB` from before the chip was widened.  Those shapes cannot
balance against the chip; `PQ/Join/Statement.lean` is now migrated to the shapes below, and that
file's `hostQOld`/`hostBOld` + `hostQ_old_not_current`/`hostB_old_not_current` (and
`Receipt/Ids.lean`'s `hostQ_no_bridge`/`hostB_no_bridge`) keep the gap as a proved `≠`.

```
HOSTQ  [ts, hid, S, np, (aLo j, aHi j)_{j<9}]   one per host call   22 fields
HOSTR  [ts, st, rLo, rHi, gLo, gHi, ar, 0]      one per host call    8 fields
HOSTB  [ts, hid, dir, pos, byte]                 one per payload byte 5 fields
```

`ts` is the Wasm execution time (strictly increasing per host call), `hid` the fixed host-table id
(the same value the request carries), `S` the instruction gas so far, `np` the call's arity
(`≤ 9`), `dir` `0` = request byte (Wasm → state) / `1` = response byte (state → Wasm), `pos` the
byte offset within the call's payload, `ar` the signature's result count (`0` or `1`).  `st`: `0`
ok, `1` host abort/gas.

The join's Lean spelling (`PQ/Join/Statement.lean`): `hostQ ts hid S np a`, `hostR ts st r gAfter
ar`, `hostB ts hid dir pos byte`; `hostQ_width`/`hostR_width`/`hostB_width` are their widths, and
`hostQ_header` shows fields 0–3 are `(ts, hid, S, np)` — which is what lets the state side tie a
byte group to its call by `(ts, hid)`.

**Byte arguments.**  A host call with a byte payload (key, value, account id, args, log, return
data) emits `HOSTB` rows with contiguous `pos < len`; the state side joins them by `(ts, hid, dir)`
and checks `pos` is exactly `0..len−1` with no gaps or duplicates (`Wire.bytesWellFormed`).  Reads
(`storage_read`, `input`, context getters) run the other way: the state side **sends** `HOSTB`, the
Wasm MEMIO rows **receive** it into space 6.

**Gas.**  `S` at the row is the instruction gas so far.  The state side reproduces `sync`
(`burned += R · (S − S_prev)`) and returns the new budget `g_after` as `(g_lo, g_hi)` in `HOSTR`.
Gas exhaustion inside the host is `status = 1`, and the Wasm side treats it as a trap with the
remaining budget as the state value — the same shape `wasm_base_sound` already proves for
instruction-level traps.

## 4. The two theorem signatures to compose

### 4.1 State side (this lane; already available)

`D1.pq_d1_rel` (and `D0a.pq_d0a_rel`):

```
pq_d1_rel :
  ExtractD1Stmt →
  prepD1 cb hint = ok p →
  |preparedBytesD1 p 0| < p →
  multBoundP nearAirV3D1 < p →
  SwirlRel off nearAirV3D1 pv tr tape →
  VdChecks off nearAirV3D1 (pubOf …) pv tr tape →
  (∀ s ∈ pubSegs, 1 ≤ s.width) →
  (∀ t i, i.mult.length ≤ 25) →
  ∃ w, RelD1a B0 cb w
```

`HOSTQ`/`HOSTR`/`HOSTB` are *additional* SWIRL buses.  A `VdChecks` produced for the joined AIR
already balances them (they are ordinary buses), so the state side needs no new Lean theorem to
*carry* the host traffic — only to *produce* it, which is the new storage/receipt tables' job.

### 4.2 Wasm side (other lane)

`wasm_base_sound` today takes `Holds (wasmBaseAir nloc ncode) pub tr`.  For a run that calls a host
function we need the relative form:

```
wasm_base_sound_host :
  Holds (wasmBaseAirHost nloc ncode nhost) pub tr →
  PubOK … → CodeOK X tr → FuncOK X tr →
  HostOK X tr →                     -- NEW: every HOST row's (host_id, np, ar) matches the table
  HostResp X tr resp →              -- NEW: the response the row received is `resp ts`
  … same size/gas/entry side conditions …
  ∃ sN, runHost X.cfg X.p (N−1) s0 resp = .fin sN ∧ … (the same conclusion shape)
```

`HostOK` is a per-row check (like the existing `CodeOK`): the row's `host_id` is in the bound
table, `np`/`ar` are its signature, and the response message it consumed is exactly `(ts, resp ts)`.
`HostResp` is an **abstract host-response function** `Nat → (status, results, g_after, bytes)`.

### 4.2a The gas invariant is the real blocker (verified)

`WasmBase.RelW.gas` is `R · S + s.gas.g = g0`: the remaining budget is a function of the
instruction counter and the *fixed* initial budget.  A successful host call replaces the budget by
`g := remaining` (`NearSpecV3/Wasm/Machine.lean:149`, `remaining = prepaid − used`), which is
**not** a function of `S` and `g0`.  So `RelW.gas` cannot be re-established after a host call, and
`wasm_base_sound`'s top-level conclusion
(`R · S + sN.gas.g = g0`, `Main/Final.lean:100`) no longer holds in that form.

This is why `pq-host-chip` recorded "the top-level gas invariant has to be generalised before a
host-aware `wasm_base_sound` can be stated" (`StepHost.lean` header), and it is confirmed here
against the spec: the invariant shows up in ~112 places across `WasmBase/{Step*,Main/*}.lean`, so
the generalisation is mechanical but broad.  The natural replacement is to carry the invariant
only *between* host calls (a per-segment `R · (S − S_seg) + g = g_seg`), with `g_seg` fixed by the
state side at each host boundary — exactly the `S_prev`/`g_after` pair the HOST chip already puts
on `HOSTQ`/`HOSTR`.

That abstraction is the whole point: the Wasm proof is relative to `resp`, and the state proof
discharges `resp` by building the actual trie reads/writes, gas and receipts.  Neither side embeds
the other.

### 4.3 The composition (`runCall` fold)

```
joined_chunk :
  RelD1a B0 cb w            (from the state proof, §4.1)
  + wasm_base_sound_host …  (from the Wasm proof, §4.2, for each FunctionCall action in `w`)
  + the two proofs balance HOSTQ/HOSTR/HOSTB against each other
  ⇒ the D3 chunk relation (D2's `ActionHooks.functionCall` filled by `d3Hooks`)
```

The last line is the **coverage theorem** (gap-analysis §2.6): `d3Hooks` already implements the
FunctionCall arm on top of `Wasm.runCall` (`NearSpecV3/D3/FunctionCall.lean:370`); the fold shows
that the joined proof's data is a valid `ActCtx`/`ActSt`/`AR` sequence for it.  That is a statement-
level induction over the action list, not a new AIR fact.

## 5. Order of work (dependency-correct)

1. **HOST chip + `HOSTQ`/`HOSTR`/`HOSTB` in the Wasm AIR** (weeks).  Blocks everything else.
   - `check` support for `call` of an import: OP_HOST records, a host signature table.
   - the HOST chip itself (§2), the MEMIO byte mover, register space 6, the `g_after` budget.
   - a trace generator + KATs, as `pq-wasm-base` did for families 2–4.
2. **`HostOK` / `HostResp` + `wasm_base_sound_host`** (part of 1's Lean work).
3. ~~**The state-side host tables**: contract-data storage reads/writes on the trie buses.~~
   **Proved for the walk half** (`PQ/Join/ContractDataView.lean`): `cdWalkV3` is `walkV3` with the
   key-nibble bus renamed, and the rename is *inert* on every other bus (`rowInterSum_rename_other`,
   `cdWalkV3_inert`), so all `walkV3` constraint/width/`maxLog`/traffic lemmas transfer verbatim.
   `W_CD = 2^21` clears every D1 walk id (`W_CD_clear`, no axioms), so a contract-data walk cannot
   be confused with a transaction/local/access-key/queue walk on `FINAL`.  The nibble-stream
   length is fixed by the key (`cdKey_nibble_count`).  The `val`/`ups` halves and the
   `RealStore.writes` ordering remain with the state render lemmas.
   **The nibble source is settled** (`PQ/Join/HostKeyNib.lean`): the `HOSTB` route, as this doc
   prefers.  `hostNibStream` splits the key bytes into `CDKEYNIB` symbols and
   `hostNibStream_syms` proves those symbols are `nibbles bytes ++ [SYM_END]` — the path
   `contractDataPath` walks.  `hostKeyNib_agrees_with_cdKib` proves the byte route and the
   `cdKibV3` relay route emit the *same* symbols, so the choice changes only where the bytes come
   from.  `hostRoute_needs_no_new_bus` records why it is the cheaper route: `CDKEYNIB = 76` is
   inside the state AIR's range, whereas the relay would need `B_CDPKEY = 77`, above
   `stateBusMax = 76`.
4. **The `runCall` fold / coverage theorem** (§4.3).  **Shape proved**
   (`PQ/Join/RunCallFold.lean`): `d3_only_execution` shows `d3Hooks` and `d2Hooks` agree on every
   action except `FunctionCall`, so the fold is a plain list induction (`fold_step`, `fold_of_all`)
   whose only interesting hypothesis is the `FunctionCall` arm.  What remains is that arm's
   relation (`WasmHalf` + `StateHalf`), not the fold structure.
5. **Statement plumbing**: carry `code_root`/`func_root`/`data_root` and the TAPE root up to V_d
   (the TAPE Lean side is done; the NV passthrough is Rust).

Steps 1–2 are the bulk and belong to the Wasm lane.  Step 3 is state-side and reuses the port.
Step 4 is new but small in code and large in care.  Step 5 is the recursion lane.

## 6. What would make this doc wrong

* If the Wasm side decides to model host functions *in-AIR* (not as an abstract `resp`), then
  `HostResp` disappears and the state-side storage tables are not needed for the call path — but
  the Wasm AIR grows by the host semantics (weeks more).
* If the state side delivers storage through a different mechanism (e.g. an in-AIR trie walk on the
  Wasm side), `HOSTB` is unused and the join bus count drops to two.
* If `ts` cannot be made unique (e.g. two host calls on the same row), `HOSTB`'s `(ts, hid, pos)`
  key breaks and a `(ts, hid, seq)` pair is needed instead.  The current chips have one host call
  per row, so this holds.  (`hid` is part of the key precisely so that a shared `ts` policy cannot
  splice one call's bytes onto another's.)

These are the decisions to confirm with the two lanes before step 1 starts.
