# Handoff prompt — lane `pq-host-memio` (2026-10-21)

Paste the block below into a fresh agent context. It is self-contained.

---

## MISSION

Finish lane `pq-host-memio` in the NEAR proof-arena repo, in the worktree
`/data/illia/nearproof-wt/pq-host-memio` (branch `lane/pq-host-memio`, already pushed).

Two parts, in order:

* **Part 1 (open):** prove `Register.RegLenAgree` — the REG group walk. The AIR constraints are
  already written and proved row-local; the whole-trace counting theorem is what is missing.
* **Part 2 (untouched):** give `HOSTB`'s `(ptr, len)` meaning — tie host-call bytes to linear
  memory (channel space 3) instead of leaving them free witnesses.

**Do not stop between part 1 and part 2.** Report at the end.

## HARD RULES

* Work ONLY in `/data/illia/nearproof-wt/pq-host-memio`. Never in `/data/illia/nearproof` (main
  checkout; other agents use it).
* Build ONLY with the heavy wrapper (the host OOM-crashed twice):
  `HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy lake build <Module>`
  run from `research/near-compression/wasm-base-lean`.
* **NO `sorry`, no `axiom`, no `native_decide`.** If you cannot finish a step, leave the file
  BUILDING and report how far you got. A green file with partial progress beats a red one.
* **`research/near-compression/native/wasm-base/target/` is git-tracked in this repo** (pre-existing
  oddity). Never `git add -A`; stage only `src/*.rs` and `wasm-base-lean/WasmBase/**`.
* Commit to `lane/pq-host-memio`; push. Do not merge to main.
* Before believing any test failure, rebuild the tools (see "Verification").

## WHERE THINGS STAND (committed, pushed, green)

`lane/pq-host-memio`, 2 commits on top of `319e9f889`:

* `0853b6685` — REG group-walk constraints + 10 row-local lemmas.
* `2e536d4b7` — range-check REG `pos` (a real soundness fix; see below).

State: `lake build WasmBase.Main.RegWalk` green (90 jobs); KAT 88/88 with real REG rows; REG tamper
99/99 (16 REG cases). No `sorry` anywhere.

### What already exists in `WasmBase/Main/RegWalk.lean` (use these)

| theorem | statement |
|---|---|
| `reg_walk_26` | index-26 plumbing: `26 < tables.length ∧ tables[26] = Reg.table` |
| `reg_walk_constraints` | alias of `reg_row_constraints` |
| `reg_act_bit` / `reg_kind_bit` / `reg_f_bit` | those columns are `0 ∨ 1` |
| `reg_byte_active` | `kind = 0` ⇒ `act = 1` (from `cByteAct`) |
| `reg_start_pos` | group-start byte row ⇒ `pos = 0` (from `cStartPos`) |
| `reg_byte_succ_not_start` | active byte row ⇒ successor `f = 0` (from `cOnlyLenEnds`) |
| `reg_pos_step` | successor is byte with `f = 0` ⇒ `nxt.pos = pos + 1` (from `cPosStep`) |
| `reg_last_byte` | successor is a length row (`kind = 1`, `f = 0`) ⇒ `blen = pos + 1` |
| `reg_len_const` | successor `f = 0` ⇒ `blen` constant |
| `reg_pos_le` | `pos ≤ r` (needed because `cPosStep` alone permits a field-level wrap) |

Note the argument shapes: `reg_pos_step` / `reg_last_byte` / `reg_len_const` take the **successor**
facts in `rowNat tr 26 ((r + 1) % tr.height 26) _` form and conclude in that same form. Call them,
then rewrite with `Nat.mod_eq_of_lt` — do not try to hand them un-modded indices.

## PART 1 — the remaining three steps

### Step 1.1 — `reg_r16_send_bits` (the missing `hsend`)

`reg_r16_query_16bit` in `WasmBase/Main/RegFacts.lean` needs

```
hsend : ∀ o ∈ occs (wasmBaseRegAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1
```

and **nothing supplies it for `wasmBaseRegAir`**. Neither `reg_recv_only_range16` nor
`occ_bits_host` gives it.

Write `reg_r16_send_bits` with that signature. Argument that works:

1. `mem_occs.mp` → `⟨t, ht, r, hr, i, hi, rfl⟩`.
2. Split `t < 26 ∨ t = 26` (from `reg_air_len : tables.length = 27`).
3. **`t < 26`** (a host-AIR table): all host tables *send* on R16, so a query there is a
   contradiction. Use `host_recv_only_range16` (exists, `WasmBase/Main/HostLinks.lean`). For
   "index ≠ 15 ⇒ table ≠ Range16" use `air_neq_range16` — **`air_get_15_eq_range16_iff` does NOT
   exist**, I invented it; derive `t = 15` from the table equality yourself.
4. **`t = 26`** (REG): kernel-verified, REG's six R16 interactions have counts exactly
   `[act·f, act·f, act·(1−kind), act, act, act]` (check with `#eval (Reg.table.inters.filter
   (fun i => i.bus = busR16)).map (fun i => i.count)`). With `act`, `f`, `kind` bits (from
   `reg_row_bits`), each is ≤ 1.

Traps I hit here (all avoidable):
* Rewriting `tables[t]` via `List.getElem_append_left` needs the *dependent* form; use
  `hsplit : tables = hostTables ++ [Reg.table]` then `rw [hsplit]` and `exact
  List.getElem_append_left hht`. Do not try to rewrite the value equality directly.
* `List.mem_filter` + `simp` to extract the count list shape: prefer stating the 6-element list
  literally and `simpa [Reg.table, Reg.inters, Reg.act, Reg.f, Reg.kind, ...]` — but check it closes.
* `nlinarith` is NOT available (no Mathlib). Use `omega` with the `< P` bounds in hand.
* `List.getElem_mem` for membership, and `absurd ... (by simp [hs])` to refute a send.

### Step 1.2 — `reg_pos_16` then `reg_pos_lt_len`

`2e536d4b7` added `r16 (v Reg.pos) (v Reg.act)` to `Reg.inters`. Prove:

```
reg_pos_16 : Holds … ⇒ act = 1 ⇒ pos < 65536
```

via `reg_r16_query_16bit` (feed it `reg_r16_send_bits`) plus the `hrecv` premise that RANGE16 answers
are indices `< 2^16` — model this on `Main/HostLinks.host_r16_sound`'s `hrecv` proof, which handles
RANGE16 specially with `host_range16_values`.

Then:

```
reg_pos_lt_len : Holds … ⇒ kind = 0 ⇒ pos < blen
```

**This is why the `r16 pos` lookup was added, and it is a genuine soundness fix, not cosmetics.**
`cPosLtLen` is `act·(1−kind)·(len − pos − 1 − gap) = 0`, i.e. `pos + 1 + gap ≡ len (mod P)` as a
*field* equation. With `len, gap < 2^16` but `pos` free, it is satisfied by `pos = P−1, len = 5,
gap = 4` (then `pos + 1 + gap = len + P`). So `pos < len` was **false** in the naturals before
`2e536d4b7`. With `pos < 2^16` as well, all three are `< 2^16` and the equation is exact:
`blen = pos + 1 + gap`, hence `pos < blen`. Write `blen = pos + 1 + gap` as a natural equation
(`natEq` + the cast bounds) and `omega`.

### Step 1.3 — `reg_group_walk`, then `RegLenAgree`

Prove:

```
reg_group_walk : Holds … ⇒ f = 1 ⇒ kind = 0 ⇒
  ∃ L, rowNat … r0 Reg.blen = L ∧
    (∀ i, i < L → rowNat … (r0+i) Reg.kind = 0 ∧ rowNat … (r0+i) Reg.pos = i ∧
                  rowNat … (r0+i) Reg.blen = L) ∧
    r0 + L < tr.height 26 ∧
    rowNat … (r0+L) Reg.kind = 1 ∧ rowNat … (r0+L) Reg.blen = L
```

**The induction shape that works** (I proved the row lemmas for exactly this):

* `let L := rowNat tr 26 r0 Reg.blen`; `reg_start_pos` gives `pos = 0` at `r0`.
* Induct on the offset `n` from `r0`, carrying **existence** of row `r0+n` alongside its byte facts.
  This is the crux: `reg_byte_not_last` needs the row to exist, and deriving existence from the walk
  is circular. Carry it.
* At each step: `reg_byte_active` → `reg_byte_succ_not_start` → `Nat.mod_eq_of_lt` (from
  `reg_byte_not_last`) → case on `reg_kind_bit` of the successor:
  * byte row → `reg_pos_step` (pos + 1) and `reg_len_const` (len constant);
  * length row → **exfalso**: `reg_last_byte` gives `L = n+1`, but we are in the case `n+1 < L`.
* Termination comes from `reg_byte_not_last` + `cFirst` (a byte row cannot be last), so the walk
  must reach a non-byte row inside the table. **You do not need `pos < len` for termination** — but
  you do want it (step 1.2) to refute a byte row at `n = L`.
* `Nat.find` does NOT exist in this core-only library. Use `Nat.rec` / strong induction, or the
  `∀ n, n ≤ L → …` helper pattern already used by `reg_pos_le`.

Then the message characterization and the deliverable:

```
regLenAgree_of_holds : Holds … ⇒ Register.RegLenAgree (msgs <reg AIR> tr pub busStk true |>.map decMsg) rid
```

Replace the stated `def RegLenAgree` in `WasmBase/RegisterSpace.lean` with the theorem (keep the def,
prove it). The authoritative message list is `msgs_flatMap` (`WasmBase/Extract/Occ.lean`) →
`rowMsgs Reg.table tr pub 26 r busStk true` per row, mapped through `decMsg`
(`WasmBase/Main/Rows.lean`). A byte row emits one `byteMsg rid pos byte ts`; a length row emits
`lenMsg rid len ts`. Combine with `reg_group_walk` so the count of byte messages equals `len`.

## PART 2 — HOSTB `(ptr, len)` → linear memory

### The gap

`Chips.HostB` (`WasmBase/HostChip.lean`) carries bytes on `busHostB = 210` as
`[ts, hid, dir, pos, byte]`, with `len`, `gap`, `act`, `f`, `reg`. `cPosLtLen` + `r16 gap` give
`pos < len` (for `len < 2^16`) — but **the byte value is a free witness**: nothing ties it to the
Wasm machine's linear memory. It is not even tied to the (ptr, len) the guest passed: `ptr` is not a
column.

Linear memory is channel space 3: one message `encB a x tp = ⟨3, a, 0, x, 0,0,0, tp⟩` per touched
byte (`WasmBase/Event.lean:197`), produced by MEMINIT at time 0, and **consumed and re-produced** by
every LOAD/STORE that touches it — see `Chips.Load.inters` for the exact pattern:

```
chRecv 3 (eaE + i) 0 [b_i,0,0,0] (tb+i) (cnt i)
timeChk (cTs) (tb+i) (hb+i) (cnt i)
chSend 3 (eaE + i) 0 [b_i,0,0,0] (cTs)   (cnt i)
```

### Proposed design (validate before committing to it)

Host functions with `(ptr, len)` in `(base, len)` = args: `log_utf8`(8), `log_utf16`(9),
`panic_utf8`(10), `value_return`(15) — see `Chips.hostFns`. Their request bytes are the memory
contents at `ptr+pos`.

* Add to HOSTB: `ptr` (two 16-bit cols, or a single col if you prove `ptr < 2^27` some other way — the
  AIR's `memBytes ≤ 2^27` bound is a statement-level fact, so two 16-bit limbs with `r16` is the
  safer route), `tp` (producer time), `hi` (time-check high limb).
* On a `dir = 0`, `reg = 0` row (a plain **request** byte), emit the LOAD-style pair
  `chRecv 3 (ptr + pos) 0 [bv,0,0,0] tp (act·(1−dir)·(1−reg))` then
  `chSend 3 (ptr + pos) 0 [bv,0,0,0] ts (act·(1−dir)·(1−reg))`, plus `timeChk ts tp hi` on the
  same count. A *read* (recv then re-produce) keeps the memory message alive, exactly like LOAD.
* Do **not** emit memory messages for `dir = 1` (state → Wasm) or `reg = 1` (register fills, which
  are register bytes, not memory).
* Counts must be bits (they are: products of `act`, `dir`, `reg`), so `perm_exact` applies.

### PREDICTED SECOND SOUNDNESS HOLE — check this first

`HostB.inters` looks up only `byte` and `gap`:

```
byteQ 0 (v bv) 0 0 (v act * (1 - v reg)),
r16 (v gap) (v act * (1 - v reg))
```

`len` and `pos` are **not** R16-checked. By the exact argument that forced `2e536d4b7`, `cPosLtLen`
on HOSTB is satisfiable with `pos = P−1, len = 5, gap = 4`. So HOSTB almost certainly needs
`r16 (v pos)` and `r16 (v blen)` too. Verify, then add them **and** the matching `st.r16(...)`
calls in `tracegen.rs`, or every HOSTB trace will fail the bus check (I hit exactly this with REG:
a query with no RANGE16 answer ⇒ `buses: unbalanced`).

### Rust generator sites to update (`native/wasm-base/src/tracegen.rs`)

Three places emit HOSTB rows; all need the new columns:
1. the register-fill HOSTB rows (~line 534) — `reg = 1`, must stay memory-free;
2. the log/return payload group (~line 609) — `(ptr, blen) := (args[0], args[1])`, bytes from
   `mem.get(ptr + pos)`; this is the one that becomes a real memory read;
3. the placeholder 4+4 byte stream (~line 620s) — `reg = 0`, `hid ∉ {8,9,10,15}`.

Padding rows for HOSTB are common-main zero columns with `act = 0, f = 1` — keep them valid.
Because HOSTB shares the common main trace, adding columns changes `airH`/`airR` widths; the KAT
regenerates `air*.json` from the Lean export, so rebuild `wasmbase-tool` first.

## VERIFICATION (do all of it)

```
cd research/near-compression/wasm-base-lean
HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy lake build   # whole lib + tool

cd ../native/wasm-base
./setup.sh && cargo build --release -j 8            # setup.sh may print a deps warning; fine
WASMBASE_BIN=$PWD/target/release/nearproof-wasm-base ./run_kat.sh /tmp/kat-memio
# expect: "KAT: 88 passed, 0 failed"
```

**KAT hygiene trap:** another agent works in this tree. If `programs/__pycache__` picks up their
in-flight `gen.py`, you will see phantom programs (`shakat*`, 97 instead of 88) and 11 spurious
"unexpectedly ineligible" failures. Confirm with
`python3 programs/gen.py /tmp/probe 8 64 | tail -1` → must be `88 programs`. This is not your bug.

Tamper (needs a matching air/prep pair — pick `airR-<nloc>-g<ngl>.json` from the prep's
`len(localTags)`/`ngl`; mismatched pairs panic on `pubs.len() != air.num_pub`):

```
./target/release/nearproof-wasm-base tamper /tmp/kat-memio/airR-0-g0.json \
  /tmp/kat-memio/progs/regkat.prep.json
# expect: "TAMPER summary 99/99 rejected" (or more, as you add cases)
```

Add tamper cases for anything new: for part 2 the obvious ones are a request byte whose value differs
from memory at `ptr+pos`, `ptr+1`, and a `len` larger than the memory region. For part 1 the walk
cases already exist (`REG[...].f=1 mid-group`, `pos+2 mid-group`, `len/rid/ts+1 mid-group`).

Finally: `#print axioms` each new headline theorem — must be a subset of
`[propext, Classical.choice, Quot.sound]`.

## PROJECT FACTS THAT WILL SAVE YOU HOURS

* **No Mathlib.** `sub_zero`, `mul_one`, `one_mul`, `norm_num`, `linarith`, `nlinarith` DO NOT
  EXIST. Use `grind`, `omega`, `simp only`, `rw`.
* The `set x := …` tactic does NOT exist. `Nat.find` does NOT exist. `by_contra` failed in this
  context once; prefer `rcases Nat.lt_or_ge a b with h | h` or `Classical.byContradiction`.
* `grind` alone closes `(1 : Fp) * ((1 : Fp) - 0) * x = 0 ⊢ x = 0`. It does NOT close it if you
  first `rw` an equation into the hypothesis — substitute the column first, then `grind`.
* **Literal-vs-name column mismatch is the main source of `rw` failures.** Worked idiom:
  `rw [show (4 : Nat) = Reg.pos from rfl] at h`.
* A constraint's `nv i` unfolds to `tr.cell 26 ((r+1) % tr.height 26) i`, while your hypotheses use
  `rowNat`. Bridge with `(Fp.cast_toNat _).symm`, then rewrite the `rowNat` value:
  ```
  have e1 : tr.cell 26 ((r + 1) % tr.height 26) 15 =
      ((rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : Nat) : F) := (Fp.cast_toNat _).symm
  rw [e1] at h
  rw [show (rowNat tr 26 ((r + 1) % tr.height 26) Reg.f : F) = 0 from by rw [hf']; rfl] at h
  ```
* `natEq : (L : Fp) = (R : Fp) → L < P → R < P → L = R` is the bridge to naturals;
  `rowNat_lt`, `bool_nat`, `zero_of_mul_nat`, `table_constr`, `P_val` (`P = 2013265921`),
  `Fp.toNat_cast_of_lt` are all in scope.
* **REG column indices:** `act 0, kind 1, rd 2, rid 3, pos 4, blen 5, bv 6, hid 7, ts 8, dir 9,
  gap 10, fresh 11, tp 12, hp 13, ptr 14, f 15`. (`Reg.len` does NOT exist — it is `Reg.blen`.)
* **INSERT `#trace_state` AND READ IT.** I burned dozens of turns guessing `omega`/`grind` calls.
  Print the goal, then choose. This is the single biggest process lesson from the previous session.

## WHAT THE PREVIOUS SESSION GOT WRONG (avoid repeating)

1. Four failed attempts at `reg_group_walk`, each defeated by a *different* structural mistake
   (circular induction; missing row existence; termination via `pos < len` instead of
   `reg_byte_not_last`; guessing tactics). The design above is the distilled correct one.
2. Two subagent attempts returned nothing useful (one empty, one whose work I discarded). If you
   delegate, verify the file actually changed before trusting the report.
3. I reverted work that contained a real insight (`reg_pos_le`) and had to rediscover it.
   Commit incrementally.

## DELIVERABLES

1. `Register.RegLenAgree` proved (no `sorry`), plus `reg_group_walk`, `reg_pos_16`,
   `reg_pos_lt_len`, `reg_r16_send_bits`.
2. HOSTB `(ptr, len)` bound to channel space 3, with the `pos`/`len` range checks if (as predicted)
   they are missing; generator updated; KAT green; tamper cases added and rejecting.
3. `research/near-compression/results/pq-host-memio/RESULTS.md`: what changed in each AIR, why
   (especially the two soundness holes), the measured cell/row cost delta, KAT/tamper counts, axioms.
4. A `docs/logs/pq-host-memio-*.md` lane log; note anything you found that a reviewer must know.
5. Update the lane row in `docs/HANDOVER.md` §"Parallel lanes to run next".
