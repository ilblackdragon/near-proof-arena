# The D3 fixture → joint proof → recursion chain: where it actually breaks (2026-10-21)

Working log for the session that tried to build "a real succinct proof of a D3 fixture, joined,
then recursed". Written as evidence, not as a plan: every claim below was checked against the
tree on `main` @ `a680c2036`, not against a lane's README.

Labels: **[M]** measured in this session, **[K]** kernel-checked/proved, **[S]** stated (a `Prop`).

## 0. The session's own baseline correction [M]

The checked-in Rust KAT binary and `wasmbase-tool` were **both stale**, and each produced a
different false failure mode:

* the tracked `nearproof-wasm-base` gave **74/97** (panic at `tracegen.rs:428`, predating the REG
  chip);
* a fresh Rust build gave **87/97** — the last 10 were the *Lean export* being stale: `HOSTB` has
  **10** columns in `HostChip.lean` (`… , "act", "f", "reg"`) but the export had 9, so tracegen
  panicked with `HOSTB: no col reg`;
* after `lake build wasmbase-tool` too: **97/97**.

This is the handover's "stale binary" trap, twice over, plus a third instance in the *other*
artifact. `main` already added `bin.sh` age/refresh guards in `6bc2bb179`; that does not cover
`wasmbase-tool`. **Rebuild both after any Lean table change, and check the *exported column list*,
not just the KAT count.**

## 1. No real D3 contract is in the Wasm base-layer domain [M]

`WasmBase/Check.lean` `kindOf` has **no** `.if_` / `.else_` case, so `analyze` returns `none`:

| contract | `if` count | `loop` count | in domain? |
|---|---:|---:|---|
| `d3tiny` (345 B) | 1 | 0 | **no** |
| `ttn2` (1055 B) | 12 | 1 | **no** |
| `d3hostx` (1109 B) | 4 | 0 | **no** |
| `d3rich` (5603 B) | 77 | 6 | **no** |

Minimal probes [M]: `(i32.const 1) (if (result i64) … )` → `eligible:false`; a hand-edited
`d3tiny` with the `if` clamp replaced by `select` **is** eligible (22 rows).

So of the 108 honest public D3 fixtures that execute ≥1 `FunctionCall`, **zero** have a
domain-eligible contract today.

## 2. No storage host exists in the fixed host table [M]

`HostChip.lean` `hostFns` = base ∪ promise ∪ ctx ∪ log/reg ∪ hash. `storage_write`, `storage_read`,
`storage_has_key`, `storage_remove` are **absent** (`grep -c storage_write` = 0). `tools/host-fns/
canonical.txt` lists them at ids **59/57/53/58**, which **collide** with the hash ids 53–56 already
in `hostFns`; the two id schemes in the handover (§"Merge lessons" 1) are still unreconciled for
the storage and hash families.

Probe [M]: the `select` version of `d3tiny` **with** `storage_write` re-added → `eligible:false`.

## 2a. The Rust byte-payload branch is dead *and* wrong [M]

`tracegen.rs:644` emits the `log_*/value_return` byte-payload group when
`[8u64, 9, 10, 15].contains(&hid)`, but `HostChip.lean`'s `hostByteIds` is `[45, 46, 47, 50]`. The
real ids in the Lean table are `log_utf8 = 45`, `log_utf16 = 46`, `panic_utf8 = 47`,
`value_return = 50`; ids `8, 9, 10, 15` are `promise_create`, `promise_then`, `promise_and`,
`promise_batch_action_deploy_contract`. So the branch is **unreachable** for a real log call: probe
[M] `logkat` has `hosts = [(45,2,[5,0]), (46,2,[4,8]), (50,2,[5,0])]` and none matches, so HOSTB
falls through to the 4-byte placeholder instead of carrying `hello` / `h\0i\0`.

It is also **argument-swapped for when it is fixed**: `let (ptr, blen) = (args[0], args[1])`, but
the spec is `utf8H len ptr` → `readMemH ptr len` (`Host.lean:128-133`), i.e. `args[0] = len`,
`args[1] = ptr` (probe: `args = [5, 0]` with `memory[0..5] = "hello"`). Correct is
`let (blen, ptr) = (args[0], args[1])`.

The KAT cannot see either problem: it checks constraints and bus balance, and an absent HOSTB group
leaves the bus balanced. This is the "test passes, meaning is missing" class the handover warns
about.

## 3. There is no D2/D3 AIR [M]

`grep -rn "def nearAirV3.* : AirP"` returns exactly two: `nearAirV3` (D0a, 25 tables) and
`nearAirV3D1` (D1, 33 tables). There is no `nearAirV3D2`/`D3` and no `rcptV3D2`/`rcptV3D3`
(`grep` count 0). D1 is transfer-only (`TxD1.lean`, `w.no_code`), so a D3 chunk's Delegate / Stake /
AddKey / DeployContract receipts have no table.

## 4. The D3 state half is Lean-only [M]

`NearV3/D3/*` proves `cdWalkV3`, the upsert, the write log and their links. There is **no render**
and **no AIR instance**, and `upsert` is hard-coded at `[0,15]` as a constraint polynomial
(handover §"Still open for the join"), so wiring it to a ContractData key is a table
parameterisation, not an instance.

## 5. The "join" theorem as drafted is a rewrite, not a join [K]/[S]

> **CORRECTION, 2026-10-22.** This section describes the *untracked worktree draft* as it stood at
> 15:00 on 2026-10-21. What actually landed (`f8c4ceb91`, 16:07) is materially different and is
> **not** a rewrite: `coverage` quantifies over an **arbitrary** state-side answer function `sa`,
> takes its agreement with the Wasm run as a hypothesis, and `patchArm_eq_d3` proves the patched
> hook *is* `d3Hooks`. It compiles (no `maxHeartbeats` timeout) with axioms
> `[propext, Classical.choice, Quot.sound]`, and the module is in the root import list.
> Verified 2026-10-22; see `docs/logs/pq-lane-status-2026-10-22.md` §"Correction 1". The two real
> obligations are named (`hagree`, `hstate`), which is the honest state. The paragraphs below are
> kept as the record of what the draft did, not as the current verdict.

`lane/pq-runcall-fold` (worktree only; `Fold.lean` and `Coverage.lean` are **untracked**) proves

```
coverage (cfg) (cb w) (sa) : ArmAgrees cfg sa → StateSide cb w sa → RelD3 cb w
```

with

```
ArmAgrees cfg sa := ∀ …, sa … (.fcall …) = (d3Hooks cfg).functionCall … (.fcall …)
StateSide cb w sa := checkD2Core (patchArm sa) true cb w (some gAlpha) = .ok ()
```

`StateSide` *is* `RelD3` given `ArmAgrees` (`checkD2Core_patch` is `rw [patchArm_eq_d3 hh]`), and
`ArmAgrees` is exactly the equality the theorem then uses. So the theorem is `h ∘ rfl`: it does not
relate a Wasm proof or a state proof to anything. This is the **same defect** the file's own header
correctly diagnoses in `PQ/StatePort/JoinFold.join_additive` (vacuous), reproduced one level up.
What is real in the lane is `Fold.checkD2Core_patch` (a genuine fold: the pipeline reads the hook
only at `.fcall`) and `runCall_eq_done`.

Also [M]: `Coverage.lean` **does not compile** — `timeout at isDefEq, maxHeartbeats (800000)` at
the `coverage` proof. The lane's "all files have 0 `sorry`" is true but the file is not built.

## 6. What this means for the chain

| link | state |
|---|---|
| a real D3 contract in the Wasm domain | **done for simple contracts** (`4b76945a6`): `d3tiny` and `d3hostx` are eligible and replay through the AIR. `d3rich` still blocked on `loop`/`memory.grow`, a different AIR |
| a D2/D3 AIR for the chunk's non-call traffic | **missing** |
| a D3 render for contract-data state | **missing** (render + `upsert` parameterisation) |
| the join Wasm ⇄ state | **real conditional, proved** (`f8c4ceb91`); premises `hagree`/`hstate` open |
| recursion over a D3 base proof | blocked on the above (only D0a has been recursed: 299,967 B) |

There is no path from a public D3 fixture to a proof today. The nearest real, measured artifact
remains the D0a packet (`research/near-compression/results/pq-chunk-e2e/d0a-h10004-s3`,
**299,967 B**, 33 bytes under the gate).

## 7. What this session landed (lane `pq-if2`, commit `55fab1e0f`)

`research/near-compression/wasm-base-lean/WasmBase/StepIf.lean`, in the `WasmBase` library closure
(`lake build WasmBase` 145 jobs), KAT **97/97** unchanged:

| lemma | statement | axioms |
|---|---|---|
| `step_if` | the spec pops the condition, takes `pc + 1` on non-zero and `tgt` otherwise (the `else` body, or the `end` itself with no `else`), pushing the `end` label | std3 |
| `step_else` | unconditional jump to the label the `if` pushed; consumes no channel value | std3 |
| `popN_snd` | `(popN s).2 = { s with stack := s.stack.pop }` | std3 |

`popN_snd` is the finding, not boilerplate: `exec`'s `.if_` arm builds its successor out of a
`match popN s`, which is **not** definitionally a record update, so no `rfl`/`congr`/`simp` closes
the `exec` comparison without it.  That single conversion is what blocked an earlier attempt.

### What is still open for `if` (in dependency order)

1. **AIR selector.** `if` falls through on non-zero; `Ctrl.fJif` (`br_if`) jumps on non-zero.  The
   polarities are opposite, so `fJif` cannot be reused and `CTRL` must stay byte-identical — the
   repo's pattern is a separate table (`ChiAir`, `ShaAir`).  A new `IF` table with
   `pc' = if c = 0 then tgt else pc + 1` is the shape; `else` is already `fJump` (no new selector).
2. **Row lemma + soundness** for that table (mirror `RowCtrl.lean`'s five-branch structure).
3. **Checker extension** (`analyzeIf`/`verifyAtIf`/`recordAtIf`/`checkModuleIf`), mirroring
   `HostCheck.lean`'s "extend, don't touch `check`" discipline, producing exactly `step_if`'s
   hypotheses (`hflT`, `hpush`, `hsz`, `hsb1`).
4. Rust `tracegen` + the tool's opcode map, then a KAT program with a real `if`/`else`.

Estimating 1-2 from the `RowCtrl` size (a new table, not a new branch) and 3-4 as mechanical.

### Correction to §5 (the join)

> **SUPERSEDED, 2026-10-22.** The paragraphs below were true of the untracked draft. The merged
> `Coverage.lean` (`f8c4ceb91`) compiles and is a genuine conditional over an arbitrary `sa`; only
> the two named premises (`hagree`, `hstate`) remain unproved. See the correction at the head of §5
> and `docs/logs/pq-lane-status-2026-10-22.md`.

`lane/pq-runcall-fold`'s `Fold.lean`/`Coverage.lean` remain **untracked and non-compiling**
(`maxHeartbeats` at `coverage`), and `coverage` is still `ArmAgrees -> StateSide -> RelD3` where
both premises already assume the conclusion.  Nothing in this session changes that verdict: the
join is not a proof yet, and `Fold.checkD2Core_patch` (the real fold) is the only reusable piece.
