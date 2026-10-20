# pq-host-ctx — the D3α context / state-read host family

Lane `lane/pq-host-ctx`, cut from `main` @ `639387b1a`, 2026-10-20.

The 19 D3α "context / state-read" host functions:

```
account_balance, account_locked_balance, attached_deposit, block_index, block_timestamp,
chain_id, current_account_id, current_contract_code, epoch_height, gas, predecessor_account_id,
prepaid_gas, random_seed, refund_to_account_id, signer_account_id, signer_account_pk, used_gas,
validator_stake, validator_total_stake
```

## 0. The architectural fact this lane works with

`WasmBase/HostChip.lean` is **generic**: it never names a function.  A HOST row takes
`(hid, np, ar)` from the fixed table `Chips.hostFns` and passes the arguments and results through
`HOSTQ` / `HOSTR` to the abstract in-trace oracle `HOSTO`.  There is no per-function AIR to build.
So "covering" a context getter is exactly what the brief says:

* (a) the function is in `hostFns` with its **exact** arity from `NearSpecV3.Wasm.hostSigs`;
* (b) the state side has a stated contract: which field / byte string / memory range it must
  supply so the abstract `HostAnswer` on `HOSTR` is the answer the spec produces;
* (c) a KAT program calls it and the trace passes the constraint + bus pre-check.

**No new AIR.**  A context getter with `np ≤ 1, ar ≤ 1` needs no AIR obligation at all: its answer
is `status` + (at most) one word + `g_after` on `HOSTR`, and the chip already carries all three
(`HostOK` / `HostResp` in `WasmBase/Main/Host.lean` bind them to the abstract response).  What is
left is the *reduction* of the spec's `hostCall` to that answer, which is `WasmBase/HostCtx.lean`.

## 1. `hostFns` entries added (deliverable 1)

`WasmBase/HostChip.lean`.  Existing ids `0..7` are untouched (`Chips.hostFns_head_stable`, kernel).
New entries, appended in id order:

| id | name | np | ar | fits the row? |
|---:|---|---:|---:|---|
| 8 | `current_account_id` | 1 | 0 | yes |
| 9 | `chain_id` | 1 | 0 | yes |
| 10 | `signer_account_id` | 1 | 0 | yes |
| 11 | `signer_account_pk` | 1 | 0 | yes |
| 12 | `predecessor_account_id` | 1 | 0 | yes |
| 13 | `refund_to_account_id` | 1 | 0 | yes |
| 14 | `account_balance` | 1 | 0 | yes |
| 15 | `account_locked_balance` | 1 | 0 | yes |
| 16 | `attached_deposit` | 1 | 0 | yes |
| 17 | `random_seed` | 1 | 0 | yes |
| 18 | `current_contract_code` | 1 | 1 | yes |
| 19 | `gas` | 1 | 0 | **no — `i32` parameter** |
| 20 | `validator_total_stake` | 1 | 0 | yes |
| 21 | `validator_stake` | 3 | 0 | **no — `np = 3`** |

Arity agreement with the PV86 linker table is a kernel check, not a claim:

* `Chips.hostFns_arity_agrees` — every entry's `(np, ar)` equals `hostSig?`'s;
* `Chips.hostFns_types` — the parameter/result types also agree (`i64` everywhere except `gas`'s
  `i32` parameter);
* `Chips.ctx_all_listed` / `ctxNames_len` — all 19 are present.

The chip's `Host.constraints` and `Host.properties` are **not** touched: arity is not widened.

## 2. Per-function table (deliverable 4)

`needs AIR?` is "no" for every function: the answer is carried by the generic row.  `state supplies`
is the whole of the state-side obligation, and it is the hypothesis list of the named Lean lemma.
`status` is `covered` (in `hostFns`, callable, KAT program, reduction lemma) or `blocked` (in
`hostFns` with its true signature, rejected by the checker, no HOST row possible in this slice).

| function | np | ar | shape | spec body | state side supplies | AIR? | Lean lemma | status |
|---|---:|---:|---|---|---|---|---|---|
| `block_index` | 0 | 1 | A | `payBaseH base`; `pushRet ctx.blockHeight` | `blockHeight`, base charge ok | no | `block_index_ok` / `_err` | covered |
| `block_timestamp` | 0 | 1 | A | `payBaseH base`; `pushRet ctx.blockTimestamp` | `blockTimestamp`, base charge ok | no | `block_timestamp_ok` / `_err` | covered |
| `epoch_height` | 0 | 1 | A | `payBaseH base`; `pushRet ctx.epochHeight` | `epochHeight`, base charge ok | no | `epoch_height_ok` / `_err` | covered |
| `storage_usage` | 0 | 1 | A | `payBaseH base`; `pushRet st.storageUsage` | `St.storageUsage` (not `CallCtx`'s), base charge ok | no | `storage_usage_ok` / `_err` | covered |
| `prepaid_gas` | 0 | 1 | A | `payBaseH base`; `pushRet ctx.prepaidGas` | `prepaidGas`, base charge ok | no | `prepaid_gas_ok` / `_err` | covered |
| `used_gas` | 0 | 1 | A | `payBaseH base`; `pushRet gas.used` | the budget's `used = burnt + promises`, base charge ok | no | `used_gas_ok` / `_err` | covered |
| `account_balance` | 1 | 0 | B | pop ptr; `payBaseH base`; `setU128H ptr balance` | `balance`, and `ptr + 16 ≤ memBytes` | no | `account_balance_ok` / `_err` | covered |
| `account_locked_balance` | 1 | 0 | B | pop ptr; `payBaseH base`; `setU128H ptr ctx.accountLocked` | `accountLocked`, `ptr + 16 ≤ memBytes` | no | `account_locked_balance_ok` / `_err` | covered |
| `attached_deposit` | 1 | 0 | B | pop ptr; `payBaseH base`; `setU128H ptr ctx.attachedDeposit` | `attachedDeposit`, `ptr + 16 ≤ memBytes` | no | `attached_deposit_ok` / `_err` | covered |
| `validator_total_stake` | 1 | 0 | B′ | pop ptr; `payBaseH base`; `payBaseH validatorTotalStakeBase`; `setU128H ptr Σ validators` | the validator table (not a trie read), `ptr + 16 ≤ memBytes` | no | `validator_total_stake_ok` / `_err` | covered |
| `current_account_id` | 1 | 0 | C | pop id; `payBaseH base`; `regSetH id ctx.currentAccount` | the byte string `d`, the register id, `regSetH`'s domain | no | `current_account_id_ok` / `_err` | covered |
| `chain_id` | 1 | 0 | C | pop id; `payBaseH base`; `regSetH id ctx.chainId` | as above, `d = chainId` | no | `chain_id_ok` / `_err` | covered |
| `signer_account_id` | 1 | 0 | C | pop id; `payBaseH base`; `regSetH id ctx.signer` | as above, `d = signer` | no | `signer_account_id_ok` / `_err` | covered |
| `signer_account_pk` | 1 | 0 | C | pop id; `payBaseH base`; `regSetH id ctx.signerPk` | as above, `d = signerPk` (32/64/1952-byte Borsh PK) | no | `signer_account_pk_ok` / `_err` | covered |
| `predecessor_account_id` | 1 | 0 | C | pop id; `payBaseH base`; `regSetH id ctx.predecessor` | as above, `d = predecessor` | no | `predecessor_account_id_ok` / `_err` | covered |
| `refund_to_account_id` | 1 | 0 | C | pop id; `payBaseH base`; `regSetH id ctx.refundTo` | as above, `d = refundTo` | no | `refund_to_account_id_ok` / `_err` | covered |
| `random_seed` | 1 | 0 | C | pop id; `payBaseH base`; `regSetH id ctx.randomSeed` | as above, `d = randomSeed` (32 bytes) | no | `random_seed_ok` / `_err` | covered |
| `current_contract_code` | 1 | 1 | C′ | pop id; `payBaseH base`; `None` ⇒ `pushRet 0`; `Local h` ⇒ `regSetH id h`; `pushRet 1` | the `Option ByteArray` (`accountContract`), the code bytes, the register id | no | `current_contract_code_none_ok`, `_local_ok`, `_err` | covered |
| `gas` | 1 | 0 | D | pop amount; `burnH (amount · 822756)` — no base charge, no word | nothing beyond the budget; `g_after` is *not* `remaining` | no | `gas_ok` / `_err` | **blocked (`i32` arg)** |
| `validator_stake` | 3 | 0 | — | pop (len, ptr, out); read the account id; `payBaseH validatorStakeBase`; `setU128H out stake` | the validator table entry for the account | no | — | **blocked (`np = 3`)** |

### Notes that matter on the state side

* **`used_gas` and `gas` and `g_after`.**  `callHost` ends with `g := remaining = prepaid − used`,
and `used = burnt + promises`.  For every function that only charges (`payBaseH`), the burn is already
in `remaining` and `g_after` is just the post-charge budget — the standard `HostSeg` restart
(`StepHost.host_seg`).  `gas` is the one member of the family whose burn is *not* a base charge: it
burns `amount · 822756` directly into `gas.burnt`.  That is still consistent with the chip (it returns
whatever `g_after` the state side computed), but the state side must not assume
`g_after = remaining_before_call`.
* **`setU128H` is a memory write, not a word.**  The Shape-B answer has `ar = 0`; the caller sees
  nothing on the operand stack.  The observable effect is 16 little-endian bytes at the popped
  pointer, so the state side's obligation includes the memory range.
* **`regSetH` is not modelled by HOSTQ/HOSTR.**  The bytes it stores go into the register file, not
  onto a host bus.  Covering this family at the *instruction* level does not require modelling the
  register space: the `HostAnswer` is `status = 0`, `ar = 0`, and the state side supplies `d`.
  (`results/pq-wasm-base/README.md` §14.2 lists the register space as a separate slice.)
* **`storage_usage` reads `St.storageUsage`, not `CallCtx.storageUsage`.**  Two fields with the same
  name; the first is the running total the storage ops maintain.
* **`current_contract_code`'s `ar = 1`** is the only Shape-C member with a result word (`0` for
  `AccountContract::None`, `1` for `Local`); the code bytes themselves go into the register.

## 3. Blocked on arity / tag (deliverable d)

Neither is missing from `hostFns`; both are **listed with their exact signature** and rejected by the
checker, so no HOST row is ever built for them (`Chips.ctx_shape_ok`, kernel):

| function | reason | kernel check | what would unblock it |
|---|---|---|---|
| `validator_stake` | `np = 3`; `HOSTQ` has two argument slots (`P0`, `P1`) | `Chips.validator_stake_blocked` | widen `Host.constraints`/`HostO.q` to `np ≤ 3` (or a second `HOSTQ_CONT` row) — **another lane** |
| `gas` | its parameter is `i32`; the row's argument slots are `i64` (`cTag0: pf0·tagP0 − pf0`, and the trace generator asserts `tag = 1`) | `Chips.ctx_shape_ok` (`filter hostChipIdOf isNone = ["gas", "validator_stake"]`) | make the argument tag a real bit (0 = i32, 1 = i64) — **another lane** |

`hostShapeOk` (`np ≤ 2 ∧ ar ≤ 1`) and `hostArgsI64` are the two predicates; `hostChipIdOf` /
`hostChipSig` conjoin them, and `HostCheck.sigOfH` / `hostOf` / `checkModuleH` now use those, so the
two rejected functions never reach a code record.  The `wasmbase-tool prep` output for a module
importing either is `{"eligible":false}` (pinned by the KAT programs `hostctxblocked_gas` and
`hostctxblocked_stake`).

**`Host.constraints` and `Host.properties` are unmodified** — no arity widening here.

## 4. Lean: what is proved (deliverable 2)

`WasmBase/HostCtx.lean` (new, imported by `WasmBase.lean`):

* **the table checks** (§1 above), kernel-only;
* **`HM` primitives**: `bind_run`, `bind_ok`, `bind_err`, `hmGet_run`, `hmSet_run`, `withGas_run`,
  `payBaseH_run`, `pushRet_run`, `popArgs1_run`.  These are the only rewrites the per-function lemmas
  use; there is no `simp` search over the spec.
* **Shape A**: `ctx_base_push_ok`/`_err` are not needed as such — each of the six functions has a
  `*_ok` / `*_err` pair proved by `rw [hostCall.eq_N]` then one `rw` chain.  The statement is
  post-state style: given the base charge's own run (`payBaseH base` from `s` to `s1`), the call
  returns `pushI64 s1 s1.<field>` (or the charge's error).
* **Shape B**: `writeMemH`'s layers (`writeTail`, `writeMemH_unfold`, `writeMemH_ok`,
  `writeMemH_mav`), the common prefix `setU128_prefix_ok`/`_err`, then the four functions.  A
  success is *exactly* `writeMemH (topArg s) (natLE v 16)` from the post-charge state.
* **Shape C**: the common prefix `regSet_prefix_ok`/`_err`, the seven register fillers, and
  `current_contract_code` (the `None`/`Local` split is the only case analysis in the family).
* **Shape D**: `gas_h`, `gas_ok`, `gas_err` — proved for the semantics, with the function marked
  blocked at the checker.

Axioms: every theorem is within `[propext, Classical.choice, Quot.sound]`; the table checks need
`[propext]` or none.  `grep -n 'sorry\|native_decide\|implemented_by' WasmBase/HostCtx.lean` is
empty.

### What is *not* claimed

The lemmas say what the spec's `hostCall` computes once the state side supplies its input.  They do
**not** say the supplied value is the *correct* one (that is the state proof's job: the account on
`MEM`, the receipt's `CallCtx`, the code hash), and they do not model the register file or the
memory-write's effect on the caller's view.  For a context getter that is the whole obligation: a
`HOSTR` word is a free witness the state side fixes, and the Wasm side must not be able to choose it
differently — which is what `HostResp` + the state-side binding give.

## 5. KAT (deliverable 3)

`native/wasm-base/programs/gen.py` gains five programs and the reference interpreter
(`programs/refinterp.py`) gains the harness values (the defaults of `NearSpecV3.Wasm.CallCtx`):

| program | imports | what it pins |
|---|---|---|
| `hostctxword` | `block_index`, `block_timestamp`, `epoch_height`, `storage_usage`, `prepaid_gas`, `used_gas` | all six Shape-A word getters are called and summed (`53`) |
| `hostctxmem` | `account_balance`, `account_locked_balance`, `attached_deposit`, `validator_total_stake` | all four Shape-B getters write 16 bytes at four pointers, read back (`0`) |
| `hostctxreg` | all seven Shape-C register fillers | each is called and produces no word (`7`) |
| `hostctxcode` | `current_contract_code` | `AccountContract::None` ⇒ `0` (`1`) |
| `hostctxblocked_gas` | `gas` | **must be ineligible** (`i32` argument) |
| `hostctxblocked_stake` | `validator_stake` | **must be ineligible** (`np = 3`) |

`run_kat.sh` treats an ineligible program as a pass iff its `.json` says `result: "ineligible"`.

Result:

```
KAT: 83 passed, 0 failed (python ref = Lean spec = Rust trace + AIR pre-check)
```

(77 before this lane + 4 covered programs + 2 blocked programs.)  Every covered program's trace
passes the full constraint and bus pre-check, which means the HOST row, the `HOSTO` oracle, the
cached `HOSTT` table (now 22 rows) and the `HOSTB` wire all balance with the new ids.

**Tamper** (the native suite, extended in `src/main.rs` with two new case families):

```
hostctxword : TAMPER summary 72/72 rejected
hostctxmem  : TAMPER summary 80/80 rejected
hostctxreg  : TAMPER summary 60/60 rejected
hostctxcode : TAMPER summary 68/68 rejected
```

The new cases are the ones this family makes interesting:

* **`HOSTO.q1/q2/q7`** — the request's `hid`, `S` and `np` fields: changing one breaks the `HOSTQ`
  balance with the HOST row.
* **`HOST[row r].hid cur -> alt (same signature)`** — swap the host id to *another id with the same
  `(np, ar)`*.  This is the attack the generic chip must resist: with 14 `np=1` ids in one table, a
  row relabelled `account_balance` → `chain_id` still type-checks against `HOSTT`.  It is rejected
  on the `HOSTQ` bus (the request carries the row's `hid`) and on the `FETCH` bus (the code record
  carries the original).  Covered in all four programs.

A real proof of `hostctxword` verifies end-to-end:

```
PROVE OK steps 26 result Some((1, 53))
STATEMENT code_root 776d0f7f…002e3f code_hash - (V_d: recomputed root matches)
```

Difftest (Lean AIR model vs Rust verifying-key DAG, `wasmBaseHostAir`, 16 random points/table,
nloc = 0, 1, 2): all agree (`10448` constraint values, `7504`/`7536`/`7568` interactions).

## 6. Reproduce

```
HEAVY_MEM=16G taskset -c 8-10,24-25 /data/illia/nearproof-deps/bin/heavy \
  sh -c 'cd research/near-compression/wasm-base-lean && lake build'
# -> Build completed successfully (125 jobs)

cd research/near-compression/native/wasm-base
CARGO_TARGET_DIR=$PWD/target taskset -c 8-10,24-25 cargo build --release
NEARPROOF_PQ_DEPS=/data/illia/nearproof-deps/pq-wasm-base \
  WASMBASE_BIN=$PWD/target/release/nearproof-wasm-base bash run_kat.sh /tmp/katrun_ctx 8 64
# -> KAT: 83 passed, 0 failed

TAMPER: $PWD/target/release/nearproof-wasm-base tamper /tmp/katrun_ctx/airH-1-g0.json \
          /tmp/katrun_ctx/progs/hostctxword.prep.json
make pin-check   # exit 0
```

**Note on the binary.**  `$NEARPROOF_PQ_DEPS/target/release/nearproof-wasm-base` is a *shared* path
and another lane had rebuilt it from a widened HOST chip at the time of this run (`HOST: no col
pf2` panics on this worktree's 2-slot table).  The numbers above are from this worktree's own build
in `native/wasm-base/target/release`, which is what `run_kat.sh` should be pointed at; the source is
unmodified in that respect.

## 7. Axioms

```
#print axioms WasmBase.block_index_ok          -> [propext, Classical.choice, Quot.sound]
#print axioms WasmBase.account_balance_ok      -> [propext, Classical.choice, Quot.sound]
#print axioms WasmBase.chain_id_ok             -> [propext, Classical.choice, Quot.sound]
#print axioms WasmBase.current_contract_code_* -> [propext, Classical.choice, Quot.sound]
#print axioms WasmBase.gas_ok                  -> [propext, Classical.choice, Quot.sound]
#print axioms WasmBase.Chips.hostFns_arity_agrees -> [propext]
#print axioms WasmBase.Chips.hostFns_head_stable  -> (none)
#print axioms WasmBase.Chips.ctx_shape_ok         -> (none)
#print axioms WasmBase.Chips.validator_stake_blocked -> (none)
```
