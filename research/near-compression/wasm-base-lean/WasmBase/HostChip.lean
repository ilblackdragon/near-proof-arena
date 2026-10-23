import WasmBase.Chips
import NearSpecV3.Wasm.HostSigs
/-!
# WasmBase.HostChip — the HOST chip and the host-function table (direct-Wasm PQ base layer)

First slice of README §14.2: a `call` of an imported function is a straight-line instruction whose
signature is taken from a **fixed host table**, bound through a cached trace exactly like FUNC.
Every domain condition is explicit and decidable.

A HOST row (`np ≤ 9`, `ar ≤ 1`):

* consumes `np` values from the operand stack (channel space 0, in argument order);
* sends one request `[ts, hid, S, np, a0lo, a0hi, …, a8lo, a8hi]` (22 fields) on `HOSTQ`;
* receives one response `[ts, st, rlo, rhi, glo, ghi, ar, 0]` on `HOSTR`, where `st = 0` means
  success and `st = 1` means the host aborted (`g := g_after` still applies);
* produces `(1 − st)·ar` result words at the stack base `sb + h − np`;
* moves to `pc + 1` (`st = 0`) or stays at `pc` with `halted = 2` (`st = 1`);
* advances `S` by `fee + hostK`, `hostK` being the host ext cost in regular-op units; `g_after` is
  the budget after the spec's `g := remaining`.

`HOSTQ` / `HOSTR` are answered inside the trace by a witness **oracle** table `HOSTO` (one row per
call), whose rows are exactly the abstract host responses.  The soundness statement is therefore
relative to that oracle: the proof says "if the state side supplies these responses, the spec `run`
takes this host-call step".  Joining with the state proof (README §14.2) replaces `HOSTO` by the
state tables on the same buses.  Keeping the oracle in-trace also makes the native bus pre-check
exact rather than partial.

## Why one wide `HOSTQ` and not one message per argument

README §14.2 sketches "a second message row for more than five words" for `np > 5`; §14.3 of that
document also keeps the whole request on one ordered bus.  Both were evaluated:

* **One message per argument** (`HOSTQ_k`, `k` messages) needs either a second bus per `k` or a
  message index field plus a per-`k` count column, i.e. a *variable-length* wire.  The state side
  would have to reassemble the request, and the HOST chip would need `np` gated interactions with
  `np`-dependent counts (`k < np`), which is a range condition the chip has no comparison for.  The
  join's `HOSTQ` balance would become a per-`(ts, k)` balance.  More rows, more columns, new gadgets.
* **One 22-field message** is a single interaction, a single balance obligation, an exact bus
  pre-check, and no new comparison gadget.  Its cost is LogUp message length only.

The backend's NV envelope is `log_max_message_length = 7`, i.e. `message.len() + 1 ≤ 128` (bus
included; `stark-backend .../keygen/mod.rs:146-151`).  22 + 1 = 23 ≤ 128, so **the wide message fits
with a factor of 5 to spare** and no protocol parameter changes.  Sixteen 16-bit limbs per argument
would still fit; nine arguments with four 16-bit limbs each (`np ≤ 9`) is the chosen shape because it
is exactly the D3α maximum (`promise_then`, `promise_yield_create_with_id`,
`promise_batch_action_add_key_with_function_call`).  The `HOSTR` response keeps its 8 fields.

The HOST table is not appended to `wasmBaseAir`: that would shift every table index of the proved
F1/memory/globals/calls slice.  Host programs use `wasmBaseHostAir`, which appends HOST (22),
HOSTO (23) and the cached HOSTT table (24).
-/
namespace WasmBase
namespace Chips
open Expr

/-- Cross-proof host request / response, and the cached host table.

`HOSTQ`/`HOSTR` are **cross-proof** buses: the state side must use the same ids. They sit above
every shifted classical bus (the port maps classical bus `b` to `128 + b`, and the widest classical
AIR uses bus 75, so the occupied range is 128-203) and above every Wasm bus (0-9): hence 208/209.
`HOSTT` is a Wasm-internal cached table, not a cross-proof bus, and stays in the low range.
See `lane/pq-d3-join:research/near-compression/results/pq-d3-join/BUS-NUMBERING.md`. -/
def busHostQ : Nat := 208
def busHostR : Nat := 209
/-- `HOSTB` (byte strings).  208/209 are taken and the state side's shifted buses occupy 128-203. -/
def busHostB : Nat := 210
def busHostT : Nat := 9

/-! ## The promise / receipt family (PART 2 table extension)

The 23 importable promise functions of PV86 (`NearSpecV3.Wasm.hostSigs`, the `promise_*` family
minus the four real-gated gas-key / global-contract / state-init actions).  Appended **after** the
eight linear-memory/context hosts, so ids `0..7` are unchanged and the cached `HOSTT` table of an
already-checked module is byte-identical for those.

Arity is `(np, ar)`: every one of them has `np ≤ 9` and `ar ≤ 1`, so the widened HOST chip
(`Host.nArgs = 9`) types all of them.  `promise_yield_resume*` push an **i32** (result tag 0), which
is the one place the chip's fixed result tag `1` is too coarse — recorded in
`results/pq-host-promise/DESIGN.md` §3, not fixed here. -/
def promiseFns : List (Nat × String × Nat × Nat) :=
  [(8, "promise_create", 8, 1),
   (9, "promise_then", 9, 1),
   (10, "promise_and", 2, 1),
   (11, "promise_batch_create", 2, 1),
   (12, "promise_batch_then", 3, 1),
   (13, "promise_set_refund_to", 3, 0),
   (14, "promise_batch_action_create_account", 1, 0),
   (15, "promise_batch_action_deploy_contract", 3, 0),
   (16, "promise_batch_action_function_call", 7, 0),
   (17, "promise_batch_action_function_call_weight", 8, 0),
   (18, "promise_batch_action_transfer", 2, 0),
   (19, "promise_batch_action_stake", 4, 0),
   (20, "promise_batch_action_add_key_with_full_access", 4, 0),
   (21, "promise_batch_action_add_key_with_function_call", 9, 0),
   (22, "promise_batch_action_delete_key", 3, 0),
   (23, "promise_batch_action_delete_account", 3, 0),
   (24, "promise_yield_create", 7, 1),
   (25, "promise_yield_create_with_id", 9, 1),
   (26, "promise_yield_resume", 4, 1),
   (27, "promise_yield_resume_with_yield_id", 4, 1),
   (28, "promise_results_count", 0, 1),
   (29, "promise_result", 2, 1),
   (30, "promise_return", 1, 0)]

/-- The linear-memory / context hosts of the first slice (`np ≤ 2`, `ar ≤ 1`).  Their ids are
pinned: they are the entries every already-checked module's cached `HOSTT` table contains. -/
def hostFnsBase : List (Nat × String × Nat × Nat) :=
  [(0, "block_index", 0, 1), (1, "block_timestamp", 0, 1), (2, "epoch_height", 0, 1),
   (3, "storage_usage", 0, 1), (4, "prepaid_gas", 0, 1), (5, "used_gas", 0, 1),
   (6, "register_len", 1, 1), (7, "panic", 0, 0)]

/-- Fixed host table `(id, name, #params, #results)`: the base entries (`id 0..7`, pinned), the 23
promise/receipt functions (`id 8..30`) and the log/panic + register/return functions (`id 45..52`).
With `Host.nArgs = 9` the wide HOST chip types every entry; `ar ≤ 1` throughout.

The D3α log/panic and register/return functions (`lane/pq-host-logreg`).  Ids are fresh, so
every previously assigned id stays stable.  `abort` (np = 4) and `write_register` (np = 3) are
admitted by the widened chip (`Host.nArgs = 9`). -/
def hostLogFns : List (Nat × String × Nat × Nat) :=
  [(45, "log_utf8", 2, 0), (46, "log_utf16", 2, 0), (47, "panic_utf8", 2, 0),
   (48, "input", 1, 0), (49, "read_register", 2, 0), (50, "value_return", 2, 0),
   (51, "abort", 4, 0), (52, "write_register", 3, 0)]

/-- The 19 D3α context / state-read hosts (`lane/pq-host-ctx`), ids 31..44. -/
def hostCtxFns : List (Nat × String × Nat × Nat) :=
  [(31, "current_account_id", 1, 0), (32, "chain_id", 1, 0),
   (33, "signer_account_id", 1, 0), (34, "signer_account_pk", 1, 0),
   (35, "predecessor_account_id", 1, 0), (36, "refund_to_account_id", 1, 0),
   (37, "account_balance", 1, 0), (38, "account_locked_balance", 1, 0),
   (39, "attached_deposit", 1, 0), (40, "random_seed", 1, 0),
   (41, "current_contract_code", 1, 1), (42, "gas", 1, 0),
   (43, "validator_total_stake", 1, 0), (44, "validator_stake", 3, 0)]

/-- The four D3α hash host functions (`lane/pq-hash-air`), ids 53..56.  All are `(3, 0)` in the
PV86 linker table (`HostSigs.lean:33-38`): `sha256(len, ptr, reg)` etc., all `i64` parameters and
no result word — the answer goes into a register.  Appended **last**, so every previously assigned
id stays stable. -/
def hostHashFns : List (Nat × String × Nat × Nat) :=
  [(53, "sha256", 3, 0), (54, "keccak256", 3, 0), (55, "keccak512", 3, 0), (56, "ripemd160", 3, 0)]

/-- The four D3α storage host functions.  Ids 57..60 are **fresh**, after the hash block, so every
previously assigned id stays stable and no cached `HOSTT` moves.  (This deliberately does not adopt
`tools/host-fns/canonical.txt`, which numbers storage 53..59 and therefore collides with the hash
ids 53..56 — see `docs/logs/pq-d3-chain-gap-2026-10-21.md` §2.)

`storage_iter_prefix` / `_range` / `_next` are omitted on purpose: they are **out of domain** in
D3α (they always abort, `Host.lean`), so no run of them can move storage and `pq-host-storage`
proved that.  The four here are the ones that read and write trie values. -/
def hostStorageFns : List (Nat × String × Nat × Nat) :=
  [(57, "storage_read", 3, 1), (58, "storage_write", 5, 1),
   (59, "storage_has_key", 2, 1), (60, "storage_remove", 3, 1)]

def hostFns : List (Nat × String × Nat × Nat) :=
  hostFnsBase ++ promiseFns ++ hostCtxFns ++ hostLogFns ++ hostHashFns ++ hostStorageFns

/-- The hash ids in the fixed table. -/
def hostHashIds : List Nat := [53, 54, 55, 56]

/-- The storage ids in the fixed table. -/
def hostStorageIds : List Nat := [57, 58, 59, 60]

/-- The HOST row accepts up to 9 arguments and at most one result. -/
def hostShapeOk (np ar : Nat) : Bool := np ≤ 9 && ar ≤ 1

/-- The HOST row's argument slots are `i64`-tagged, so a function with an `i32` parameter cannot be
called (`gas`, `abort`); widening the tag is a later lane's change. -/
def hostArgsI64 (name : String) : Bool :=
  match NearSpecV3.Wasm.hostSigs.find? (·.1 = name) with
  | some (_, ft) => ft.params.all (· == .i64)
  | none => false

/-- The PV86 linker signature of a host function name (`NearSpecV3.Wasm.hostSigs`), or `none` if it
is not an importable host function.  The arity/type checks compare the fixed HOST table against
this, so a table entry that disagrees with the spec fails the build. -/
def hostSig? (name : String) : Option NearSpecV3.Wasm.FuncType :=
  (NearSpecV3.Wasm.hostSigs.find? (fun x => x.1 = name)).map (·.2)

/-- Host id of an imported function name (`none`: not in the fixed table ⇒ outside the domain). -/
def hostIdOf (name : String) : Option Nat :=
  (hostFns.find? (fun x => x.2.1 = name)).map (·.1)

/-- Signature `(np, ar)` of a host id. -/
def hostSig (id : Nat) : Option (Nat × Nat) :=
  (hostFns.find? (fun x => x.1 = id)).map fun x => (x.2.2.1, x.2.2.2)

/-- Host ids whose call carries a **byte payload** on `HOSTB` (`log_utf8`, `log_utf16`,
`panic_utf8`, `value_return`).  `input`, `read_register` and `register_len` are the register-space
functions (space 6); `panic` has no payload. -/
def hostByteIds : List Nat := [45, 46, 47, 50]

theorem hostByteIds_mem : ∀ i ∈ hostByteIds, (hostSig i).isSome := by decide

/-- Host id of `name` **if its signature fits the HOST row**: `np ≤ 9`, `ar ≤ 1`, and every
parameter is `i64`.  This is what the checker uses. -/
def hostChipIdOf (name : String) : Option Nat :=
  (hostFns.find? (fun x => x.2.1 = name && hostShapeOk x.2.2.1 x.2.2.2 && hostArgsI64 name)).map (·.1)

/-- Signature of a host id, restricted to the shapes the HOST chip carries. -/
def hostChipSig (id : Nat) : Option (Nat × Nat) :=
  (hostSig id).bind fun (np, ar) =>
    if hostShapeOk np ar then
      (match hostFns.find? (·.1 = id) with
       | some x => if hostArgsI64 x.2.1 then some (np, ar) else none
       | none => none)
    else none

def hostRow (id np ar : Nat) : List Nat := [id, np, ar, 0, 0, 0, 0, 0]

/-- FETCH opcode of an import call (not a Wasm opcode of the F1 family). -/
def opHost : Nat := 0x1FF

namespace Host
/-- The argument window width.  `np ≤ 9` covers every D3α host function including `promise_then`,
`promise_yield_create_with_id` and `promise_batch_action_add_key_with_function_call`. -/
def nArgs : Nat := 9
/-- Index of the first per-argument stack receive in `inters`: the 6 header interactions
(stateIn, stateOut, fetch, hostT, hostQ, hostR), the 4 `ga` and 4 `rb` range checks, and the
`4·nArgs` argument-limb range checks.  Per argument `inters` then holds (`stkRecv j`, two `r16`s of
`timeChk j`), i.e. **stride 3**; the single `stkSend` follows the last argument.  Deriving these
keeps `Main/HostChipBits` independent of `nArgs`. -/
def chBase : Nat := 6 + 4 + 4 + 4 * nArgs
/-- Stride between consecutive arguments' `stkRecv` in `inters`. -/
def chStride : Nat := 3
/-- Index of the `stkSend` (`nres`) interaction. -/
def sendIdx : Nat := chBase + chStride * nArgs

/-- The argument indices `0 … nArgs − 1`. -/
def argRange : List Nat := List.range nArgs

def act : Nat := 5
def hid : Nat := 6
def np : Nat := 7
def ar : Nat := 8
/-- response status: 0 = success, 1 = abort -/
def st : Nat := 9
def nres : Nat := 10
def ga : Nat := 11     -- g_after limbs 11..14
def rb : Nat := 15     -- result limbs 15..18
def pf (j : Nat) : Nat := 19 + j              -- 19..27: argument j present (j < nArgs)
def tagP (j : Nat) : Nat := 28 + 7 * j
def P (j : Nat) : Nat := 29 + 7 * j           -- 4 limbs
def tP (j : Nat) : Nat := 33 + 7 * j
def hP (j : Nat) : Nat := 34 + 7 * j
def kSb : Nat := 91
def kCid : Nat := 92

def argCols (j : Nat) : List String :=
  [s!"tagP{j}", s!"P{j}_0", s!"P{j}_1", s!"P{j}_2", s!"P{j}_3", s!"tP{j}", s!"hP{j}"]

def cols : List String := headerCols ++
  ["act", "hid", "np", "ar", "st", "nres", "ga0", "ga1", "ga2", "ga3",
   "r0", "r1", "r2", "r3"] ++
  (argRange.map fun j => s!"pf{j}") ++ (argRange.flatMap argCols) ++ frameCols

def sbNew : Expr := v kSb + v cH - v np
def aLo (j : Nat) : Expr := v (P j) + 65536 * v (P j + 1)
def aHi (j : Nat) : Expr := v (P j + 2) + 65536 * v (P j + 3)
def gLo : Expr := v ga + 65536 * v (ga + 1)
def gHi : Expr := v (ga + 2) + 65536 * v (ga + 3)
def rLo : Expr := v rb + 65536 * v (rb + 1)
def rHi : Expr := v (rb + 2) + 65536 * v (rb + 3)
def ok : Expr := 1 - v st

/-- The left fold of a list of expressions (so that `cNp` / message shapes are spelled
uniformly for any `nArgs`). -/
def sumE (l : List Nat) (f : Nat → Expr) : Expr := (l.map f).foldl (· + ·) 0
/-- `np = Σ_j pf j`. -/
def pfSum : Expr := sumE argRange (fun j => v (pf j))

/-! Constraints.  `S` advances by the instruction `fee` only: host ext costs are burnt by the state
side (`sync`) and returned as `g_after`, not counted in instruction-gas units.  Each constraint is
named so its membership is `by simp`. -/
def cAct : Expr := bool (v act)
def cSt : Expr := bool (v st)
def cP (j : Nat) : Expr := bool (v (pf j))
def cP0 : Expr := cP 0
def cP1 : Expr := cP 1
/-- `pf j` is prefix-closed: `pf (j+1) = pf j · pf (j+1)` (with `pf j` a bit:
`pf (j+1)·(1−pf j) = 0`).  This is what makes `np = Σ pf j` the number of *leading* arguments and
therefore what makes the stack slots `sb + h − np + j` line up with the stack messages. -/
def cPOrder (j : Nat) : Expr := v (pf (j + 1)) - v (pf j) * v (pf (j + 1))
/-- The historical two-argument name (`pf1 = pf0·pf1`). -/
def cP1P0 : Expr := cPOrder 0
def cNp : Expr := v np - pfSum
def cAr : Expr := bool (v ar)
/-- `nres = (1−st)·ar`. -/
def cNres : Expr := v nres - v ar + v st * v ar
def cGLo : Expr := gLo - (v ga + 65536 * v (ga + 1))
def cGHi : Expr := gHi - (v (ga + 2) + 65536 * v (ga + 3))
def cRLo : Expr := rLo - (v rb + 65536 * v (rb + 1))
def cRHi : Expr := rHi - (v (rb + 2) + 65536 * v (rb + 3))
/-- The argument padding: an absent argument has zero tag and zero limbs; a present one has tag 1. -/
def cPad (j : Nat) : Expr := v (tagP j) - v (pf j) * v (tagP j)
def cTag (j : Nat) : Expr := v (pf j) * v (tagP j) - v (pf j)
def cPad0 : Expr := cPad 0
def cPad1 : Expr := cPad 1
def cTag0 : Expr := cTag 0
def cTag1 : Expr := cTag 1

def cPadL (j : Nat) : List Expr :=
  (List.range 4).map fun i => v (P j + i) - v (pf j) * v (P j + i)

/-- An inactive row emits nothing: the CH channels are gated by `pf j` / `nres`, so without these
links the `ChipFacts.inactive` premise fails (see `results/pq-host-gas/RESULTS.md` §3.3).  These
turn `pf j` and `nres` off on inactive rows, which is what makes the bus decomposition in
`Main/ExecHost.lean` follow from `Holds` alone. -/
def cActPf (j : Nat) : Expr := (1 - v act) * v (pf j)
def cActNres : Expr := (1 - v act) * v nres

/-- The constraints, split into named groups so that membership is one `List.mem_append` step each. -/
def cBase : List Expr := [cAct, cSt, cAr, cNres, cGLo, cGHi, cRLo, cRHi, cNp]
def cFlags : List Expr := argRange.map cP
def cOrder : List Expr := argRange.filterMap fun j => if j + 1 < nArgs then some (cPOrder j) else none
def cPads : List Expr := argRange.flatMap fun j => [cPad j, cTag j] ++ cPadL j
def cGates : List Expr := argRange.map cActPf

def constraints : List Expr := cBase ++ cFlags ++ cOrder ++ cPads ++ cGates ++ [cActNres]

/-- The HOSTQ request message: `[ts, hid, S, np]` then `(aLo j, aHi j)` for every argument. -/
def qMsg : List Expr := [v cTs, v hid, v cS, v np] ++ (argRange.flatMap fun j => [aLo j, aHi j])

def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) (v act),
   stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee) (2 * v st) (v kSb) (v kCid) (v act),
   fetch (v cPc) (Expr.c opHost) (v cH) (v cFee) [v hid, v np, v ar, 0] (v act),
   ⟨busHostT, true, v act, [v hid, v np, v ar, 0, 0, 0, 0, 0]⟩,
   ⟨busHostQ, true, v act, qMsg⟩,
   ⟨busHostR, false, v act, [v cTs, v st, rLo, rHi, gLo, gHi, v ar, 0]⟩] ++
  (List.range 4).map (fun i => r16 (v (ga + i)) (v act)) ++
  (List.range 4).map (fun i => r16 (v (rb + i)) (v act)) ++
  (argRange.flatMap fun j => (List.range 4).map (fun i => r16 (v (P j + i)) (v act))) ++
  (argRange.flatMap fun j =>
    [stkRecv (sbNew + Expr.c j) (v (tagP j)) (limbsOf (P j)) (v (tP j)) (v (pf j))] ++
    timeChk (v cTs) (v (tP j)) (v (hP j)) (v (pf j))) ++
  [stkSend sbNew 1 (limbsOf rb) (v cTs) (v nres)]

def table : Table := ⟨"HOST", cols, constraints, inters⟩
end Host

/-- Every entry of the fixed host table fits the widened HOST chip: `np ≤ Host.nArgs`, `ar ≤ 1`,
and the HOSTQ request stays inside the backend's NV envelope (`log_max_message_length = 7`, i.e.
`message.len() + 1 ≤ 128`, bus included).  Kernel-checked, so a future table edit that breaks the
window fails the build rather than the prover. -/
theorem hostFns_shape :
    hostFns.all (fun x => x.2.2.1 ≤ Host.nArgs && x.2.2.2 ≤ 1) = true := by
  simp only [hostFns, Host.nArgs]
  decide

/-- The HOSTQ message is 23 fields including the bus, so it fits NV's `log_max_message_length = 7`
(128 fields).  `Host.qMsg.length = 22`. -/
theorem hostQ_len : Host.qMsg.length + 1 ≤ 128 := by decide


namespace HostTab
def mult : Nat := 8
def cachedWidth : Nat := 8
def table : Table := ⟨"HOSTT", ["id", "np", "ar", "z0", "z1", "z2", "z3", "z4", "mult"], [],
  [⟨busHostT, false, v mult, (List.range 8).map v⟩]⟩
end HostTab

/-! The witness oracle of the host responses (one row per host call): it absorbs the HOSTQ request
and emits the HOSTR response; on the joined proof the state side plays this role.

The request is copied verbatim from the HOST row (`Host.qMsg`), so the oracle must hold all
`Host.qMsg.length = 22` fields.  `q i` for `i < 22` is the request; `st`, `rb`, `ga`, `ar` and
`mult` follow.  The response reuses `q 0` (`ts`) exactly as before. -/
namespace HostO
/-- The request length, *derived* from the HOST chip's message so the two can never drift. -/
def qLen : Nat := Host.qMsg.length
def q (i : Nat) : Nat := i        -- request columns 0..21
def st : Nat := 22
def rb : Nat := 23                -- response word limbs 23..26
def ga : Nat := 27                -- g_after limbs 27..30
def ar : Nat := 31
def mult : Nat := 32
def cols : List String := (List.range qLen).map (fun i => s!"q{i}") ++ ["st",
  "r0", "r1", "r2", "r3", "g0", "g1", "g2", "g3", "ar", "mult"]
def gLo : Expr := v ga + 65536 * v (ga + 1)
def gHi : Expr := v (ga + 2) + 65536 * v (ga + 3)
def rLo : Expr := v rb + 65536 * v (rb + 1)
def rHi : Expr := v (rb + 2) + 65536 * v (rb + 3)
def qMsg : List Expr := (List.range qLen).map fun i => v (q i)
/-- The oracle's two interactions, named so that an extension table (`WasmBase.Chips.HostOH`) can
keep them and append its own.  `table` stays spelled out exactly as before, so every proof that
unfolds it is unaffected. -/
def inters : List Inter := [
  ⟨busHostQ, false, v mult, qMsg⟩,
  ⟨busHostR, true, v mult, [v (q 0), v st, rLo, rHi, gLo, gHi, v ar, 0]⟩]
def table : Table := ⟨"HOSTO", cols, [], [
  ⟨busHostQ, false, v mult, qMsg⟩,
  ⟨busHostR, true, v mult, [v (q 0), v st, rLo, rHi, gLo, gHi, v ar, 0]⟩]⟩

theorem table_inters : table.inters = inters := rfl
end HostO

/-! ## HOSTB: the byte-string wire of a host call

One row per byte moved by a host call, message `[ts, dir, pos, byte]`: `dir = 0` is a request
byte (Wasm → state), `dir = 1` a response byte (state → Wasm).  Rows are **groups** delimited by
the break flag `f = 1` on the first row of a group; inside a group `ts` and `dir` are constant and
`pos` increases by exactly one per row (so a `(ts, dir)` group is a contiguous run with distinct,
consecutive positions).
* `cFirst` — row 0 is a group start, so the cyclic `next` of the last row is a start and the
  continuation constraints do not fire across the wrap;
* `cLast` — the last row is a group start too: the table begins and ends at a group break (the
  final-row check, the analogue of RANGE16's endpoint pin).  The trace generator pads to a power
  of two with group-start rows, so this is always satisfiable;
* `act` is row activity (0 on padding rows); padding rows are group starts with `act = 0` and
  `byte = 0`, so their interactions have count 0 and are invisible on the bus;
* `byte < 256` is a `BYTE` kind-0 lookup with count `act`, as in every other byte-carrying chip.

All constraints have degree ≤ 2.

## The MEMIO link (`(ptr, len)` → linear memory)

The columns `ptrLo, ptrHi` commit the buffer base `ptr = ptrLo + 2^16·ptrHi` (group-constant,
`ptr < 2^27`).  A **request** byte (`dir = 0`, `reg = 0`) is read out of linear memory, so the row
carries the memory message in both directions (count `memCnt = act·(1−dir)·(1−reg)`):

```
chRecv 3 (ptr + pos) 0 [byte,0,0,0] mtp     -- the live memory byte, at its producer time
chSend 3 (ptr + pos) 0 [byte,0,0,0] ts      -- the same byte, re-timed to this call
timeChk ts mtp hp                           -- mtp < ts
```

`mtp` is the byte's producer time, so the two messages **differ** and the pair is not a same-time
self-cancellation: the `recv` can only balance against a memory message some other table produced, so
it genuinely asserts "memory[ptr + pos] = byte at `mtp`", and the `send` re-times it to `ts` — exactly
the LOAD shape of `Chips.Load`.  `mtp < ts` is what makes the assertion non-vacuous (a same-time pair
cancels for every count, `Main/MemIO.ch_pair_vacuous`).

What is still *not* constrained: the byte values of response payloads (`dir = 1`) and the
register-fill half (`reg = 1`) are state-side data, not memory reads; and `ptr + len ≤ memBytes` is a
statement-level bound (`MemIO.BufOK`), not a polynomial constraint, since `ptr, len < 2^27/2^16` only
bound each of them separately. -/
namespace HostB
def ts : Nat := 0
def dir : Nat := 1
def pos : Nat := 2
def bv : Nat := 3
def blen : Nat := 4
def hid : Nat := 5
def gap : Nat := 6
def act : Nat := 7
def f : Nat := 8
/-- `reg = 1`: this byte **also** fills a register.  `HOSTB` then owns only the state-side half of
the message; the Wasm-side half (receiving it into channel space 6) is `REG` (`WasmBase.RegChip`).
Such a byte is always a *response* byte (`dir = 1`, state → Wasm) — `cRegDir` below.  With
`reg = 0` the byte is a plain host payload and `HOSTB` keeps both halves (a self-permutation). -/
def reg : Nat := 9
/-- The buffer base, as two 16-bit limbs (`ptrLo + 2^16 · ptrHi`).  Group-constant.  This is the
`ptr` of the host call's `(ptr, len)` memory range: the MEMIO link sends and receives the memory
byte at `ptr + pos` on channel space 3, so the bytes on `HOSTB` *are* the linear-memory bytes. -/
def ptrLo : Nat := 10
def ptrHi : Nat := 11
/-- The producer time of the memory byte this row touches (`mtp < ts`, checked by `timeChk`).  A
request byte consumes the live memory message at `mtp` and re-produces it, unchanged, at `ts` —
the same LOAD shape every memory access uses, which is what makes the link non-vacuous. -/
def mtp : Nat := 12
/-- The high limb of `ts − mtp − 1` (the `timeChk` witness). -/
def hp : Nat := 13
/-- `len` is the group's byte count, committed on every row of the group (so it is a function of
`ts` rather than a free witness per row), and `hid` ties the group to the host call it belongs to.
Together they are the HOSTB <-> HOSTQ link: the same `(ts, hid)` pair appears on HOSTQ, so a byte
group cannot be spliced onto a different call.  The `(ptr, len)` range is the buffer
`[ptr, ptr + len)`: `ptr` is committed as two limbs (group-constant, `ptr < 2^27`) and every
request byte carries the space-3 message of `ptr + pos` (see `memCnt`/`memAddr` below). -/
def cols : List String := ["ts", "dir", "pos", "byte", "len", "hid", "gap", "act", "f", "reg",
  "ptrLo", "ptrHi", "mtp", "hp"]

def cAct : Expr := bool (v act)
def cF : Expr := bool (v f)
def cDir : Expr := bool (v dir)
def cReg : Expr := bool (v reg)
/-- Only a response byte can fill a register (a request byte is Wasm → state). -/
def cRegDir : Expr := v reg * (1 - v dir)
def cFirst : Expr := .first * (1 - v f)
def cLast : Expr := .last * (1 - v f)
/-- A group continues with the same `ts`. -/
def cTs : Expr := (1 - nv f) * (nv ts - v ts)
/-- A group continues with the same `dir`. -/
def cDirG : Expr := (1 - nv f) * (nv dir - v dir)
/-- A group continues at the next position (strictly increasing, consecutively). -/
def cPos : Expr := (1 - nv f) * (nv pos - v pos - 1)
/-- A byte position is inside its group's length: `pos < len`.

`pos < len` is not expressible as a polynomial without a comparison gadget, so it is delegated to
the same 16-bit comparison the chips use (`cmp`), exposed here as a lookup into the pre-existing
`RANGE16` table with the gap `len - pos - 1`: a 16-bit witness `g` with `pos + g + 1 = len` proves
`pos < len` for every `pos, len < 2^16`, and a `RANGE16` membership of `g` pins `g < 2^16`.  The
domain therefore requires `len < 2^16`, which is stated as a public bound. -/
def cPosLtLen : Expr := v act * (v blen - v pos - 1 - v gap)
/-- `len` is the same on every row of a group. -/
def cLenConst : Expr := (1 - nv f) * (nv blen - v blen)
/-- `hid` is the same on every row of a group. -/
def cHidConst : Expr := (1 - nv f) * (nv hid - v hid)
/-- `ptr` is the same on every row of a group (both limbs), so the buffer address is a function of
the group rather than a free witness per byte. -/
def cPtrLoConst : Expr := (1 - nv f) * (nv ptrLo - v ptrLo)
def cPtrHiConst : Expr := (1 - nv f) * (nv ptrHi - v ptrHi)

def constraints : List Expr :=
  [cAct, cF, cDir, cReg, cRegDir, cFirst, cLast, cTs, cDirG, cPos, cPosLtLen, cLenConst, cHidConst,
   cPtrLoConst, cPtrHiConst]

def msg : List Expr := [v ts, v hid, v dir, v pos, v bv]
/-- The space-3 address of this row's byte: `ptr + pos`.  Exact in the naturals: `ptr < 2^27` and
`pos < 2^16` (both R16-checked) keep the sum below the field modulus. -/
def memAddr : Expr := v ptrLo + 65536 * v ptrHi + v pos
/-- A **request** byte (`dir = 0`, `reg = 0`) is read from linear memory, so it carries the memory
message in both directions: it consumes the live message at the producer time `mtp` and produces it
again at `ts`.  This is the LOAD shape of `Chips.Load` — crucially `mtp < ts`, so the pair is not a
same-time self-cancellation (`ch_raw_host`'s memory block then absorbs the re-timing). -/
def memCnt : Expr := v act * (1 - v dir) * (1 - v reg)
/-- The memory message of this row: byte `bv` at `memAddr`, tag 0 (a plain byte, as `encB`). -/
def memMsg : List Expr := [Expr.c 3, memAddr, 0, v bv, 0, 0, 0]
/-- **The register link.**  When `reg = 1` the byte fills a register and the Wasm-side half of
the wire lives in `REG` (`WasmBase.RegChip`): the fill (`dir = 1`) is *sent* here and *received* by
`REG` (whose `cDirRd` makes a fill byte a response byte).  One
register byte is Wasm-side only, so it never travels back).  When `reg = 0` the byte is a plain
payload and this table carries both halves (the self-permutation of the minimum slice), exactly as
`HOSTO` stands in for the state side on `HOSTQ`/`HOSTR`.  A joined proof keeps the Wasm-side halves
and replaces the others by the state tables on bus 210.  All counts are bits. -/
def inters : List Inter :=
  [⟨busHostB, true, v act * (1 - v dir) * (1 - v reg), msg⟩,
   ⟨busHostB, false, v act * (1 - v dir) * (1 - v reg), msg⟩,
   ⟨busHostB, true, v act * v dir * (1 - v reg), msg⟩,
   ⟨busHostB, false, v act * v dir * (1 - v reg), msg⟩,
   -- the state-side half of a register-filling byte (`cRegDir` forces `dir = 1`)
   ⟨busHostB, true, v act * v reg, msg⟩,
   -- the MEMIO link: a request byte consumes the live memory byte at `ptr + pos` (producer time
   -- `mtp`) and re-produces it at `ts`.  `mtp < ts`, so the two messages differ and the pair is
   -- NOT the vacuous same-time recv/send that cancels identically (see `Main/MemIO.lean`).
   chRecv 3 memAddr 0 [v bv, 0, 0, 0] (v mtp) memCnt,
   chSend 3 memAddr 0 [v bv, 0, 0, 0] (v ts) memCnt] ++
  timeChk (v ts) (v mtp) (v hp) memCnt ++
  [-- a register-filling byte (`reg = 1`) is looked up by `REG`, which owns the register wire
   byteQ 0 (v bv) 0 0 (v act * (1 - v reg)),
   r16 (v gap) (v act * (1 - v reg)),
   -- `pos` and `len` must be 16-bit: without this, `cPosLtLen` (`pos + gap + 1 = len`) is
   -- satisfiable with `pos + 1 + gap = len + P` (i.e. `pos = P − 1`, `len = 5`, `gap = 4`), so
   -- `pos < len` — the only bound tying a byte's position to its group's length — would be FALSE.
   -- The same hole forced `r16 pos` in `REG`; this is the predicted HOSTB counterpart
   -- (`hostb_pos_lt_len_needs_r16`, `Main/HostChipFacts`).
   r16 (v pos) (v act * (1 - v reg)),
   r16 (v blen) (v act * (1 - v reg)),
   -- `ptr` is a 27-bit address: `ptrLo < 2^16` and `32·ptrHi < 2^16` (so `ptrHi < 2^11`).  Without
   -- these, `memAddr = ptr + pos` would be a free field element and could alias any address.
   r16 (v ptrLo) (v act * (1 - v reg)),
   r16 (32 * v ptrHi) (v act * (1 - v reg))]

def table : Table := ⟨"HOSTB", cols, constraints, inters⟩
end HostB

/-- **Every host id is distinct.**  This is the invariant that the `canonical.txt` table broke: it
numbers `storage_write` 59, colliding with the hash block's 53..56 range when read literally.  The
table here allocates storage at fresh ids 57..60 and this theorem states, once, that no two entries
share an id — so a future insertion cannot silently collide. -/
theorem hostFns_ids_nodup : (hostFns.map (·.1)).Nodup := by decide +kernel

/-- The storage ids and signatures, pinned (the four D3α functions that read/write trie values). -/
theorem hostStorage_sigs :
    hostSig 57 = some (3, 1) ∧ hostSig 58 = some (5, 1) ∧
    hostSig 59 = some (2, 1) ∧ hostSig 60 = some (3, 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The four storage functions are reachable by name at exactly those ids. -/
theorem hostStorage_names :
    (hostFns.find? (·.2.1 = "storage_read")).map (·.1) = some 57 ∧
    (hostFns.find? (·.2.1 = "storage_write")).map (·.1) = some 58 ∧
    (hostFns.find? (·.2.1 = "storage_has_key")).map (·.1) = some 59 ∧
    (hostFns.find? (·.2.1 = "storage_remove")).map (·.1) = some 60 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The hash block keeps its ids, so every cached `HOSTT` that names a hash function still resolves. -/
theorem hostHash_ids_stable : hostHashIds = [53, 54, 55, 56] := by decide +kernel

end Chips

/-- The direct-Wasm base AIR **with host calls**: the proved F1/memory/globals/calls tables plus
HOST (22), the response oracle HOSTO (23), the cached HOSTT table (24) and the byte wire HOSTB
(25). -/
def wasmBaseHostAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseAir nloc ngl).tables ++
      [Chips.Host.table, Chips.HostO.table, Chips.HostTab.table, Chips.HostB.table]
    numPub := (wasmBaseAir nloc ngl).numPub }

/-- The base AIR **with `if`**: the 22 base tables plus the `IF` table (22).  A separate AIR rather
than an extra table in `wasmBaseAir`, for the same reason `ChiAir`/`ShaAir` are exported separately:
every existing proof, table index and cached export keeps its meaning, so nothing has to be re-proved.
The host AIR keeps its own indices too. -/
def wasmBaseIfAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseAir nloc ngl).tables ++ [Chips.IfC.table]
    numPub := (wasmBaseAir nloc ngl).numPub }

/-- The host AIR **with `if`**: `wasmBaseHostAir` plus `IF` at index 26.  Host proofs keep their
table 22–25 indices unchanged. -/
def wasmBaseIfHostAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseHostAir nloc ngl).tables ++ [Chips.IfC.table]
    numPub := (wasmBaseHostAir nloc ngl).numPub }

end WasmBase
