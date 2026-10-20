import WasmBase.Main.Host
import WasmBase.Mem
import NearSpecV3.Wasm.HostSigs
/-!
# WasmBase.HostCtx — the D3α context / state-read host family (lane `pq-host-ctx`)

`results/pq-host-ctx/README.md` documents the 19 context / state-read host functions of D3α
(`account_balance`, `block_index`, `chain_id`, `validator_total_stake`, …).  The HOST chip
(`WasmBase/HostChip.lean`) is **generic**: it never names a function — it takes `(hid, np, ar)` from
the fixed table `Chips.hostFns` and passes the arguments/results through `HOSTQ`/`HOSTR` to the
abstract in-trace oracle `HOSTO`.  So covering a family is *not* a new AIR per function; it is

1. its functions present in `hostFns` with the exact arity of `NearSpecV3.Wasm.hostSigs`, and
2. a statement of what the **state side** has to supply so the abstract `HostAnswer` on `HOSTR` is
   the answer the spec's `hostCall` produces.

This file is (2), in the form the join consumes, plus the kernel checks of (1).

## What the state side has to supply, per shape

Every family member has one of five shapes.  In each, `HOSTR` carries `(status, ar, word, g_after)`
and the row's `stkSend` carries `word`; the Wasm side never learns *how* it was produced.

| shape | functions | spec `hostCall` | state side supplies | AIR? |
|---|---|---|---|---|
| A: `np=0, ar=1` word getter | `block_index`, `block_timestamp`, `epoch_height`, `storage_usage`, `prepaid_gas`, `used_gas` | `payBaseH C.base`; `pushRet field` | the field value (`word`) and the base charge's success | none |
| B: `np=1, ar=0` `u128` getter | `account_balance`, `account_locked_balance`, `attached_deposit`, `validator_total_stake` | `popArgs 1`; `payBaseH C.base`; `setU128H ptr v` | the value `v` **and** the memory range `ptr + 16 ≤ memBytes` | none |
| C: `np=1, ar=0` register filler | `current_account_id`, `chain_id`, `signer_account_id`, `signer_account_pk`, `predecessor_account_id`, `refund_to_account_id`, `random_seed` | `popArgs 1`; `payBaseH C.base`; `regSetH id d` | the byte string `d`, the register id, and `regSetH`'s domain | none |
| C′: `np=1, ar=1` | `current_contract_code` | as C, then `pushRet 0/1` | as C plus `AccountContract::None`/`Local` | none |
| D: `np=1, ar=0` burn | `gas` | `popArgs 1`; `burnH (n · 822756)` | nothing beyond the budget it already owns | none |

None of these needs a new AIR constraint: the chip already carries `status`, `ar`, `word`
(`rb` limbs), `g_after` (`ga` limbs) and the `np` argument words, and `Main/Host.lean`'s
`HostOK`/`HostResp` bind them to the abstract answer.  What was missing for the family is the
**reduction** below: it says the spec's host call is exactly the `HM` program whose single payload
is the value the state side supplies.

`gas` is the one member whose `g_after` is *not* just `remaining`: it burns without a base charge.

## Method

Everything is a rewrite chain over four `HM` primitives (`bind`, `get`, `withGas`, `popArgs`) and the
spec's own equation lemmas `hostCall.eq_N`; there is no `simp` search and no assumption about the
*value* of a context field.  No axiom beyond `[propext, Classical.choice, Quot.sound]`.
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The table (deliverable 1)

`hostFns` lives in `WasmBase/HostChip.lean`; these are the kernel checks on it. -/

namespace Chips

/-- The 19 D3α context / state-read functions this lane covers. -/
def ctxNames : List String :=
  ["account_balance", "account_locked_balance", "attached_deposit", "block_index",
   "block_timestamp", "chain_id", "current_account_id", "current_contract_code", "epoch_height",
   "gas", "predecessor_account_id", "prepaid_gas", "random_seed", "refund_to_account_id",
   "signer_account_id", "signer_account_pk", "used_gas", "validator_stake",
   "validator_total_stake"]

theorem ctxNames_len : ctxNames.length = 19 := by decide +kernel

/-- Every family member is in the fixed HOST table. -/
theorem ctx_all_listed : ctxNames.all (fun n => (hostIdOf n).isSome) = true := by decide +kernel

/-- **Arity agreement.**  Every `hostFns` entry has exactly the `(np, ar)` that
`NearSpecV3.Wasm.hostSigs` — the PV86 linker table — gives its name.  The chip reads `np`/`ar` from
this table, so this check makes the signature a HOST row enforces the spec's signature. -/
theorem hostFns_arity_agrees :
    hostFns.all (fun x => decide ((hostSig? x.2.1).map (fun t => (t.params.size, t.results.size)) =
      some (x.2.2.1, x.2.2.2))) = true := by decide +kernel

/-- The parameter/result **types** agree too (`i64` everywhere except `gas`'s `i32` parameter). -/
theorem hostFns_types :
    hostFns.all (fun x =>
      (x.2.1 = "gas" && decide (hostSig? x.2.1 = some { params := #[.i32], results := #[] })) ||
      decide (hostSig? x.2.1 = some { params := (List.replicate x.2.2.1 .i64).toArray,
                                      results := (List.replicate x.2.2.2 .i64).toArray })) = true := by
  decide +kernel

/-- The existing ids `0..7` are unchanged (the first slice's table stays stable). -/
theorem hostFns_head_stable :
    hostFns.take 8 = [(0, "block_index", 0, 1), (1, "block_timestamp", 0, 1),
      (2, "epoch_height", 0, 1), (3, "storage_usage", 0, 1), (4, "prepaid_gas", 0, 1),
      (5, "used_gas", 0, 1), (6, "register_len", 1, 1), (7, "panic", 0, 0)] := by decide +kernel

/-- Two family members do not fit the HOST row and are therefore blocked: `validator_stake`
(`np = 3`) and `gas` (an `i32` parameter).  Every other one is callable (`hostChipIdOf` is `some`). -/
theorem ctx_shape_ok :
    (ctxNames.filter (fun n => (hostChipIdOf n).isNone)) = ["gas", "validator_stake"] := by
  decide +kernel

/-- **`validator_stake` is blocked on arity**, not missing: it is in the table with `np = 3`, and
`hostChipIdOf` / `hostChipSig` reject it, so a module importing it is outside the checker's domain
and no HOST row is ever built for it.  Widening the chip is another lane's change. -/
theorem validator_stake_blocked :
    hostSig (hostIdOf "validator_stake").get! = some (3, 0) ∧
      hostChipIdOf "validator_stake" = none ∧
      hostChipSig (hostIdOf "validator_stake").get! = none := by decide +kernel

end Chips

/-! ## `HM` primitives

`HM = EStateM String St`.  These compute one layer of it; the per-function lemmas are rewrite chains
over them. -/

/-- One bind of `HM`. -/
theorem bind_run {α β : Type} (x : HM α) (f : α → HM β) (t : St) :
    (x >>= f).run t = match x.run t with
      | .ok a s => (f a).run s
      | .error e s => .error e s := by
  show EStateM.bind x f t = _
  unfold EStateM.bind EStateM.run; cases x t <;> rfl

/-- A bind on the left of a successful `x`. -/
theorem bind_ok {α β : Type} {x : HM α} {f : α → HM β} {t s' : St} {a : α}
    (hx : x.run t = .ok a s') : (x >>= f).run t = (f a).run s' := by rw [bind_run, hx]

/-- A bind on the left of a failing `x`. -/
theorem bind_err {α β : Type} {x : HM α} {f : α → HM β} {t s' : St} {e : String}
    (hx : x.run t = .error e s') : (x >>= f).run t = .error e s' := by rw [bind_run, hx]

theorem hmGet_run (t : St) : (get : HM St).run t = .ok t t := rfl
theorem hmSet_run (u : St) (t : St) : (set u : HM Unit).run t = .ok () u := rfl

/-- `withGas`: write the new budget, then abort with the charge's error (if any). -/
theorem withGas_run (f : Gas → Gas × Option String) (s : St) :
    (withGas f).run s = (match h : (f s.gas).2 with
      | some e => .error e { s with gas := (f s.gas).1 }
      | none => .ok () { s with gas := (f s.gas).1 }) := by
  rw [withGas.eq_def, bind_ok (hmGet_run s)]
  cases hf : f s.gas with
  | mk g e => simp only [hf]; cases e with
    | none => rfl
    | some e => rfl

theorem payBaseH_run (c : Cost) (s : St) :
    (payBaseH c).run s = (match h : (payBase s.gas c).2 with
      | some e => .error e { s with gas := (payBase s.gas c).1 }
      | none => .ok () { s with gas := (payBase s.gas c).1 }) := by
  rw [payBaseH]; exact withGas_run _ s

/-- `pushRet` writes exactly one `i64` word. -/
theorem pushRet_run (s : St) (v : Nat) : (pushRet v).run s = .ok () (pushI64 s v) := by
  rw [pushRet]; rfl

/-- `popArgs 1` pops the top operand word (the getter's pointer / register id). -/
theorem popArgs1_run (s : St) :
    (popArgs 1).run s =
      .ok (⟨#[vNum (s.stack.back?.getD (.i32 0))], by simp⟩) { s with stack := s.stack.pop } := by
  unfold popArgs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [show (1 - 0 + 1 - 1) / 1 = 1 from rfl]
  simp only [List.range'_one, List.forIn_cons, List.forIn_nil, EStateM.run, popN_eq,
    Array.size_reverse, Array.push_empty]
  rfl

/-- The word a one-argument getter pops (its pointer or register id). -/
abbrev topArg (s : St) : Nat := vNum (s.stack.back?.getD (.i32 0))

/-! ## Shape A: `payBaseH C.base >>= get >>= pushRet ∘ f`

`block_index`, `block_timestamp`, `epoch_height`, `storage_usage`, `prepaid_gas`, `used_gas`.
The successful case is the one the `HOSTR` answer describes; the aborting case is a base-charge
failure and is a `status = 1` response.  Both are stated **post-state style**: the hypothesis `e1` is
the base charge's own run, `s1` its result state. -/

theorem block_index_h :
    hostCall "block_index" =
      some ((payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s => pushRet s.ctx.blockHeight) :=
  hostCall.eq_12

theorem block_timestamp_h :
    hostCall "block_timestamp" =
      some ((payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s => pushRet s.ctx.blockTimestamp) :=
  hostCall.eq_13

theorem epoch_height_h :
    hostCall "epoch_height" =
      some ((payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s => pushRet s.ctx.epochHeight) :=
  hostCall.eq_14

theorem storage_usage_h :
    hostCall "storage_usage" =
      some ((payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s => pushRet s.storageUsage) :=
  hostCall.eq_15

theorem prepaid_gas_h :
    hostCall "prepaid_gas" =
      some ((payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s => pushRet s.ctx.prepaidGas) :=
  hostCall.eq_16

theorem used_gas_h :
    hostCall "used_gas" =
      some ((payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s => pushRet s.gas.used) :=
  hostCall.eq_17

/-- **`block_index`, successful answer.**  One `i64` word: `s1.ctx.blockHeight`. -/
theorem block_index_ok (s s1 : St) (e1 : (payBaseH C.base).run s = .ok () s1) :
    (hostCall "block_index").get!.run s = .ok () (pushI64 s1 s1.ctx.blockHeight) := by
  rw [block_index_h]; simp only [Option.get!]
  rw [bind_ok e1, bind_ok (hmGet_run _), pushRet_run]

theorem block_index_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run s = .error er s1) :
    (hostCall "block_index").get!.run s = .error er s1 := by
  rw [block_index_h]; simp only [Option.get!]; exact bind_err e1

theorem block_timestamp_ok (s s1 : St) (e1 : (payBaseH C.base).run s = .ok () s1) :
    (hostCall "block_timestamp").get!.run s = .ok () (pushI64 s1 s1.ctx.blockTimestamp) := by
  rw [block_timestamp_h]; simp only [Option.get!]
  rw [bind_ok e1, bind_ok (hmGet_run _), pushRet_run]

theorem block_timestamp_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run s = .error er s1) :
    (hostCall "block_timestamp").get!.run s = .error er s1 := by
  rw [block_timestamp_h]; simp only [Option.get!]; exact bind_err e1

theorem epoch_height_ok (s s1 : St) (e1 : (payBaseH C.base).run s = .ok () s1) :
    (hostCall "epoch_height").get!.run s = .ok () (pushI64 s1 s1.ctx.epochHeight) := by
  rw [epoch_height_h]; simp only [Option.get!]
  rw [bind_ok e1, bind_ok (hmGet_run _), pushRet_run]

theorem epoch_height_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run s = .error er s1) :
    (hostCall "epoch_height").get!.run s = .error er s1 := by
  rw [epoch_height_h]; simp only [Option.get!]; exact bind_err e1

theorem storage_usage_ok (s s1 : St) (e1 : (payBaseH C.base).run s = .ok () s1) :
    (hostCall "storage_usage").get!.run s = .ok () (pushI64 s1 s1.storageUsage) := by
  rw [storage_usage_h]; simp only [Option.get!]
  rw [bind_ok e1, bind_ok (hmGet_run _), pushRet_run]

theorem storage_usage_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run s = .error er s1) :
    (hostCall "storage_usage").get!.run s = .error er s1 := by
  rw [storage_usage_h]; simp only [Option.get!]; exact bind_err e1

theorem prepaid_gas_ok (s s1 : St) (e1 : (payBaseH C.base).run s = .ok () s1) :
    (hostCall "prepaid_gas").get!.run s = .ok () (pushI64 s1 s1.ctx.prepaidGas) := by
  rw [prepaid_gas_h]; simp only [Option.get!]
  rw [bind_ok e1, bind_ok (hmGet_run _), pushRet_run]

theorem prepaid_gas_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run s = .error er s1) :
    (hostCall "prepaid_gas").get!.run s = .error er s1 := by
  rw [prepaid_gas_h]; simp only [Option.get!]; exact bind_err e1

theorem used_gas_ok (s s1 : St) (e1 : (payBaseH C.base).run s = .ok () s1) :
    (hostCall "used_gas").get!.run s = .ok () (pushI64 s1 s1.gas.used) := by
  rw [used_gas_h]; simp only [Option.get!]
  rw [bind_ok e1, bind_ok (hmGet_run _), pushRet_run]

theorem used_gas_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run s = .error er s1) :
    (hostCall "used_gas").get!.run s = .error er s1 := by
  rw [used_gas_h]; simp only [Option.get!]; exact bind_err e1

/-! ## Shape B: a `u128` getter through memory

`account_balance`, `account_locked_balance`, `attached_deposit`, `validator_total_stake`.
`popArgs 1` (the pointer) then `payBaseH C.base` then `setU128H ptr v = writeMemH ptr (natLE v 16)`.
The answer has **no result word**, so the state-side obligations are the value `v` and the pointer's
memory range `ptr + 16 ≤ memBytes`.

`writeMemH_ok` is the successful write (what `status = 0` carries) and `writeMemH_mav` the bounds
failure; the two charge failures are `status = 1` and carry `g_after` from the trace.
`setU128_prefix_ok` / `_err` are the family's common prefix (pop, base charge). -/

/-- The `writeMemH` tail after the base charge: byte charge, bounds check, then `writeBytes`. -/
def writeTail (ptr : Nat) (d : ByteArray) : HM Unit :=
  (payPerH C.writeMemoryByte d.size) >>= fun _ => (get : HM St) >>= fun s =>
    if ptr + d.size > memBytes s then
      ((hErr "MemoryAccessViolation" : HM Unit) >>= fun _ => set (writeBytes s ptr d))
     else set (writeBytes s ptr d)

theorem writeMemH_unfold (ptr : Nat) (d : ByteArray) :
    writeMemH ptr d = ((payBaseH C.writeMemoryBase) >>= fun _ => writeTail ptr d) := rfl

/-- **`writeMemH` succeeds**, from the base-charge state `s1` through the byte-charge state `s2`. -/
theorem writeMemH_ok {s s1 s2 : St} {ptr : Nat} {d : ByteArray}
    (e1 : (payBaseH C.writeMemoryBase).run s = .ok () s1)
    (e2 : (payPerH C.writeMemoryByte d.size).run s1 = .ok () s2)
    (h3 : ¬ (ptr + d.size > memBytes s2)) :
    (writeMemH ptr d).run s = .ok () (writeBytes s2 ptr d) := by
  rw [writeMemH_unfold, bind_ok e1, writeTail, bind_ok e2, bind_ok (hmGet_run _)]
  rw [ite_eq_right (by simp [h3]), hmSet_run]

/-- The memory bound fails: `writeMemH` aborts with `HostError(MemoryAccessViolation)`. -/
theorem writeMemH_mav {s s1 s2 : St} {ptr : Nat} {d : ByteArray}
    (e1 : (payBaseH C.writeMemoryBase).run s = .ok () s1)
    (e2 : (payPerH C.writeMemoryByte d.size).run s1 = .ok () s2)
    (h3 : ptr + d.size > memBytes s2) :
    (writeMemH ptr d).run s = .error "HostError(MemoryAccessViolation)" s2 := by
  rw [writeMemH_unfold, bind_ok e1, writeTail, bind_ok e2, bind_ok (hmGet_run _)]
  rw [ite_eq_left (by simp [h3])]
  rfl

/-- `setU128H ptr v` is the 16-byte little-endian write. -/
theorem setU128H_eq (ptr v : Nat) : setU128H ptr v = writeMemH ptr (natLE v 16) := rfl

/-- **The family's common prefix**: pop the pointer, charge `C.base`, then write `g s` at it.  On
success it is exactly `writeMemH (topArg s) (natLE (g s1) 16)` run from `s1`. -/
theorem setU128_prefix_ok {s s1 : St} {g : St → Nat}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s =>
      setU128H a[0] (g s) : HM Unit).run s =
      (writeMemH (topArg s) (natLE (g s1) 16)).run s1 := by
  rw [bind_ok (popArgs1_run s), bind_ok e1, bind_ok (hmGet_run _)]
  rfl

/-- The same on a base-charge failure. -/
theorem setU128_prefix_err {s s1 : St} {g : St → Nat} {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s =>
      setU128H a[0] (g s) : HM Unit).run s = .error er s1 := by
  rw [bind_ok (popArgs1_run s), bind_err e1]

theorem account_balance_h :
    hostCall "account_balance" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s =>
        setU128H a[0] s.balance) :=
  hostCall.eq_18

theorem account_locked_balance_h :
    hostCall "account_locked_balance" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s =>
        setU128H a[0] s.ctx.accountLocked) :=
  hostCall.eq_19

theorem attached_deposit_h :
    hostCall "attached_deposit" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s =>
        setU128H a[0] s.ctx.attachedDeposit) :=
  hostCall.eq_20

/-- **`account_balance`**: the answer is the 16-byte write of `s1.balance` at `topArg s`. -/
theorem account_balance_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "account_balance").get!.run s =
      (writeMemH (topArg s) (natLE s1.balance 16)).run s1 := by
  rw [account_balance_h]; simp only [Option.get!]; exact setU128_prefix_ok e1

theorem account_balance_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "account_balance").get!.run s = .error er s1 := by
  rw [account_balance_h]; simp only [Option.get!]; exact setU128_prefix_err e1

theorem account_locked_balance_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "account_locked_balance").get!.run s =
      (writeMemH (topArg s) (natLE s1.ctx.accountLocked 16)).run s1 := by
  rw [account_locked_balance_h]; simp only [Option.get!]; exact setU128_prefix_ok e1

theorem account_locked_balance_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "account_locked_balance").get!.run s = .error er s1 := by
  rw [account_locked_balance_h]; simp only [Option.get!]; exact setU128_prefix_err e1

theorem attached_deposit_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "attached_deposit").get!.run s =
      (writeMemH (topArg s) (natLE s1.ctx.attachedDeposit 16)).run s1 := by
  rw [attached_deposit_h]; simp only [Option.get!]; exact setU128_prefix_ok e1

theorem attached_deposit_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "attached_deposit").get!.run s = .error er s1 := by
  rw [attached_deposit_h]; simp only [Option.get!]; exact setU128_prefix_err e1

theorem validator_total_stake_h :
    hostCall "validator_total_stake" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ =>
        (payBaseH C.validatorTotalStakeBase) >>= fun _ =>
        (get : HM St) >>= fun s => setU128H a[0] (s.ctx.validators.foldl (fun acc v => acc + v.2) 0)) :=
  hostCall.eq_23

/-- **`validator_total_stake`**: it charges `C.base` **and** `C.validatorTotalStakeBase`, then
writes the sum of the context's validator stakes.  The state side supplies the validator table
(not a trie read). -/
theorem validator_total_stake_ok (s s1 s2 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1)
    (e2 : (payBaseH C.validatorTotalStakeBase).run s1 = .ok () s2) :
    (hostCall "validator_total_stake").get!.run s =
      (writeMemH (topArg s) (natLE (s2.ctx.validators.foldl (fun acc v => acc + v.2) 0) 16)).run s2 := by
  rw [validator_total_stake_h]; simp only [Option.get!]
  rw [bind_ok (popArgs1_run s), bind_ok e1, bind_ok e2, bind_ok (hmGet_run _)]
  rfl

theorem validator_total_stake_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "validator_total_stake").get!.run s = .error er s1 := by
  rw [validator_total_stake_h]; simp only [Option.get!]
  rw [bind_ok (popArgs1_run s), bind_err e1]

/-! ## Shape C: a register filler

`current_account_id`, `chain_id`, `signer_account_id`, `signer_account_pk`,
`predecessor_account_id`, `refund_to_account_id`, `random_seed`, and (with `ar = 1`)
`current_contract_code`.  `popArgs 1` (the register id) then `payBaseH C.base` then `regSetH id d`.
The state side supplies the byte string `d`, the register id and `regSetH`'s domain (its
`MemoryAccessViolation` limits).  `regSetH` is not modelled by the HOST chip; its outcome is the
`status` on `HOSTR` (success or `status = 1`). -/

theorem current_account_id_h :
    hostCall "current_account_id" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ =>
        (get : HM St) >>= fun s => regSetH a[0] s.ctx.currentAccount.toUTF8) :=
  hostCall.eq_4

theorem signer_account_id_h :
    hostCall "signer_account_id" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ =>
        (get : HM St) >>= fun s => regSetH a[0] s.ctx.signer.toUTF8) :=
  hostCall.eq_5

theorem signer_account_pk_h :
    hostCall "signer_account_pk" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ =>
        (get : HM St) >>= fun s => regSetH a[0] s.ctx.signerPk) :=
  hostCall.eq_6

theorem predecessor_account_id_h :
    hostCall "predecessor_account_id" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ =>
        (get : HM St) >>= fun s => regSetH a[0] s.ctx.predecessor.toUTF8) :=
  hostCall.eq_7

theorem refund_to_account_id_h :
    hostCall "refund_to_account_id" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ =>
        (get : HM St) >>= fun s => regSetH a[0] s.ctx.refundTo.toUTF8) :=
  hostCall.eq_8

theorem chain_id_h :
    hostCall "chain_id" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ =>
        (get : HM St) >>= fun s => regSetH a[0] s.ctx.chainId.toUTF8) :=
  hostCall.eq_9

theorem random_seed_h :
    hostCall "random_seed" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ =>
        (get : HM St) >>= fun s => regSetH a[0] s.ctx.randomSeed) :=
  hostCall.eq_11

/-- **The register-filler prefix**: pop the register id, charge `C.base`, then `regSetH` with the
byte string `d s`.  On success it is exactly `regSetH (topArg s) (d s1)` run from `s1`. -/
theorem regSet_prefix_ok {s s1 : St} {d : St → ByteArray}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s =>
      regSetH a[0] (d s) : HM Unit).run s = (regSetH (topArg s) (d s1)).run s1 := by
  rw [bind_ok (popArgs1_run s), bind_ok e1, bind_ok (hmGet_run _)]
  rfl

theorem regSet_prefix_err {s s1 : St} {d : St → ByteArray} {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ => (get : HM St) >>= fun s =>
      regSetH a[0] (d s) : HM Unit).run s = .error er s1 := by
  rw [bind_ok (popArgs1_run s), bind_err e1]

theorem current_account_id_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "current_account_id").get!.run s =
      (regSetH (topArg s) s1.ctx.currentAccount.toUTF8).run s1 := by
  rw [current_account_id_h]; simp only [Option.get!]; exact regSet_prefix_ok e1

theorem current_account_id_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "current_account_id").get!.run s = .error er s1 := by
  rw [current_account_id_h]; simp only [Option.get!]; exact regSet_prefix_err e1

theorem chain_id_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "chain_id").get!.run s = (regSetH (topArg s) s1.ctx.chainId.toUTF8).run s1 := by
  rw [chain_id_h]; simp only [Option.get!]; exact regSet_prefix_ok e1

theorem chain_id_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "chain_id").get!.run s = .error er s1 := by
  rw [chain_id_h]; simp only [Option.get!]; exact regSet_prefix_err e1

theorem signer_account_id_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "signer_account_id").get!.run s =
      (regSetH (topArg s) s1.ctx.signer.toUTF8).run s1 := by
  rw [signer_account_id_h]; simp only [Option.get!]; exact regSet_prefix_ok e1

theorem signer_account_id_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "signer_account_id").get!.run s = .error er s1 := by
  rw [signer_account_id_h]; simp only [Option.get!]; exact regSet_prefix_err e1

theorem signer_account_pk_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "signer_account_pk").get!.run s = (regSetH (topArg s) s1.ctx.signerPk).run s1 := by
  rw [signer_account_pk_h]; simp only [Option.get!]; exact regSet_prefix_ok e1

theorem signer_account_pk_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "signer_account_pk").get!.run s = .error er s1 := by
  rw [signer_account_pk_h]; simp only [Option.get!]; exact regSet_prefix_err e1

theorem predecessor_account_id_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "predecessor_account_id").get!.run s =
      (regSetH (topArg s) s1.ctx.predecessor.toUTF8).run s1 := by
  rw [predecessor_account_id_h]; simp only [Option.get!]; exact regSet_prefix_ok e1

theorem predecessor_account_id_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "predecessor_account_id").get!.run s = .error er s1 := by
  rw [predecessor_account_id_h]; simp only [Option.get!]; exact regSet_prefix_err e1

theorem refund_to_account_id_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "refund_to_account_id").get!.run s =
      (regSetH (topArg s) s1.ctx.refundTo.toUTF8).run s1 := by
  rw [refund_to_account_id_h]; simp only [Option.get!]; exact regSet_prefix_ok e1

theorem refund_to_account_id_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "refund_to_account_id").get!.run s = .error er s1 := by
  rw [refund_to_account_id_h]; simp only [Option.get!]; exact regSet_prefix_err e1

theorem random_seed_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "random_seed").get!.run s = (regSetH (topArg s) s1.ctx.randomSeed).run s1 := by
  rw [random_seed_h]; simp only [Option.get!]; exact regSet_prefix_ok e1

theorem random_seed_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "random_seed").get!.run s = .error er s1 := by
  rw [random_seed_h]; simp only [Option.get!]; exact regSet_prefix_err e1

theorem current_contract_code_h :
    hostCall "current_contract_code" = some
      ((popArgs 1) >>= fun a => (payBaseH C.base) >>= fun _ =>
        (get : HM St) >>= fun s => match s.ctx.accountContract with
          | none => pushRet 0
          | some h => regSetH a[0] h >>= fun _ => pushRet 1) :=
  hostCall.eq_21

set_option maxRecDepth 100000 in
/-- `current_contract_code`: `AccountContract::None` pushes `0` (the harness default); `Local h`
fills the register and pushes `1`.  The state side supplies the `Option` and, for `Local`, the
code bytes and the register id. -/
theorem current_contract_code_none_ok (s s1 : St)
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1)
    (hn : s1.ctx.accountContract = none) :
    (hostCall "current_contract_code").get!.run s = .ok () (pushI64 s1 0) := by
  rw [current_contract_code_h]; simp only [Option.get!]
  rw [bind_ok (popArgs1_run s), bind_ok e1, bind_ok (hmGet_run _), hn, pushRet_run]

set_option maxRecDepth 100000 in
theorem current_contract_code_local_ok (s s1 s2 : St) {h : ByteArray}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .ok () s1)
    (hc : s1.ctx.accountContract = some h)
    (e2 : (regSetH (topArg s) h).run s1 = .ok () s2) :
    (hostCall "current_contract_code").get!.run s = .ok () (pushI64 s2 1) := by
  rw [current_contract_code_h]; simp only [Option.get!]
  rw [bind_ok (popArgs1_run s), bind_ok e1, bind_ok (hmGet_run _),
    show (s1.ctx.accountContract) = some h from hc]
  rw [show (⟨#[topArg s], by simp⟩ : Vector Nat 1)[0] = topArg s from by simp]
  rw [bind_ok e2, pushRet_run]

set_option maxRecDepth 100000 in
theorem current_contract_code_err (s s1 : St) {er : String}
    (e1 : (payBaseH C.base).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "current_contract_code").get!.run s = .error er s1 := by
  rw [current_contract_code_h]; simp only [Option.get!]
  rw [bind_ok (popArgs1_run s), bind_err e1]

/-! ## Shape D: `gas` — **blocked on the argument tag**

`gas(amount)` burns `amount · 822756` with no base charge and pushes nothing.  It is **not callable
in this slice**: its parameter is `i32` (`HostSigs.lean:88`) while the HOST row's argument slots are
`i64` (`cTag0`/`cTag1`, and the trace generator asserts `tag = 1`), so a call to it would need
`tagP 0 = 0` and the row would not satisfy `cTag0`.  The reduction below is still stated and proved,
because it is the semantics the state side must reproduce once the tag becomes a bit; the function
itself is listed as blocked (`Chips.ctx_shape_ok`).

`gas(amount)` burns `amount · 822756` with **no** base charge and pushes nothing (`ar = 0`); that
is the spec's transliteration of `GasCounter::burn` (`Host.lean:689-691`).  It is the one family
member whose `g_after` is not just `remaining`: the burn moves `gas.burnt`, so
`remaining = prepaid − used` moves by the burn too.  The HOST chip already returns the resulting
`g_after` on `HOSTR`, so this needs no new AIR — but the state side must take `g_after` from the
trace rather than recompute it from `S` alone. -/

/-- The gas constant the spec burns per unit (`Host.lean:691`). -/
def gasPriceOld : Nat := 822756

set_option maxRecDepth 1000000 in
theorem gas_h :
    hostCall "gas" = some ((popArgs 1) >>= fun a => burnH (a[0] * gasPriceOld)) := by
  rfl

/-- **`gas`**: pop the amount, burn `amount · 822756`, no word, no base charge. -/
theorem gas_ok (s s1 : St)
    (e : (burnH (topArg s * gasPriceOld)).run { s with stack := s.stack.pop } = .ok () s1) :
    (hostCall "gas").get!.run s = .ok () s1 := by
  rw [gas_h]; simp only [Option.get!]
  rw [bind_ok (popArgs1_run s)]
  exact e

theorem gas_err (s s1 : St) {er : String}
    (e : (burnH (topArg s * gasPriceOld)).run { s with stack := s.stack.pop } = .error er s1) :
    (hostCall "gas").get!.run s = .error er s1 := by
  rw [gas_h]; simp only [Option.get!]
  rw [bind_ok (popArgs1_run s)]
  exact e

/-! ## Blocked on arity: `validator_stake`

`validator_stake(len, ptr, out_ptr)` has `np = 3`; the `HOSTQ` message has two argument slots.  Its
spec arm (`hostCall.eq_22`) reads the account id from `(len, ptr)`, charges
`C.validatorStakeBase`, and writes the stake to `out_ptr`.  Covering it needs the chip's message
widened, which is another lane's change; `Chips.validator_stake_blocked` records the exact reason it
is not in this slice. -/

end WasmBase
