import WasmBase.Main.HostTwoRun

/-!
# WasmBase.Main.HostTwoRunArms — the two-run footprint of the host arms and of `callHost` (E2E M6.1)
-/

namespace WasmBase
namespace TwoRun
open NearSpecV3.Wasm
open HostFoot
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Popping the arguments -/

/-- The arguments `popArgs n` pops from `s` (first argument first). -/
def argsOf (n : Nat) (s : St) : Vector Nat n := ⟨(popsF n s #[]).1.reverse, by simp [popsF_size]⟩

/-- The `i`-th argument (no bound proof: canonical atoms for `omega`). -/
def argN (n : Nat) (s : St) (i : Nat) : Nat := ((popsF n s #[]).1.reverse)[i]!

@[simp] theorem argsOf_get (n : Nat) (s : St) (i : Nat) (h : i < n) : (argsOf n s)[i] = argN n s i := by
  have h' : i < (popsF n s #[]).1.reverse.size := by simp [popsF_size]; exact h
  simp only [argsOf, argN, Vector.getElem_mk]
  exact (getElem!_pos _ i h').symm

theorem popArgs_ok (n : Nat) (s : St) : popArgs n s = .ok (argsOf n s) (popsF n s #[]).2 := popArgs_eq n s

section
variable {s0 s0' : St} {k : Nat} {A : Nat → Prop}

/-- **An arm that starts by popping its arguments**: the two runs pop the same arguments (those of
the left state, `argsOf n s0`) into twinned states, and continue in lock step. -/
theorem rc_popArgs_bind (hL : Low A k s0 s0') {n : Nat} (hn : n ≤ k) {β : Type} {W : β → Prop}
    {f : Vector Nat n → HM β} (hf : Rel2 (Tw s0 s0' k A) W (f (argsOf n s0)) (f (argsOf n s0))) :
    RC (Tw s0 s0' k A) W ((popArgs n >>= f) s0) ((popArgs n >>= f) s0') := by
  obtain ⟨a, y, y', h1, h2, hT⟩ := popArgs_two hL hn
  have ha : a = argsOf n s0 := by
    rw [popArgs_ok] at h1; cases h1; rfl
  simp only [bind, EStateM.bind, h1, h2]
  subst ha
  exact hf y y' hT

/-- An arm without arguments runs in lock step from the start pair. -/
theorem rc_of_rel (hL : Low A k s0 s0') {β : Type} {W : β → Prop} {m : HM β}
    (hm : Rel2 (Tw s0 s0' k A) W m m) : RC (Tw s0 s0' k A) W (m s0) (m s0') :=
  hm s0 s0' (tw_start hL)

end

/-! ## 2. Read sets -/

/-- The addresses `[ptr, ptr + len)`. -/
def memRange (ptr len : Nat) : Nat → Prop := fun b => ptr ≤ b ∧ b < ptr + len

/-- The memory read of `memOrRegH ptr len`: `[ptr, ptr + len)` unless `len = u64::MAX` (a register). -/
def mrRange (ptr len : Nat) : Nat → Prop := fun b => len ≠ u64Bound - 1 ∧ memRange ptr len b

/-- One memory read of an arm (a description; `rdIn` is its address set). -/
inductive Rd where
  /-- `memOrRegH ptr len`: `[ptr, ptr + len)`, or a register when `len = u64::MAX` -/
  | mr (ptr len : Nat)
  /-- `readMemH ptr len` -/
  | m (ptr len : Nat)
  /-- `utf8H len ptr`: `[ptr, ptr + len)`, or (NUL-terminated, `len = u64::MAX`) the window
  `[ptr, ptr + maxTotalLogLength]` — a superset of the bytes the scan reads -/
  | u8 (ptr len : Nat)
  /-- `[ptr, memBytes)`: the memory from `ptr` on — the (coarse) read set of the UTF-16 arms, whose
  lengths are read from memory -/
  | tail (ptr : Nat)

def rdIn (s : St) : Rd → Nat → Prop
  | .mr p l, b => l ≠ u64Bound - 1 ∧ p ≤ b ∧ b < p + l
  | .m p l, b => p ≤ b ∧ b < p + l
  | .u8 p l, b => (l ≠ u64Bound - 1 ∧ p ≤ b ∧ b < p + l) ∨ (l = u64Bound - 1 ∧ p ≤ b ∧ b ≤ p + maxTotalLogLength)
  | .tail p, b => p ≤ b ∧ b < memBytes s

def rdSet (s : St) : List Rd → Nat → Prop
  | [], _ => False
  | e :: l, b => rdIn s e b ∨ rdSet s l b

/-- The number of arguments an arm pops. -/
def nargs (name : String) : Nat :=
  match name with
  | "read_register" => 2 | "register_len" => 1 | "write_register" => 3
  | "current_account_id" => 1 | "signer_account_id" => 1 | "signer_account_pk" => 1
  | "predecessor_account_id" => 1 | "refund_to_account_id" => 1 | "chain_id" => 1 | "input" => 1
  | "random_seed" => 1
  | "account_balance" => 1 | "account_locked_balance" => 1 | "attached_deposit" => 1
  | "current_contract_code" => 1 | "validator_stake" => 3 | "validator_total_stake" => 1
  | "sha256" => 3 | "keccak256" => 3 | "keccak512" => 3 | "ripemd160" => 3
  | "value_return" => 2 | "panic_utf8" => 2 | "log_utf8" => 2 | "log_utf16" => 2 | "abort" => 4
  | "gas" => 1 | "storage_write" => 5 | "storage_read" => 3 | "storage_remove" => 3 | "storage_has_key" => 2
  | "storage_iter_prefix" => 2 | "storage_iter_range" => 4 | "storage_iter_next" => 3
  | "promise_batch_create" => 2 | "promise_batch_then" => 3 | "promise_and" => 2 | "promise_create" => 8
  | "promise_then" => 9 | "promise_set_refund_to" => 3 | "promise_batch_action_create_account" => 1
  | "promise_batch_action_deploy_contract" => 3 | "promise_batch_action_function_call" => 7
  | "promise_batch_action_function_call_weight" => 8 | "promise_batch_action_transfer" => 2
  | "promise_batch_action_stake" => 4 | "promise_batch_action_add_key_with_full_access" => 4
  | "promise_batch_action_add_key_with_function_call" => 9 | "promise_batch_action_delete_key" => 3
  | "promise_batch_action_delete_account" => 3 | "promise_result" => 2 | "promise_return" => 1
  | "promise_yield_create" => 7 | "promise_yield_resume" => 4 | "ed25519_verify" => 6
  | "promise_yield_create_with_id" => 9 | "promise_batch_action_transfer_to_gas_key" => 4
  | "promise_batch_action_add_gas_key_with_full_access" => 4
  | "promise_batch_action_add_gas_key_with_function_call" => 9
  | "promise_yield_resume_with_yield_id" => 4
  | "promise_batch_action_deploy_global_contract" => 3
  | "promise_batch_action_deploy_global_contract_by_account_id" => 3
  | "promise_batch_action_use_global_contract" => 3
  | "promise_batch_action_use_global_contract_by_account_id" => 3
  | "promise_batch_action_state_init" => 4 | "promise_batch_action_state_init_by_account_id" => 4
  | "set_state_init_data_entry" => 6
  | _ => 0

/-- **The memory reads of each arm**, in terms of the left state's arguments (`argsOf`). -/
def reads (name : String) (s : St) : List Rd :=
  match name with
  | "write_register" =>
      [.m (argN 3 s 2) (argN 3 s 1)]
  | "validator_stake" =>
      [.mr (argN 3 s 1) (argN 3 s 0)]
  | "sha256" =>
      [.mr (argN 3 s 1) (argN 3 s 0)]
  | "keccak256" =>
      [.mr (argN 3 s 1) (argN 3 s 0)]
  | "keccak512" =>
      [.mr (argN 3 s 1) (argN 3 s 0)]
  | "ripemd160" =>
      [.mr (argN 3 s 1) (argN 3 s 0)]
  | "value_return" =>
      [.mr (argN 2 s 1) (argN 2 s 0)]
  | "panic_utf8" =>
      [.u8 (argN 2 s 1) (argN 2 s 0)]
  | "log_utf8" =>
      [.u8 (argN 2 s 1) (argN 2 s 0)]
  | "log_utf16" =>
      [.tail (argN 2 s 1)]
  | "abort" =>
      [.tail ((argN 4 s 0) % 2 ^ 32 - 4), .tail ((argN 4 s 1) % 2 ^ 32 - 4)]
  | "storage_write" =>
      [.mr (argN 5 s 1) (argN 5 s 0), .mr (argN 5 s 3) (argN 5 s 2)]
  | "storage_read" =>
      [.mr (argN 3 s 1) (argN 3 s 0)]
  | "storage_remove" =>
      [.mr (argN 3 s 1) (argN 3 s 0)]
  | "storage_has_key" =>
      [.mr (argN 2 s 1) (argN 2 s 0)]
  | "promise_batch_create" =>
      [.mr (argN 2 s 1) (argN 2 s 0)]
  | "promise_batch_then" =>
      [.mr (argN 3 s 2) (argN 3 s 1)]
  | "promise_and" =>
      [.m (argN 2 s 0) ((argN 2 s 1) * 8)]
  | "promise_create" =>
      [.mr (argN 8 s 1) (argN 8 s 0), .m (argN 8 s 6) 16, .mr (argN 8 s 3) (argN 8 s 2), .mr (argN 8 s 5) (argN 8 s 4)]
  | "promise_then" =>
      [.mr (argN 9 s 2) (argN 9 s 1), .m (argN 9 s 7) 16, .mr (argN 9 s 4) (argN 9 s 3), .mr (argN 9 s 6) (argN 9 s 5)]
  | "promise_set_refund_to" =>
      [.mr (argN 3 s 2) (argN 3 s 1)]
  | "promise_batch_action_deploy_contract" =>
      [.mr (argN 3 s 2) (argN 3 s 1)]
  | "promise_batch_action_function_call" =>
      [.m (argN 7 s 5) 16, .mr (argN 7 s 2) (argN 7 s 1), .mr (argN 7 s 4) (argN 7 s 3)]
  | "promise_batch_action_function_call_weight" =>
      [.m (argN 8 s 5) 16, .mr (argN 8 s 2) (argN 8 s 1), .mr (argN 8 s 4) (argN 8 s 3)]
  | "promise_batch_action_transfer" =>
      [.m (argN 2 s 1) 16]
  | "promise_batch_action_stake" =>
      [.m (argN 4 s 1) 16, .mr (argN 4 s 3) (argN 4 s 2)]
  | "promise_batch_action_add_key_with_full_access" =>
      [.mr (argN 4 s 2) (argN 4 s 1)]
  | "promise_batch_action_add_key_with_function_call" =>
      [.mr (argN 9 s 2) (argN 9 s 1), .m (argN 9 s 4) 16, .mr (argN 9 s 6) (argN 9 s 5), .mr (argN 9 s 8) (argN 9 s 7)]
  | "promise_batch_action_delete_key" =>
      [.mr (argN 3 s 2) (argN 3 s 1)]
  | "promise_batch_action_delete_account" =>
      [.mr (argN 3 s 2) (argN 3 s 1)]
  | "promise_yield_create" =>
      [.mr (argN 7 s 1) (argN 7 s 0), .mr (argN 7 s 3) (argN 7 s 2)]
  | "promise_yield_resume" =>
      [.mr (argN 4 s 1) (argN 4 s 0), .mr (argN 4 s 3) (argN 4 s 2)]
  | "ed25519_verify" =>
      [.mr (argN 6 s 1) (argN 6 s 0), .mr (argN 6 s 3) (argN 6 s 2), .mr (argN 6 s 5) (argN 6 s 4)]
  | "promise_yield_create_with_id" =>
      [.m (argN 9 s 4) 16, .mr (argN 9 s 1) (argN 9 s 0), .mr (argN 9 s 3) (argN 9 s 2), .mr (argN 9 s 8) (argN 9 s 7)]
  | "promise_batch_action_transfer_to_gas_key" =>
      [.mr (argN 4 s 2) (argN 4 s 1), .m (argN 4 s 3) 16]
  | "promise_batch_action_add_gas_key_with_full_access" =>
      [.mr (argN 4 s 2) (argN 4 s 1)]
  | "promise_batch_action_add_gas_key_with_function_call" =>
      [.mr (argN 9 s 2) (argN 9 s 1), .m (argN 9 s 4) 16, .mr (argN 9 s 6) (argN 9 s 5), .mr (argN 9 s 8) (argN 9 s 7)]
  | "promise_yield_resume_with_yield_id" =>
      [.mr (argN 4 s 1) (argN 4 s 0), .mr (argN 4 s 3) (argN 4 s 2)]
  | "promise_batch_action_deploy_global_contract" =>
      [.mr (argN 3 s 2) (argN 3 s 1)]
  | "promise_batch_action_deploy_global_contract_by_account_id" =>
      [.mr (argN 3 s 2) (argN 3 s 1)]
  | "promise_batch_action_use_global_contract" =>
      [.mr (argN 3 s 2) (argN 3 s 1)]
  | "promise_batch_action_use_global_contract_by_account_id" =>
      [.mr (argN 3 s 2) (argN 3 s 1)]
  | "promise_batch_action_state_init" =>
      [.mr (argN 4 s 2) (argN 4 s 1), .m (argN 4 s 3) 16]
  | "promise_batch_action_state_init_by_account_id" =>
      [.mr (argN 4 s 2) (argN 4 s 1), .m (argN 4 s 3) 16]
  | "set_state_init_data_entry" =>
      [.mr (argN 6 s 3) (argN 6 s 2), .mr (argN 6 s 5) (argN 6 s 4)]
  | _ => []

/-- **The read set of an arm** at the left start state. -/
def readSetOf (name : String) (s : St) : Nat → Prop := rdSet s (reads name s)

/-- **The two-run statement for one arm**: from a low-equivalent start pair (on a superset of the
arm's read set, with the arm's arguments in the shared stack top), the two runs correspond. -/
def ArmTwo (name : String) : Prop :=
  ∀ (s0 s0' : St) (k : Nat) (A : Nat → Prop) (h : HM Unit), hostCall name = some h →
    Low A k s0 s0' → nargs name ≤ k → (∀ b, readSetOf name s0 b → A b) →
    RC (Tw s0 s0' k A) (fun _ => True) (h s0) (h s0')

/-- Close the byte-equality side goals left by `rel_auto` inside a byte loop. -/
syntax "tw_rd " term : tactic
open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| tw_rd $hA) => withMainContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      unless (← whnfR (← instantiateMVars d.type)).isAppOf ``Tw do continue
      let stx ← Term.exprToSyntax d.toExpr
      let saved ← saveState
      try
        evalTactic (← `(tactic| (have hm := Tw.mem0 $stx; simp (disch := first | (apply $hA; simp only [argsOf_get, Prod.mk.injEq] at *; simp [List.mem_range'] at *; omega) | (intro i hi; apply $hA; simp only [argsOf_get, Prod.mk.injEq] at *; omega)) only [Tw.read $stx, Tw.readBytes $stx]; done)))
        return
      catch _ => saved.restore
    throwError "tw_rd: failed"

/-- The per-arm proof: unfold the arm, pop the arguments, `rel_auto`, discharge the read-set goals. -/
syntax "arm_two " str : tactic
macro_rules
  | `(tactic| arm_two $nm) => `(tactic|
      (intro s0 s0' k A h e hL hk hA
       have e2 : hostCall $nm = some _ := rfl
       rw [e2] at e; injection e with e; subst e; clear e2
       conv at hk => lhs; whnf
       unfold readSetOf at hA
       conv at hA => enter [b, 1, 2]; whnf
       simp only [rdSet, rdIn] at hA
       apply rc_popArgs_bind hL hk
       rel_auto
       all_goals first
         | (intro _ i hi; apply hA; simp only [argsOf_get, Prod.mk.injEq] at *; omega)
         | tw_rd hA))

/-- The per-arm proof of an arm without arguments. -/
syntax "arm_two0 " str : tactic
macro_rules
  | `(tactic| arm_two0 $nm) => `(tactic|
      (intro s0 s0' k A h e hL _ _
       have e2 : hostCall $nm = some _ := rfl
       rw [e2] at e; injection e with e
       apply rc_of_rel hL
       subst e; clear e2
       rel_auto))

theorem arm2_read_register : ArmTwo "read_register" := by arm_two "read_register"
theorem arm2_register_len : ArmTwo "register_len" := by arm_two "register_len"
theorem arm2_write_register : ArmTwo "write_register" := by arm_two "write_register"
theorem arm2_current_account_id : ArmTwo "current_account_id" := by arm_two "current_account_id"
theorem arm2_signer_account_id : ArmTwo "signer_account_id" := by arm_two "signer_account_id"
theorem arm2_signer_account_pk : ArmTwo "signer_account_pk" := by arm_two "signer_account_pk"
theorem arm2_predecessor_account_id : ArmTwo "predecessor_account_id" := by arm_two "predecessor_account_id"
theorem arm2_refund_to_account_id : ArmTwo "refund_to_account_id" := by arm_two "refund_to_account_id"
theorem arm2_chain_id : ArmTwo "chain_id" := by arm_two "chain_id"
theorem arm2_input : ArmTwo "input" := by arm_two "input"
theorem arm2_random_seed : ArmTwo "random_seed" := by arm_two "random_seed"
theorem arm2_block_index : ArmTwo "block_index" := by arm_two0 "block_index"
theorem arm2_block_timestamp : ArmTwo "block_timestamp" := by arm_two0 "block_timestamp"
theorem arm2_epoch_height : ArmTwo "epoch_height" := by arm_two0 "epoch_height"
theorem arm2_storage_usage : ArmTwo "storage_usage" := by arm_two0 "storage_usage"
theorem arm2_prepaid_gas : ArmTwo "prepaid_gas" := by arm_two0 "prepaid_gas"
theorem arm2_used_gas : ArmTwo "used_gas" := by arm_two0 "used_gas"
theorem arm2_account_balance : ArmTwo "account_balance" := by arm_two "account_balance"
theorem arm2_account_locked_balance : ArmTwo "account_locked_balance" := by arm_two "account_locked_balance"
theorem arm2_attached_deposit : ArmTwo "attached_deposit" := by arm_two "attached_deposit"
theorem arm2_current_contract_code : ArmTwo "current_contract_code" := by arm_two "current_contract_code"
theorem arm2_validator_stake : ArmTwo "validator_stake" := by arm_two "validator_stake"
theorem arm2_validator_total_stake : ArmTwo "validator_total_stake" := by arm_two "validator_total_stake"
theorem arm2_sha256 : ArmTwo "sha256" := by arm_two "sha256"
theorem arm2_keccak256 : ArmTwo "keccak256" := by arm_two "keccak256"
theorem arm2_keccak512 : ArmTwo "keccak512" := by arm_two "keccak512"
theorem arm2_ripemd160 : ArmTwo "ripemd160" := by arm_two "ripemd160"
theorem arm2_value_return : ArmTwo "value_return" := by arm_two "value_return"
theorem arm2_panic : ArmTwo "panic" := by arm_two0 "panic"
theorem arm2_panic_utf8 : ArmTwo "panic_utf8" := by arm_two "panic_utf8"
theorem arm2_log_utf8 : ArmTwo "log_utf8" := by arm_two "log_utf8"
theorem arm2_log_utf16 : ArmTwo "log_utf16" := by arm_two "log_utf16"
theorem arm2_abort : ArmTwo "abort" := by arm_two "abort"
theorem arm2_gas : ArmTwo "gas" := by arm_two "gas"
theorem arm2_storage_write : ArmTwo "storage_write" := by arm_two "storage_write"
theorem arm2_storage_read : ArmTwo "storage_read" := by arm_two "storage_read"
theorem arm2_storage_remove : ArmTwo "storage_remove" := by arm_two "storage_remove"
theorem arm2_storage_has_key : ArmTwo "storage_has_key" := by arm_two "storage_has_key"
theorem arm2_storage_iter_prefix : ArmTwo "storage_iter_prefix" := by arm_two "storage_iter_prefix"
theorem arm2_storage_iter_range : ArmTwo "storage_iter_range" := by arm_two "storage_iter_range"
theorem arm2_storage_iter_next : ArmTwo "storage_iter_next" := by arm_two "storage_iter_next"
theorem arm2_promise_batch_create : ArmTwo "promise_batch_create" := by arm_two "promise_batch_create"
theorem arm2_promise_batch_then : ArmTwo "promise_batch_then" := by arm_two "promise_batch_then"
theorem arm2_promise_and : ArmTwo "promise_and" := by arm_two "promise_and"
theorem arm2_promise_create : ArmTwo "promise_create" := by arm_two "promise_create"
theorem arm2_promise_then : ArmTwo "promise_then" := by arm_two "promise_then"
theorem arm2_promise_set_refund_to : ArmTwo "promise_set_refund_to" := by arm_two "promise_set_refund_to"
theorem arm2_promise_batch_action_create_account : ArmTwo "promise_batch_action_create_account" := by arm_two "promise_batch_action_create_account"
theorem arm2_promise_batch_action_deploy_contract : ArmTwo "promise_batch_action_deploy_contract" := by arm_two "promise_batch_action_deploy_contract"
theorem arm2_promise_batch_action_function_call : ArmTwo "promise_batch_action_function_call" := by arm_two "promise_batch_action_function_call"
theorem arm2_promise_batch_action_function_call_weight : ArmTwo "promise_batch_action_function_call_weight" := by arm_two "promise_batch_action_function_call_weight"
theorem arm2_promise_batch_action_transfer : ArmTwo "promise_batch_action_transfer" := by arm_two "promise_batch_action_transfer"
theorem arm2_promise_batch_action_stake : ArmTwo "promise_batch_action_stake" := by arm_two "promise_batch_action_stake"
theorem arm2_promise_batch_action_add_key_with_full_access : ArmTwo "promise_batch_action_add_key_with_full_access" := by arm_two "promise_batch_action_add_key_with_full_access"
theorem arm2_promise_batch_action_add_key_with_function_call : ArmTwo "promise_batch_action_add_key_with_function_call" := by arm_two "promise_batch_action_add_key_with_function_call"
theorem arm2_promise_batch_action_delete_key : ArmTwo "promise_batch_action_delete_key" := by arm_two "promise_batch_action_delete_key"
theorem arm2_promise_batch_action_delete_account : ArmTwo "promise_batch_action_delete_account" := by arm_two "promise_batch_action_delete_account"
theorem arm2_promise_results_count : ArmTwo "promise_results_count" := by arm_two0 "promise_results_count"
theorem arm2_promise_result : ArmTwo "promise_result" := by arm_two "promise_result"
theorem arm2_promise_return : ArmTwo "promise_return" := by arm_two "promise_return"
theorem arm2_promise_yield_create : ArmTwo "promise_yield_create" := by arm_two "promise_yield_create"
theorem arm2_promise_yield_resume : ArmTwo "promise_yield_resume" := by arm_two "promise_yield_resume"
theorem arm2_ed25519_verify : ArmTwo "ed25519_verify" := by arm_two "ed25519_verify"
theorem arm2_promise_yield_create_with_id : ArmTwo "promise_yield_create_with_id" := by arm_two "promise_yield_create_with_id"
theorem arm2_promise_batch_action_transfer_to_gas_key : ArmTwo "promise_batch_action_transfer_to_gas_key" := by arm_two "promise_batch_action_transfer_to_gas_key"
theorem arm2_promise_batch_action_add_gas_key_with_full_access : ArmTwo "promise_batch_action_add_gas_key_with_full_access" := by arm_two "promise_batch_action_add_gas_key_with_full_access"
theorem arm2_promise_batch_action_add_gas_key_with_function_call : ArmTwo "promise_batch_action_add_gas_key_with_function_call" := by arm_two "promise_batch_action_add_gas_key_with_function_call"
theorem arm2_promise_yield_resume_with_yield_id : ArmTwo "promise_yield_resume_with_yield_id" := by arm_two "promise_yield_resume_with_yield_id"
theorem arm2_promise_batch_action_deploy_global_contract : ArmTwo "promise_batch_action_deploy_global_contract" := by arm_two "promise_batch_action_deploy_global_contract"
theorem arm2_promise_batch_action_deploy_global_contract_by_account_id : ArmTwo "promise_batch_action_deploy_global_contract_by_account_id" := by arm_two "promise_batch_action_deploy_global_contract_by_account_id"
theorem arm2_promise_batch_action_use_global_contract : ArmTwo "promise_batch_action_use_global_contract" := by arm_two "promise_batch_action_use_global_contract"
theorem arm2_promise_batch_action_use_global_contract_by_account_id : ArmTwo "promise_batch_action_use_global_contract_by_account_id" := by arm_two "promise_batch_action_use_global_contract_by_account_id"
theorem arm2_promise_batch_action_state_init : ArmTwo "promise_batch_action_state_init" := by arm_two "promise_batch_action_state_init"
theorem arm2_promise_batch_action_state_init_by_account_id : ArmTwo "promise_batch_action_state_init_by_account_id" := by arm_two "promise_batch_action_state_init_by_account_id"
theorem arm2_set_state_init_data_entry : ArmTwo "set_state_init_data_entry" := by arm_two "set_state_init_data_entry"

end TwoRun
end WasmBase
