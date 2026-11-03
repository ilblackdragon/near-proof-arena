import WasmBase.Main.HostTwoRunArms

/-!
# WasmBase.Main.HostTwoRunCall — `callHost_two_run`: a host call cannot tell low-equivalent states apart (E2E M6.1)

* `armTwo_all`: every arm of D3α's `hostCall` (75 names, `hostNames`) satisfies `ArmTwo`
  (`Main/HostTwoRunArms.lean`).
* `HostEff`, `HostEff.apply`: a host call's effect as data — the shared stack top replaced, a list of
  byte writes, the new host part (gas, context, storage, logs, promises, registers, …).
* **`callHost_two_run`**: from `Low (readSetOf name s) k s s'` (equal host parts, equal top-`k` stack
  entries, `k ≥ nargs name`, well-sized pages of equal count, equal bytes on the arm's read set),
  `callHost s name` and `callHost s' name` correspond (`CallCorr`): both continue, both abort with
  the same message, or both are unmodeled with the same message; continuing/aborting post-states are
  **one effect applied to both** (`x = eff.apply s`, `x' = eff.apply s'`), so in particular they
  agree on `sideR` and `gas.g`, popped/pushed the same values, wrote the same bytes, and left frames,
  globals, the stack below the top `k` and the unread bytes untouched.
-/

namespace WasmBase
namespace TwoRun
open NearSpecV3.Wasm
open HostFoot
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. All arms -/

/-- The 75 names `hostCall` has an arm for (in `hostCall`'s order). -/
def hostNames : List String :=
  ["read_register",
   "register_len",
   "write_register",
   "current_account_id",
   "signer_account_id",
   "signer_account_pk",
   "predecessor_account_id",
   "refund_to_account_id",
   "chain_id",
   "input",
   "random_seed",
   "block_index",
   "block_timestamp",
   "epoch_height",
   "storage_usage",
   "prepaid_gas",
   "used_gas",
   "account_balance",
   "account_locked_balance",
   "attached_deposit",
   "current_contract_code",
   "validator_stake",
   "validator_total_stake",
   "sha256",
   "keccak256",
   "keccak512",
   "ripemd160",
   "value_return",
   "panic",
   "panic_utf8",
   "log_utf8",
   "log_utf16",
   "abort",
   "gas",
   "storage_write",
   "storage_read",
   "storage_remove",
   "storage_has_key",
   "storage_iter_prefix",
   "storage_iter_range",
   "storage_iter_next",
   "promise_batch_create",
   "promise_batch_then",
   "promise_and",
   "promise_create",
   "promise_then",
   "promise_set_refund_to",
   "promise_batch_action_create_account",
   "promise_batch_action_deploy_contract",
   "promise_batch_action_function_call",
   "promise_batch_action_function_call_weight",
   "promise_batch_action_transfer",
   "promise_batch_action_stake",
   "promise_batch_action_add_key_with_full_access",
   "promise_batch_action_add_key_with_function_call",
   "promise_batch_action_delete_key",
   "promise_batch_action_delete_account",
   "promise_results_count",
   "promise_result",
   "promise_return",
   "promise_yield_create",
   "promise_yield_resume",
   "ed25519_verify",
   "promise_yield_create_with_id",
   "promise_batch_action_transfer_to_gas_key",
   "promise_batch_action_add_gas_key_with_full_access",
   "promise_batch_action_add_gas_key_with_function_call",
   "promise_yield_resume_with_yield_id",
   "promise_batch_action_deploy_global_contract",
   "promise_batch_action_deploy_global_contract_by_account_id",
   "promise_batch_action_use_global_contract",
   "promise_batch_action_use_global_contract_by_account_id",
   "promise_batch_action_state_init",
   "promise_batch_action_state_init_by_account_id",
   "set_state_init_data_entry"]

set_option maxHeartbeats 20000000 in
/-- **Every arm of `hostCall` satisfies the two-run statement** (one `split` of the name match). -/
theorem armTwo_all (name : String) : ArmTwo name := by
  intro s0 s0' k A h e
  unfold hostCall at e
  split at e
  case h_1 => exact arm2_read_register s0 s0' k A h e
  case h_2 => exact arm2_register_len s0 s0' k A h e
  case h_3 => exact arm2_write_register s0 s0' k A h e
  case h_4 => exact arm2_current_account_id s0 s0' k A h e
  case h_5 => exact arm2_signer_account_id s0 s0' k A h e
  case h_6 => exact arm2_signer_account_pk s0 s0' k A h e
  case h_7 => exact arm2_predecessor_account_id s0 s0' k A h e
  case h_8 => exact arm2_refund_to_account_id s0 s0' k A h e
  case h_9 => exact arm2_chain_id s0 s0' k A h e
  case h_10 => exact arm2_input s0 s0' k A h e
  case h_11 => exact arm2_random_seed s0 s0' k A h e
  case h_12 => exact arm2_block_index s0 s0' k A h e
  case h_13 => exact arm2_block_timestamp s0 s0' k A h e
  case h_14 => exact arm2_epoch_height s0 s0' k A h e
  case h_15 => exact arm2_storage_usage s0 s0' k A h e
  case h_16 => exact arm2_prepaid_gas s0 s0' k A h e
  case h_17 => exact arm2_used_gas s0 s0' k A h e
  case h_18 => exact arm2_account_balance s0 s0' k A h e
  case h_19 => exact arm2_account_locked_balance s0 s0' k A h e
  case h_20 => exact arm2_attached_deposit s0 s0' k A h e
  case h_21 => exact arm2_current_contract_code s0 s0' k A h e
  case h_22 => exact arm2_validator_stake s0 s0' k A h e
  case h_23 => exact arm2_validator_total_stake s0 s0' k A h e
  case h_24 => exact arm2_sha256 s0 s0' k A h e
  case h_25 => exact arm2_keccak256 s0 s0' k A h e
  case h_26 => exact arm2_keccak512 s0 s0' k A h e
  case h_27 => exact arm2_ripemd160 s0 s0' k A h e
  case h_28 => exact arm2_value_return s0 s0' k A h e
  case h_29 => exact arm2_panic s0 s0' k A h e
  case h_30 => exact arm2_panic_utf8 s0 s0' k A h e
  case h_31 => exact arm2_log_utf8 s0 s0' k A h e
  case h_32 => exact arm2_log_utf16 s0 s0' k A h e
  case h_33 => exact arm2_abort s0 s0' k A h e
  case h_34 => exact arm2_gas s0 s0' k A h e
  case h_35 => exact arm2_storage_write s0 s0' k A h e
  case h_36 => exact arm2_storage_read s0 s0' k A h e
  case h_37 => exact arm2_storage_remove s0 s0' k A h e
  case h_38 => exact arm2_storage_has_key s0 s0' k A h e
  case h_39 => exact arm2_storage_iter_prefix s0 s0' k A h e
  case h_40 => exact arm2_storage_iter_range s0 s0' k A h e
  case h_41 => exact arm2_storage_iter_next s0 s0' k A h e
  case h_42 => exact arm2_promise_batch_create s0 s0' k A h e
  case h_43 => exact arm2_promise_batch_then s0 s0' k A h e
  case h_44 => exact arm2_promise_and s0 s0' k A h e
  case h_45 => exact arm2_promise_create s0 s0' k A h e
  case h_46 => exact arm2_promise_then s0 s0' k A h e
  case h_47 => exact arm2_promise_set_refund_to s0 s0' k A h e
  case h_48 => exact arm2_promise_batch_action_create_account s0 s0' k A h e
  case h_49 => exact arm2_promise_batch_action_deploy_contract s0 s0' k A h e
  case h_50 => exact arm2_promise_batch_action_function_call s0 s0' k A h e
  case h_51 => exact arm2_promise_batch_action_function_call_weight s0 s0' k A h e
  case h_52 => exact arm2_promise_batch_action_transfer s0 s0' k A h e
  case h_53 => exact arm2_promise_batch_action_stake s0 s0' k A h e
  case h_54 => exact arm2_promise_batch_action_add_key_with_full_access s0 s0' k A h e
  case h_55 => exact arm2_promise_batch_action_add_key_with_function_call s0 s0' k A h e
  case h_56 => exact arm2_promise_batch_action_delete_key s0 s0' k A h e
  case h_57 => exact arm2_promise_batch_action_delete_account s0 s0' k A h e
  case h_58 => exact arm2_promise_results_count s0 s0' k A h e
  case h_59 => exact arm2_promise_result s0 s0' k A h e
  case h_60 => exact arm2_promise_return s0 s0' k A h e
  case h_61 => exact arm2_promise_yield_create s0 s0' k A h e
  case h_62 => exact arm2_promise_yield_resume s0 s0' k A h e
  case h_63 => exact arm2_ed25519_verify s0 s0' k A h e
  case h_64 => exact arm2_promise_yield_create_with_id s0 s0' k A h e
  case h_65 => exact arm2_promise_batch_action_transfer_to_gas_key s0 s0' k A h e
  case h_66 => exact arm2_promise_batch_action_add_gas_key_with_full_access s0 s0' k A h e
  case h_67 => exact arm2_promise_batch_action_add_gas_key_with_function_call s0 s0' k A h e
  case h_68 => exact arm2_promise_yield_resume_with_yield_id s0 s0' k A h e
  case h_69 => exact arm2_promise_batch_action_deploy_global_contract s0 s0' k A h e
  case h_70 => exact arm2_promise_batch_action_deploy_global_contract_by_account_id s0 s0' k A h e
  case h_71 => exact arm2_promise_batch_action_use_global_contract s0 s0' k A h e
  case h_72 => exact arm2_promise_batch_action_use_global_contract_by_account_id s0 s0' k A h e
  case h_73 => exact arm2_promise_batch_action_state_init s0 s0' k A h e
  case h_74 => exact arm2_promise_batch_action_state_init_by_account_id s0 s0' k A h e
  case h_75 => exact arm2_set_state_init_data_entry s0 s0' k A h e
  all_goals cases e

/-! ## 2. The read set only looks at the stack and the page count -/

theorem popsF_fst_congr : ∀ (j : Nat) (s t : St) (out : Array Nat), s.stack = t.stack →
    (popsF j s out).1 = (popsF j t out).1
  | 0, _, _, _, _ => rfl
  | j + 1, s, t, out, h => by
    simp only [popsF, popN_eq, h]
    exact popsF_fst_congr j _ _ _ (by simp [h])

theorem argN_congr {s t : St} (h : s.stack = t.stack) (n : Nat) : argN n s = argN n t := by
  funext i; simp only [argN, popsF_fst_congr n s t #[] h]

theorem readSetOf_congr (name : String) {s t : St} (h : s.stack = t.stack) (hp : s.pages.size = t.pages.size) :
    readSetOf name s = readSetOf name t := by
  have hm : memBytes s = memBytes t := by simp [memBytes, hp]
  have hr : reads name s = reads name t := by
    unfold reads; split <;> simp only [argN_congr h]
  unfold readSetOf
  rw [hr]
  generalize reads name t = l
  funext b
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [rdSet, ih]
    cases e <;> simp only [rdIn, hm]

/-! ## 3. Effects -/

/-- **A host call's effect** on a state: the top `k` stack entries replaced by `top`, the byte
writes `writes` applied in order, the host part (every non-Wasm field, registers and the whole gas
record included) replaced by `host`'s. -/
structure HostEff where
  k : Nat
  top : Array Val
  writes : List (Nat × ByteArray)
  host : St

def HostEff.apply (e : HostEff) (s : St) : St :=
  { e.host with stack := base e.k s ++ e.top, frames := s.frames, pages := wbAll e.writes s.pages,
                globals := s.globals, table := s.table, tableMax := s.tableMax, elems := s.elems,
                datas := s.datas, stackRem := s.stackRem }

theorem st_eq_of_visW {x y : St} (hv : visW x = visW y) (hr : hostR x = hostR y) : x = y := by
  apply st_eq_of_parts
  · simp only [visW, Prod.mk.injEq] at hv
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hv
    simp only [vis, h1, h2, h3, h4, h5, h6, h7, h8, h9, congrArg St.registers hr]
    exact congrArg St.registers hr ▸ rfl
  · exact congrArg (fun z : St => { z with registers := #[] }) hr

theorem hostR_apply (e : HostEff) (s : St) : hostR (e.apply s) = hostR e.host := rfl

/-- **Twinned states are one effect applied to the two start states.** -/
theorem eff_of_tw {s0 s0' : St} {k : Nat} {A : Nat → Prop} {x x' : St} (h : Tw s0 s0' k A x x') :
    ∃ e : HostEff, e.k = k ∧ x = e.apply s0 ∧ x' = e.apply s0' := by
  obtain ⟨hh, -, top, W, h1, h2⟩ := h
  refine ⟨⟨k, top, W, x⟩, rfl, st_eq_of_visW ?_ rfl, st_eq_of_visW ?_ hh.symm⟩
  · simp only [visW, HostEff.apply, h1.stack, h1.pages, h1.frames, h1.globals, h1.table, h1.tableMax, h1.elems,
      h1.datas, h1.stackRem]
  · simp only [visW, HostEff.apply, h2.stack, h2.pages, h2.frames, h2.globals, h2.table, h2.tableMax, h2.elems,
      h2.datas, h2.stackRem]

/-- An effect gives equal host sides (`sideR`) and gas registers. -/
theorem sideR_apply (e : HostEff) (s s' : St) : sideR (e.apply s) = sideR (e.apply s') := rfl
theorem g_apply (e : HostEff) (s s' : St) : (e.apply s).gas.g = (e.apply s').gas.g := rfl

/-! ## 4. `callHost` -/

/-- **Corresponding host-call results** (relative to the start pair). -/
def CallCorr (s0 s0' : St) (k : Nat) (A : Nat → Prop) : Res → Res → Prop
  | .cont x, .cont x' => Tw s0 s0' k A x x'
  | .abort x e, .abort x' e' => e = e' ∧ Tw s0 s0' k A x x'
  | .unmodeled w, .unmodeled w' => w = w'
  | _, _ => False

/-- `VisAt` only looks at the start state's visible part. -/
theorem visAt_base {s0 s1 : St} (hv : visW s1 = visW s0) {k : Nat} {top : Array Val}
    {W : List (Nat × ByteArray)} {x : St} (h : VisAt s1 k top W x) : VisAt s0 k top W x := by
  simp only [visW, Prod.mk.injEq] at hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.stack]; simp only [base, h1]
  · rw [h.pages, h2]
  · rw [h.frames, h3]
  · rw [h.globals, h4]
  · rw [h.table, h5]
  · rw [h.tableMax, h6]
  · rw [h.elems, h7]
  · rw [h.datas, h8]
  · rw [h.stackRem, h9]

theorem tw_base {s0 s0' s1 s1' : St} (hv : visW s1 = visW s0) (hv' : visW s1' = visW s0') {k : Nat}
    {A : Nat → Prop} {x x' : St} (h : Tw s1 s1' k A x x') : Tw s0 s0' k A x x' := by
  obtain ⟨hh, hA, top, W, h1, h2⟩ := h
  exact ⟨hh, hA, top, W, visAt_base hv h1, visAt_base hv' h2⟩

/-- A gas-only change of a low-equivalent pair keeps it low-equivalent. -/
theorem low_gas {A : Nat → Prop} {k : Nat} {s s' : St} (h : Low A k s s') (g : Gas) :
    Low A k { s with gas := g } { s' with gas := g } := by
  refine ⟨?_, h.kle, h.kle', h.top, agree_congr h.mem rfl rfl⟩
  obtain ⟨-, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, -⟩ := Tw.eqs (tw_start h)
  simp only [hostR, hostSide, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]

theorem sync_congr {s s' : St} (hg : s'.gas = s.gas) :
    (∀ s1, sync s = .ok s1 → sync s' = .ok { s' with gas := s1.gas } ∧ s1 = { s with gas := s1.gas }) ∧
    (∀ e, sync s = .error e → sync s' = .error e) := by
  unfold sync; rw [hg]
  refine ⟨fun s1 h => ?_, fun e h => ?_⟩
  · dsimp only at h ⊢
    split at h
    · cases h; rw [if_pos ‹_›]; exact ⟨by rw [← hg], rfl⟩
    · rw [if_neg ‹_›]; split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h
  · dsimp only at h ⊢
    split at h
    · cases h
    · rw [if_neg ‹_›]; split at h
      · cases h
      · cases h; rfl

/-- **`callHost_two_run`: a host call cannot tell low-equivalent states apart.**  For an arm of
`hostCall`, from `Low A k s s'` with `A` covering the arm's read set at `s` and `k ≥ nargs name`, the
two calls give corresponding results (`CallCorr`). -/
theorem callHost_two_run {name : String} {s s' : St} {k : Nat} {A : Nat → Prop}
    (hL : Low A k s s') (hn : (hostCall name).isSome) (hk : nargs name ≤ k)
    (hA : ∀ b, readSetOf name s b → A b) :
    CallCorr s s' k A (callHost s name) (callHost s' name) := by
  have eqs := Tw.eqs (tw_start hL)
  obtain ⟨eg, -, -, -, -, -, -, -, -, -, -, -, -, ereal, -, eglob, ecurve, -⟩ := eqs
  unfold callHost
  rw [ereal, eglob]
  split
  · rfl
  obtain ⟨sc1, sc2⟩ := sync_congr eg
  cases hs : sync s with
  | error e => rw [sc2 e hs]; exact (rfl : e = e)
  | ok s1 =>
    rw [(sc1 s1 hs).1]
    have hs1 : s1 = { s with gas := s1.gas } := (sc1 s1 hs).2
    dsimp only
    have hL1 : Low A k s1 { s' with gas := s1.gas } := by rw [hs1]; exact low_gas hL _
    have hd : dispatchArm { s' with gas := s1.gas } name = dispatchArm s1 name := by
      unfold dispatchArm; rw [hs1]; simp only [ecurve]
    rw [hd]
    obtain ⟨h, eh⟩ := Option.isSome_iff_exists.mp hn
    have hd1 : dispatchArm s1 name = some h := by unfold dispatchArm; rw [eh]
    rw [hd1]
    dsimp only
    have hA1 : ∀ b, readSetOf name s1 b → A b := by
      rw [hs1, readSetOf_congr name (s := { s with gas := s1.gas }) (t := s) rfl rfl]; exact hA
    have hrc := armTwo_all name s1 { s' with gas := s1.gas } k A h eh hL1 hk hA1
    have hv : visW s1 = visW s := by rw [hs1]; rfl
    have hv' : visW ({ s' with gas := s1.gas } : St) = visW s' := rfl
    simp only [EStateM.run]
    revert hrc
    cases h s1 with
    | ok a x =>
      cases h { s' with gas := s1.gas } with
      | ok b x' =>
        rintro ⟨-, -, ht⟩
        have ht' := tw_base hv hv' ht
        obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, -⟩ := Tw.eqs ht'
        refine tw_of ht' rfl rfl ?_
        simp only [hostR, hostSide, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]
      | error e x' => intro h; exact h.elim
    | error e x =>
      cases h { s' with gas := s1.gas } with
      | ok b x' => intro h; exact h.elim
      | error e' x' =>
        rintro ⟨rfl, ht⟩
        by_cases hu : e.startsWith "unmodeled" = true
        · simp only [hu, ite_true]; exact (rfl : e = e)
        · simp only [hu]; exact ⟨rfl, tw_base hv hv' ht⟩

/-- **`callHost_two_run`, effect form.**  A continuing call from `s` continues from `s'`, and the two
post-states are one `HostEff` applied to `s` and `s'`: the same values popped and pushed (on the
shared top `k`), the same bytes written, the same new host side (`sideR`) and gas register; frames,
globals, the stack below the top `k` and all unwritten bytes are each side's own. -/
theorem callHost_two_run_cont {name : String} {s s' : St} {k : Nat} {A : Nat → Prop}
    (hL : Low A k s s') (hn : (hostCall name).isSome) (hk : nargs name ≤ k)
    (hA : ∀ b, readSetOf name s b → A b) {x : St} (hx : callHost s name = .cont x) :
    ∃ (x' : St) (eff : HostEff), callHost s' name = .cont x' ∧ eff.k = k ∧ x = eff.apply s ∧
      x' = eff.apply s' ∧ sideR x = sideR x' ∧ x.gas.g = x'.gas.g := by
  have h := callHost_two_run hL hn hk hA
  rw [hx] at h
  revert h
  cases callHost s' name with
  | cont x' =>
    intro h
    obtain ⟨eff, hk', e1, e2⟩ := eff_of_tw h
    exact ⟨x', eff, rfl, hk', e1, e2, by rw [e1, e2]; rfl, by rw [e1, e2]; rfl⟩
  | _ => intro h; exact h.elim

/-- **`callHost_two_run`, abort form.** -/
theorem callHost_two_run_abort {name : String} {s s' : St} {k : Nat} {A : Nat → Prop}
    (hL : Low A k s s') (hn : (hostCall name).isSome) (hk : nargs name ≤ k)
    (hA : ∀ b, readSetOf name s b → A b) {x : St} {err : String} (hx : callHost s name = .abort x err) :
    ∃ (x' : St) (eff : HostEff), callHost s' name = .abort x' err ∧ eff.k = k ∧ x = eff.apply s ∧
      x' = eff.apply s' := by
  have h := callHost_two_run hL hn hk hA
  rw [hx] at h
  revert h
  cases callHost s' name with
  | abort x' e' =>
    rintro ⟨rfl, h⟩
    obtain ⟨eff, hk', e1, e2⟩ := eff_of_tw h
    exact ⟨x', eff, rfl, hk', e1, e2⟩
  | _ => intro h; exact h.elim

#print axioms armTwo_all
#print axioms callHost_two_run
#print axioms callHost_two_run_cont
#print axioms callHost_two_run_abort

end TwoRun
end WasmBase
