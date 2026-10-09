import NearSpecV3.Logged.WasmCRHost
import NearSpecV3.Logged.WasmStep

/-! # Every non-storage host function leaves the trie store alone (`CR_hostCall`)

One case per `hostCall` arm (via its equation lemmas); generated. -/

namespace NearSpecV3.Logged.W

open NearSpecV3.Wasm

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem CR_hostCall (σ : TTN.Store) (name : String) (h : HM Unit) (hh : hostCall name = some h)
    (hn : storageHosts.contains name = false) : CR σ h h := by
  by_cases h1 : name = "read_register"
  · subst h1; rw [hostCall.eq_1] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h2 : name = "register_len"
  · subst h2; rw [hostCall.eq_2] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h3 : name = "write_register"
  · subst h3; rw [hostCall.eq_3] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h4 : name = "current_account_id"
  · subst h4; rw [hostCall.eq_4] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h5 : name = "signer_account_id"
  · subst h5; rw [hostCall.eq_5] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h6 : name = "signer_account_pk"
  · subst h6; rw [hostCall.eq_6] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h7 : name = "predecessor_account_id"
  · subst h7; rw [hostCall.eq_7] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h8 : name = "refund_to_account_id"
  · subst h8; rw [hostCall.eq_8] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h9 : name = "chain_id"
  · subst h9; rw [hostCall.eq_9] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h10 : name = "input"
  · subst h10; rw [hostCall.eq_10] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h11 : name = "random_seed"
  · subst h11; rw [hostCall.eq_11] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h12 : name = "block_index"
  · subst h12; rw [hostCall.eq_12] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h13 : name = "block_timestamp"
  · subst h13; rw [hostCall.eq_13] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h14 : name = "epoch_height"
  · subst h14; rw [hostCall.eq_14] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h15 : name = "storage_usage"
  · subst h15; rw [hostCall.eq_15] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h16 : name = "prepaid_gas"
  · subst h16; rw [hostCall.eq_16] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h17 : name = "used_gas"
  · subst h17; rw [hostCall.eq_17] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h18 : name = "account_balance"
  · subst h18; rw [hostCall.eq_18] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h19 : name = "account_locked_balance"
  · subst h19; rw [hostCall.eq_19] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h20 : name = "attached_deposit"
  · subst h20; rw [hostCall.eq_20] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h21 : name = "current_contract_code"
  · subst h21; rw [hostCall.eq_21] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h22 : name = "validator_stake"
  · subst h22; rw [hostCall.eq_22] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h23 : name = "validator_total_stake"
  · subst h23; rw [hostCall.eq_23] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h24 : name = "sha256"
  · subst h24; rw [hostCall.eq_24] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h25 : name = "keccak256"
  · subst h25; rw [hostCall.eq_25] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h26 : name = "keccak512"
  · subst h26; rw [hostCall.eq_26] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h27 : name = "ripemd160"
  · subst h27; rw [hostCall.eq_27] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h28 : name = "value_return"
  · subst h28; rw [hostCall.eq_28] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h29 : name = "panic"
  · subst h29; rw [hostCall.eq_29] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h30 : name = "panic_utf8"
  · subst h30; rw [hostCall.eq_30] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h31 : name = "log_utf8"
  · subst h31; rw [hostCall.eq_31] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h32 : name = "log_utf16"
  · subst h32; rw [hostCall.eq_32] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h33 : name = "abort"
  · subst h33; rw [hostCall.eq_33] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h34 : name = "gas"
  · subst h34; rw [hostCall.eq_34] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h35 : name = "storage_write"
  · subst h35; exact absurd hn (by decide)
  by_cases h36 : name = "storage_read"
  · subst h36; exact absurd hn (by decide)
  by_cases h37 : name = "storage_remove"
  · subst h37; exact absurd hn (by decide)
  by_cases h38 : name = "storage_has_key"
  · subst h38; exact absurd hn (by decide)
  by_cases h39 : name = "storage_iter_prefix"
  · subst h39; rw [hostCall.eq_39] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h40 : name = "storage_iter_range"
  · subst h40; rw [hostCall.eq_40] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h41 : name = "storage_iter_next"
  · subst h41; rw [hostCall.eq_41] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h42 : name = "promise_batch_create"
  · subst h42; rw [hostCall.eq_42] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h43 : name = "promise_batch_then"
  · subst h43; rw [hostCall.eq_43] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h44 : name = "promise_and"
  · subst h44; rw [hostCall.eq_44] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h45 : name = "promise_create"
  · subst h45; rw [hostCall.eq_45] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h46 : name = "promise_then"
  · subst h46; rw [hostCall.eq_46] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h47 : name = "promise_set_refund_to"
  · subst h47; rw [hostCall.eq_47] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h48 : name = "promise_batch_action_create_account"
  · subst h48; rw [hostCall.eq_48] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h49 : name = "promise_batch_action_deploy_contract"
  · subst h49; rw [hostCall.eq_49] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h50 : name = "promise_batch_action_function_call"
  · subst h50; rw [hostCall.eq_50] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h51 : name = "promise_batch_action_function_call_weight"
  · subst h51; rw [hostCall.eq_51] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h52 : name = "promise_batch_action_transfer"
  · subst h52; rw [hostCall.eq_52] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h53 : name = "promise_batch_action_stake"
  · subst h53; rw [hostCall.eq_53] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h54 : name = "promise_batch_action_add_key_with_full_access"
  · subst h54; rw [hostCall.eq_54] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h55 : name = "promise_batch_action_add_key_with_function_call"
  · subst h55; rw [hostCall.eq_55] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h56 : name = "promise_batch_action_delete_key"
  · subst h56; rw [hostCall.eq_56] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h57 : name = "promise_batch_action_delete_account"
  · subst h57; rw [hostCall.eq_57] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h58 : name = "promise_results_count"
  · subst h58; rw [hostCall.eq_58] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h59 : name = "promise_result"
  · subst h59; rw [hostCall.eq_59] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h60 : name = "promise_return"
  · subst h60; rw [hostCall.eq_60] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h61 : name = "promise_yield_create"
  · subst h61; rw [hostCall.eq_61] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h62 : name = "promise_yield_resume"
  · subst h62; exact absurd hn (by decide)
  by_cases h63 : name = "ed25519_verify"
  · subst h63; rw [hostCall.eq_63] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h64 : name = "promise_yield_create_with_id"
  · subst h64; exact absurd hn (by decide)
  by_cases h65 : name = "promise_batch_action_transfer_to_gas_key"
  · subst h65; rw [hostCall.eq_65] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h66 : name = "promise_batch_action_add_gas_key_with_full_access"
  · subst h66; rw [hostCall.eq_66] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h67 : name = "promise_batch_action_add_gas_key_with_function_call"
  · subst h67; rw [hostCall.eq_67] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h68 : name = "promise_yield_resume_with_yield_id"
  · subst h68; exact absurd hn (by decide)
  by_cases h69 : name = "promise_batch_action_deploy_global_contract"
  · subst h69; rw [hostCall.eq_69] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h70 : name = "promise_batch_action_deploy_global_contract_by_account_id"
  · subst h70; rw [hostCall.eq_70] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h71 : name = "promise_batch_action_use_global_contract"
  · subst h71; rw [hostCall.eq_71] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h72 : name = "promise_batch_action_use_global_contract_by_account_id"
  · subst h72; rw [hostCall.eq_72] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h73 : name = "promise_batch_action_state_init"
  · subst h73; rw [hostCall.eq_73] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h74 : name = "promise_batch_action_state_init_by_account_id"
  · subst h74; rw [hostCall.eq_74] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  by_cases h75 : name = "set_state_init_data_entry"
  · subst h75; rw [hostCall.eq_75] at hh; have hh2 := Option.some.inj hh; clear hh; subst hh2; cr
  rw [hostCall.eq_76 name h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73 h74 h75] at hh; cases hh

end NearSpecV3.Logged.W
