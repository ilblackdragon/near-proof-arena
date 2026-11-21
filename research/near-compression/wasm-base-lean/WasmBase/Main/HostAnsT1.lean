import WasmBase.Main.HostAns2
import WasmBase.Main.HostIfTape

namespace WasmBase
namespace HostAns

open NearSpecV3.Wasm
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 50000
set_option maxRecDepth 100000

/-! ## 1. The answer function of T1's host set -/

/-- **An answer function with a host-side update, per host name** (the `HostAnsF` shape plus the
update of the fields `HAns` does not carry). -/
structure HostAnsU where
  ans : String → St → List Nat → (Nat → UInt8) → Nat → HAns
  upd : String → St → List Nat → (Nat → UInt8) → Nat → St → St

/-- T1's host functions (corpus case `d3/02-h10196-s3`, contract `d3tiny`, method `run`). -/
def t1Hosts : List String :=
  ["input", "register_len", "read_register", "storage_write", "log_utf8", "value_return"]

/-- The arity of each T1 host function. -/
def nargsT1 (name : String) : Nat :=
  match name with
  | "input" => 1 | "register_len" => 1 | "read_register" => 2 | "storage_write" => 5
  | "log_utf8" => 2 | "value_return" => 2 | _ => 0

/-- **The answers of T1's six host functions** (`ansKnown`'s three plus `storage_write`, `log_utf8`,
`value_return`); arguments in popped order. -/
def ansT1 (name : String) (σ : St) (args : List Nat) (mem : Nat → UInt8) (memSz : Nat) : HAns :=
  if name = "register_len" then ansRegisterLen σ (args.getD 0 0)
  else if name = "input" then ansInput σ (args.getD 0 0)
  else if name = "read_register" then ansReadRegister σ (args.getD 0 0) (args.getD 1 0) memSz
  else if name = "storage_write" then
    ansStorageWrite σ (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0) (args.getD 4 0) mem memSz
  else if name = "log_utf8" then ansLogUtf8 σ (args.getD 0 0) (args.getD 1 0) mem memSz
  else if name = "value_return" then ansValueReturn σ (args.getD 0 0) (args.getD 1 0) mem memSz
  else ⟨some "unmodeled", [], σ.gas, σ.registers, σ.regUsage, []⟩

/-- **Their host-side updates** (identity for the three register/memory functions). -/
def updT1 (name : String) (σ : St) (args : List Nat) (mem : Nat → UInt8) (memSz : Nat) : St → St :=
  if name = "storage_write" then
    updStorageWrite σ (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0) (args.getD 4 0) mem memSz
  else if name = "log_utf8" then updLogUtf8 σ (args.getD 0 0) (args.getD 1 0) mem memSz
  else if name = "value_return" then updValueReturn σ (args.getD 0 0) (args.getD 1 0) mem memSz
  else id

def ansT1U : HostAnsU := ⟨ansT1, updT1⟩

theorem vec_getD {n : Nat} (v : Vector Nat n) (i : Nat) (h : i < n) : v.toList.getD i 0 = v[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## 2. The arm is the answer, for every T1 host (post-pop form) -/

section Eqs
variable (σ : St) (args : List Nat) (mem : Nat → UInt8) (memSz : Nat)
theorem ansT1_register_len : ansT1 "register_len" σ args mem memSz = ansRegisterLen σ (args.getD 0 0) := by
  rw [ansT1, if_pos rfl]
theorem ansT1_input : ansT1 "input" σ args mem memSz = ansInput σ (args.getD 0 0) := by
  rw [ansT1, if_neg (by decide), if_pos rfl]
theorem ansT1_read_register :
    ansT1 "read_register" σ args mem memSz = ansReadRegister σ (args.getD 0 0) (args.getD 1 0) memSz := by
  rw [ansT1, if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem ansT1_storage_write : ansT1 "storage_write" σ args mem memSz =
    ansStorageWrite σ (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0) (args.getD 4 0) mem memSz := by
  rw [ansT1, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem ansT1_log_utf8 : ansT1 "log_utf8" σ args mem memSz = ansLogUtf8 σ (args.getD 0 0) (args.getD 1 0) mem memSz := by
  rw [ansT1, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem ansT1_value_return :
    ansT1 "value_return" σ args mem memSz = ansValueReturn σ (args.getD 0 0) (args.getD 1 0) mem memSz := by
  rw [ansT1, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos rfl]
theorem updT1_input : updT1 "input" σ args mem memSz = id := by
  rw [updT1, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
theorem updT1_register_len : updT1 "register_len" σ args mem memSz = id := by
  rw [updT1, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
theorem updT1_read_register : updT1 "read_register" σ args mem memSz = id := by
  rw [updT1, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
theorem updT1_storage_write : updT1 "storage_write" σ args mem memSz =
    updStorageWrite σ (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0) (args.getD 4 0) mem memSz := by
  rw [updT1, if_pos rfl]
theorem updT1_log_utf8 : updT1 "log_utf8" σ args mem memSz = updLogUtf8 σ (args.getD 0 0) (args.getD 1 0) mem memSz := by
  rw [updT1, if_neg (by decide), if_pos rfl]
theorem updT1_value_return :
    updT1 "value_return" σ args mem memSz = updValueReturn σ (args.getD 0 0) (args.getD 1 0) mem memSz := by
  rw [updT1, if_neg (by decide), if_neg (by decide), if_pos rfl]
end Eqs

/-- **Every T1 host's arm is its answer** (`ansT1`, `updT1`) from the post-pop state, every branch. -/
theorem ansT1_arm {name : String} (hm : name ∈ t1Hosts) {s s0 : St} {args : Vector Nat (nargsT1 name)}
    (e0 : (popArgs (nargsT1 name)).run s = .ok args s0) :
    (hostCall name).get!.run s =
      runOfU s0 (ansT1 name s0 args.toList (readByte s0) (memBytes s0))
        (updT1 name s0 args.toList (readByte s0) (memBytes s0)) := by
  simp only [t1Hosts, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · -- input
    have e1 : (popArgs 1).run s = .ok args s0 := e0
    rw [popArgs1_run] at e1
    injection e1 with ea es
    subst es
    rw [ansT1_input, updT1_input, runOfU_id, vec_getD args 0 (by decide), ← ea]
    exact input_ans s
  · -- register_len
    have e1 : (popArgs 1).run s = .ok args s0 := e0
    rw [popArgs1_run] at e1
    injection e1 with ea es
    subst es
    rw [ansT1_register_len, updT1_register_len, runOfU_id, vec_getD args 0 (by decide), ← ea]
    exact register_len_ans s
  · -- read_register
    have e1 : (popArgs 2).run s = .ok args s0 := e0
    rw [ansT1_read_register, updT1_read_register, runOfU_id, vec_getD args 0 (by decide),
      vec_getD args 1 (by decide)]
    exact read_register_ans e1
  · -- storage_write
    have e1 : (popArgs 5).run s = .ok args s0 := e0
    rw [ansT1_storage_write, updT1_storage_write, vec_getD args 0 (by decide), vec_getD args 1 (by decide),
      vec_getD args 2 (by decide), vec_getD args 3 (by decide), vec_getD args 4 (by decide)]
    exact storage_write_ans e1
  · -- log_utf8
    have e1 : (popArgs 2).run s = .ok args s0 := e0
    rw [ansT1_log_utf8, updT1_log_utf8, vec_getD args 0 (by decide), vec_getD args 1 (by decide)]
    exact log_utf8_ans e1
  · -- value_return
    have e1 : (popArgs 2).run s = .ok args s0 := e0
    rw [ansT1_value_return, updT1_value_return, vec_getD args 0 (by decide), vec_getD args 1 (by decide)]
    exact value_return_ans e1


#print axioms ansT1_arm

end HostAns
end WasmBase
