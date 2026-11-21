import WasmBase.Main.HostAns2
import WasmBase.Main.HostIfTape
import WasmBase.Main.HostTwoRunArms

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



/-! ## 3. The answers read only the host side (field congruence) -/

/-- The host fields T1's answers read. -/
structure HostFieldsEq (σ σ' : St) : Prop where
  gas : σ.gas = σ'.gas
  registers : σ.registers = σ'.registers
  regUsage : σ.regUsage = σ'.regUsage
  ctx : σ.ctx = σ'.ctx
  logs : σ.logs = σ'.logs
  totalLogLen : σ.totalLogLen = σ'.totalLogLen
  trie : σ.trie = σ'.trie
  real : σ.real = σ'.real
  storageUsage : σ.storageUsage = σ'.storageUsage

theorem hostFieldsEq_stack (σ : St) (x : Array Val) : HostFieldsEq { σ with stack := x } σ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hostFieldsEq_of_hostR {σ σ' : St} (h : TwoRun.hostR σ = TwoRun.hostR σ') : HostFieldsEq σ σ' :=
  have e : ∀ {β : Type} (f : St → β), f (TwoRun.hostR σ) = f (TwoRun.hostR σ') := fun f => congrArg f h
  ⟨e St.gas, e St.registers, e St.regUsage, e St.ctx, e St.logs, e St.totalLogLen, e St.trie, e St.real,
    e St.storageUsage⟩

section Congr
variable {σ σ' : St} (h : HostFieldsEq σ σ')
include h

theorem regSetAns_congrH (g : Gas) (id : Nat) (d : ByteArray) : regSetAns σ g id d = regSetAns σ' g id d :=
  regSetAns_congr g id d h.registers h.regUsage

theorem ansRegisterLen_congr (id : Nat) : ansRegisterLen σ id = ansRegisterLen σ' id := by
  unfold ansRegisterLen regLen; simp only [h.gas, h.registers, h.regUsage]

theorem ansInputG_congr (p1 p2 : Gas × Option String) (id : Nat) : ansInputG σ p1 p2 id = ansInputG σ' p1 p2 id := by
  unfold ansInputG; simp only [regSetAns_congrH h, h.registers, h.regUsage, h.ctx]

theorem ansInput_congr (id : Nat) : ansInput σ id = ansInput σ' id := by
  unfold ansInput; simp only [ansInputG_congr h, h.gas]

theorem ansReadRegisterG_congr (id ptr memSz : Nat) (dr : Option ByteArray) (p1 pr1 pr2 pw1 pw2 : Gas × Option String) :
    ansReadRegisterG σ id ptr memSz dr p1 pr1 pr2 pw1 pw2 = ansReadRegisterG σ' id ptr memSz dr p1 pr1 pr2 pw1 pw2 := by
  unfold ansReadRegisterG errA; simp only [h.registers, h.regUsage]

theorem ansReadRegister_congr (id ptr memSz : Nat) : ansReadRegister σ id ptr memSz = ansReadRegister σ' id ptr memSz := by
  unfold ansReadRegister; simp only [ansReadRegisterG_congr h, h.registers, h.gas]

theorem resAns_congr {α} (r : EStateM.Result String Gas α) (f : α → List Nat) : resAns σ r f = resAns σ' r f := by
  unfold resAns; simp only [h.registers, h.regUsage]

theorem vrG_congr (mem : Nat → UInt8) (memSz ptr len : Nat) : vrG σ mem memSz ptr len = vrG σ' mem memSz ptr len := by
  unfold vrG vrBurn; simp only [h.registers, h.ctx]

theorem ansValueReturn_congr (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    ansValueReturn σ len ptr mem memSz = ansValueReturn σ' len ptr mem memSz := by
  unfold ansValueReturn; simp only [vrG_congr h, resAns_congr h, h.gas]

theorem updValueReturn_congr (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    updValueReturn σ len ptr mem memSz = updValueReturn σ' len ptr mem memSz := by
  unfold updValueReturn; simp only [vrG_congr h, h.gas]

theorem lgG_congr (mem : Nat → UInt8) (memSz len ptr : Nat) : lgG σ mem memSz len ptr = lgG σ' mem memSz len ptr := by
  unfold lgG; simp only [h.logs, h.totalLogLen]

theorem lgAnsOf_congr (r : EStateM.Result String Gas String) : lgAnsOf σ r = lgAnsOf σ' r := by
  unfold lgAnsOf; simp only [h.totalLogLen, h.registers, h.regUsage]

theorem lgUpdOf_congr (r : EStateM.Result String Gas String) : lgUpdOf σ r = lgUpdOf σ' r := by
  unfold lgUpdOf; simp only [h.totalLogLen]

theorem ansLogUtf8_congr (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    ansLogUtf8 σ len ptr mem memSz = ansLogUtf8 σ' len ptr mem memSz := by
  unfold ansLogUtf8; simp only [lgG_congr h, lgAnsOf_congr h, h.gas]

theorem updLogUtf8_congr (len ptr : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    updLogUtf8 σ len ptr mem memSz = updLogUtf8 σ' len ptr mem memSz := by
  unfold updLogUtf8; simp only [lgG_congr h, lgUpdOf_congr h, h.gas]

theorem swG_congr (mem : Nat → UInt8) (memSz klen kptr vlen vptr : Nat) :
    swG σ mem memSz klen kptr vlen vptr = swG σ' mem memSz klen kptr vlen vptr := by
  unfold swG; simp only [h.registers]

theorem swOldSome_congr (T : Array (ByteArray × ByteArray)) (R : Option TTN.RealStore) (reg : Nat) (v o : ByteArray)
    (rr : EStateM.Result String Gas Unit) : swOldSome σ T R reg v o rr = swOldSome σ' T R reg v o rr := by
  cases rr with
  | error e g => unfold swOldSome; simp only [h.registers, h.regUsage, h.storageUsage]
  | ok x g => unfold swOldSome; simp only [regSetAns_congrH h, h.storageUsage]

theorem swOldR_congr (g : Gas) (T : Array (ByteArray × ByteArray)) (R : Option TTN.RealStore) (reg : Nat)
    (k v : ByteArray) (old : Option ByteArray) : swOldR σ g T R reg k v old = swOldR σ' g T R reg k v old := by
  cases old with
  | none => unfold swOldR; simp only [h.registers, h.regUsage, h.storageUsage]
  | some o => unfold swOldR; simp only [swOldSome_congr h]

theorem swBackR_congr (g : Gas) (reg : Nat) (k v : ByteArray) : swBackR σ g reg k v = swBackR σ' g reg k v := by
  unfold swBackR trieGet
  simp only [swOldR_congr h, h.real, h.trie, h.registers, h.regUsage, h.storageUsage]

theorem swAnsOf_congr (reg : Nat) (r : EStateM.Result String Gas (ByteArray × ByteArray)) :
    swAnsOf σ reg r = swAnsOf σ' reg r := by
  cases r with
  | error e g => unfold swAnsOf; simp only [h.registers, h.regUsage]
  | ok kv g => unfold swAnsOf; simp only [swBackR_congr h]

theorem swUpdOf_congr (reg : Nat) (r : EStateM.Result String Gas (ByteArray × ByteArray)) :
    swUpdOf σ reg r = swUpdOf σ' reg r := by
  cases r with
  | error e g => rfl
  | ok kv g => unfold swUpdOf; simp only [swBackR_congr h]

theorem ansStorageWrite_congr (klen kptr vlen vptr reg : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    ansStorageWrite σ klen kptr vlen vptr reg mem memSz = ansStorageWrite σ' klen kptr vlen vptr reg mem memSz := by
  unfold ansStorageWrite; simp only [swG_congr h, swAnsOf_congr h, h.gas]

theorem updStorageWrite_congr (klen kptr vlen vptr reg : Nat) (mem : Nat → UInt8) (memSz : Nat) :
    updStorageWrite σ klen kptr vlen vptr reg mem memSz = updStorageWrite σ' klen kptr vlen vptr reg mem memSz := by
  unfold updStorageWrite; simp only [swG_congr h, swUpdOf_congr h, h.gas]

/-- **`ansT1` / `updT1` read only the host fields** of the state. -/
theorem ansT1_congr (name : String) (args : List Nat) (mem : Nat → UInt8) (memSz : Nat) :
    ansT1 name σ args mem memSz = ansT1 name σ' args mem memSz ∧
      updT1 name σ args mem memSz = updT1 name σ' args mem memSz := by
  unfold ansT1 updT1
  rw [ansRegisterLen_congr h, ansInput_congr h, ansReadRegister_congr h, ansStorageWrite_congr h, ansLogUtf8_congr h,
    ansValueReturn_congr h, updStorageWrite_congr h, updLogUtf8_congr h, updValueReturn_congr h, h.gas, h.registers,
    h.regUsage]
  exact ⟨rfl, rfl⟩

end Congr


/-! ## 4. The answers read memory only on the arm's read set -/

/-- The memory reads of T1's arms, from the popped arguments (`TwoRun.reads`' descriptions:
`.mr ptr len` a `memOrRegH` read, `.u8 ptr len` the `utf8H` read incl. its NUL-terminated window). -/
def rdsT1 (name : String) (args : List Nat) : List TwoRun.Rd :=
  if name = "storage_write" then [.mr (args.getD 1 0) (args.getD 0 0), .mr (args.getD 3 0) (args.getD 2 0)]
  else if name = "log_utf8" then [.u8 (args.getD 1 0) (args.getD 0 0)]
  else if name = "value_return" then [.mr (args.getD 1 0) (args.getD 0 0)]
  else []

theorem bytesOf_congr {mem mem' : Nat → UInt8} {ptr len : Nat} (h : ∀ i, i < len → mem (ptr + i) = mem' (ptr + i)) :
    bytesOf mem ptr len = bytesOf mem' ptr len := by
  unfold bytesOf
  apply foldl_congr_mem
  intro i hi d
  simp only [List.mem_range'] at hi
  rw [h i (by omega)]

theorem memOrRegG_congr {σ0 : St} {mem mem' : Nat → UInt8} (regs : Array (Nat × ByteArray)) (memSz ptr len : Nat)
    (h : ∀ b, TwoRun.rdIn σ0 (.mr ptr len) b → mem b = mem' b) :
    memOrRegG regs mem memSz ptr len = memOrRegG regs mem' memSz ptr len := by
  unfold memOrRegG
  by_cases hl : len = u64Bound - 1
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl, bytesOf_congr (fun i hi => h _ ⟨hl, by omega, by omega⟩)]

theorem vrG_mem (σ : St) {mem mem' : Nat → UInt8} (memSz ptr len : Nat)
    (h : ∀ b, TwoRun.rdIn σ (.mr ptr len) b → mem b = mem' b) :
    vrG σ mem memSz ptr len = vrG σ mem' memSz ptr len := by
  unfold vrG; rw [memOrRegG_congr (σ0 := σ) _ _ _ _ h]

theorem swG_mem (σ : St) {mem mem' : Nat → UInt8} (memSz klen kptr vlen vptr : Nat)
    (h1 : ∀ b, TwoRun.rdIn σ (.mr kptr klen) b → mem b = mem' b)
    (h2 : ∀ b, TwoRun.rdIn σ (.mr vptr vlen) b → mem b = mem' b) :
    swG σ mem memSz klen kptr vlen vptr = swG σ mem' memSz klen kptr vlen vptr := by
  unfold swG; simp only [memOrRegG_congr (σ0 := σ) _ _ _ _ h1, memOrRegG_congr (σ0 := σ) _ _ _ _ h2]

theorem forIn_list_congr {α β : Type} (l : List α) (b : β) (f f' : α → β → GM (ForInStep β))
    (h : ∀ x ∈ l, f x = f' x) : forIn l b f = forIn l b f' := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    rw [List.forIn_cons, List.forIn_cons, h x List.mem_cons_self]
    congr 1; funext r
    cases r with
    | done c => rfl
    | yield c => exact ih c (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem utf8G_mem (σ : St) (tl : Nat) {mem mem' : Nat → UInt8} (memSz len ptr : Nat)
    (h : ∀ b, TwoRun.rdIn σ (.u8 ptr len) b → mem b = mem' b) :
    utf8G tl mem memSz len ptr = utf8G tl mem' memSz len ptr := by
  unfold utf8G
  by_cases hl : len ≠ u64Bound - 1
  · simp only [if_pos hl]
    rw [bytesOf_congr (fun i hi => h _ (Or.inl ⟨hl, by omega, by omega⟩))]
  · simp only [if_neg hl]
    have hl' : len = u64Bound - 1 := Classical.byContradiction hl
    rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range',
      forIn_list_congr _ _ _ _ (fun i hi => ?_)]
    simp only [List.mem_range'] at hi
    funext st
    unfold nulStepG
    rw [h (ptr + i) (Or.inr ⟨hl', by omega, by simp at hi; omega⟩)]

theorem lgG_mem (σ : St) {mem mem' : Nat → UInt8} (memSz len ptr : Nat)
    (h : ∀ b, TwoRun.rdIn σ (.u8 ptr len) b → mem b = mem' b) :
    lgG σ mem memSz len ptr = lgG σ mem' memSz len ptr := by
  unfold lgG; rw [utf8G_mem σ _ _ _ _ h]

/-- **`ansT1` / `updT1` read memory only on the arm's read set** (`rdsT1`), for every T1 host. -/
theorem ansT1_mem {name : String} (hm : name ∈ t1Hosts) (σ : St) (args : List Nat) {mem mem' : Nat → UInt8}
    (memSz : Nat) (h : ∀ b, TwoRun.rdSet σ (rdsT1 name args) b → mem b = mem' b) :
    ansT1 name σ args mem memSz = ansT1 name σ args mem' memSz ∧
      updT1 name σ args mem memSz = updT1 name σ args mem' memSz := by
  simp only [t1Hosts, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ansT1_input, ansT1_input, updT1_input, updT1_input]; exact ⟨rfl, rfl⟩
  · rw [ansT1_register_len, ansT1_register_len, updT1_register_len, updT1_register_len]; exact ⟨rfl, rfl⟩
  · rw [ansT1_read_register, ansT1_read_register, updT1_read_register, updT1_read_register]; exact ⟨rfl, rfl⟩
  · have e : rdsT1 "storage_write" args = [.mr (args.getD 1 0) (args.getD 0 0), .mr (args.getD 3 0) (args.getD 2 0)] := by
      rw [rdsT1, if_pos rfl]
    rw [e] at h
    rw [ansT1_storage_write, ansT1_storage_write, updT1_storage_write, updT1_storage_write]
    unfold ansStorageWrite updStorageWrite
    rw [swG_mem σ _ _ _ _ _ (fun b hb => h b (Or.inl hb)) (fun b hb => h b (Or.inr (Or.inl hb)))]
    exact ⟨rfl, rfl⟩
  · have e : rdsT1 "log_utf8" args = [.u8 (args.getD 1 0) (args.getD 0 0)] := by
      rw [rdsT1, if_neg (by decide), if_pos rfl]
    rw [e] at h
    rw [ansT1_log_utf8, ansT1_log_utf8, updT1_log_utf8, updT1_log_utf8]
    unfold ansLogUtf8 updLogUtf8
    rw [lgG_mem σ _ _ _ (fun b hb => h b (Or.inl hb))]
    exact ⟨rfl, rfl⟩
  · have e : rdsT1 "value_return" args = [.mr (args.getD 1 0) (args.getD 0 0)] := by
      rw [rdsT1, if_neg (by decide), if_neg (by decide), if_pos rfl]
    rw [e] at h
    rw [ansT1_value_return, ansT1_value_return, updT1_value_return, updT1_value_return]
    unfold ansValueReturn updValueReturn
    rw [vrG_mem σ _ _ _ (fun b hb => h b (Or.inl hb))]
    exact ⟨rfl, rfl⟩


/-! ## 5. The spec clause at the trace level (lane B's `ProducerObl.spec`, restated) -/

theorem valNat_vNum (v : Val) : TwoRun.valNat v = vNum v := by cases v <;> rfl

theorem popsF_fst : ∀ (j : Nat) (s : St) (out : Array Nat), j ≤ s.stack.size →
    (TwoRun.popsF j s out).1 =
      out ++ ((List.range j).map fun k => vNum (s.stack[s.stack.size - 1 - k]?.getD (.i32 0))).toArray
  | 0, s, out, _ => by simp [TwoRun.popsF]
  | j + 1, s, out, hj => by
    simp only [TwoRun.popsF]
    rw [TwoRun.popN_eq]
    rw [popsF_fst j _ _ (by simp; omega)]
    simp only [Array.size_pop]
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    rw [Array.back?_eq_getElem?, valNat_vNum]
    apply Array.ext'
    simp only [Array.toList_append, Array.toList_push, List.append_assoc]
    simp only [List.cons_append, List.nil_append, Nat.sub_zero]
    congr 2
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    simp only [Function.comp, Array.getElem?_pop]
    rw [if_pos (by omega)]
    congr 3
    omega

theorem argsOf_toList (n : Nat) (s : St) (hn : n ≤ s.stack.size) :
    (TwoRun.argsOf n s).toList = (List.range n).map fun i => vNum (s.stack[s.stack.size - n + i]?.getD (.i32 0)) := by
  apply List.ext_getElem
  · simp [TwoRun.argsOf, TwoRun.popsF_size]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp [TwoRun.argsOf, popsF_fst n s #[] hn]
    congr 3; omega

theorem popsF_snd (n : Nat) (s : St) (hn : n ≤ s.stack.size) :
    (TwoRun.popsF n s #[]).2 = { s with stack := s.stack.extract 0 (s.stack.size - n) } := by
  obtain ⟨-, e, -⟩ := TwoRun.popsF_two n s s [] [] s.stack.toList #[] (by simp) (by simp) (by simp; exact hn)
  rw [e]
  congr 1
  apply Array.ext'
  simp

theorem readByte_stack (s : St) (x : Array Val) : readByte { s with stack := x } = readByte s := rfl
theorem memBytes_stack (s : St) (x : Array Val) : memBytes { s with stack := x } = memBytes s := rfl

section Trace
open ZkFormal.Algebra Chips Seg Local HostIf

theorem hostReadMem_eq {tr : Trace} {pub : List F} {r : Nat} {s : St} {b : Nat}
    (hmem : ∀ x ∈ hostBytes tr pub r, x.1 = 0 → x.2.1 = 0 → (readByte s x.2.2.1).toNat = x.2.2.2)
    (hx : ∃ x ∈ hostBytes tr pub r, x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = b) : readByte s b = hostReadMem tr pub r b := by
  obtain ⟨x, hxm, hx1, hx2, hx3⟩ := hx
  unfold hostReadMem
  cases hf : (hostBytes tr pub r).find? (fun x => x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = b) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf x hxm
    simp [hx1, hx2, hx3] at this
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    dsimp only
    rw [← hmem y hy hp1 hp2, hp3]
    simp

/-- **The spec clause of the producer obligations, with the host-side update** (`ProducerObl.spec`
restated): `runOf` cannot express `value_return`/`log_utf8`/`storage_write` (they change `ret`,
`logs`/`totalLogLen`, `trie`/`real`/`storageUsage`), so the arm is `runOfU` with `A.upd`; the
stack premise `len ≤ size` is added (an honest pre-state holds the row's operands).  The host-side
premise of `ProducerObl.spec` is dropped (the clause holds for every state). -/
def SpecU (A : HostAnsU) (tr : Trace) (pub : List F) (memSz : Nat → Nat) : Prop :=
  ∀ r, HAct tr pub r → ∀ s : St,
    (hostArgs tr r).length ≤ s.stack.size →
    (∀ i, i < (hostArgs tr r).length → vNum (s.stack[s.stack.size - (hostArgs tr r).length + i]?.getD (.i32 0)) =
      (hostArgs tr r).getD i 0) →
    (∀ x ∈ hostBytes tr pub r, x.1 = 0 → x.2.1 = 0 → (readByte s x.2.2.1).toNat = x.2.2.2) →
    memBytes s = memSz r →
    (hostCall (hidName (hostHid tr r))).get!.run s =
      runOfU { s with stack := s.stack.extract 0 (s.stack.size - (hostArgs tr r).length) }
        (A.ans (hidName (hostHid tr r)) s (hostArgs tr r) (hostReadMem tr pub r) (memSz r))
        (A.upd (hidName (hostHid tr r)) s (hostArgs tr r) (hostReadMem tr pub r) (memSz r))

/-- **The spec half of lane B's obligations for T1's host set**: if every active HOST row calls a T1
host, its argument count is that host's arity (`np`), and its request bytes cover the arm's read
set (`rdsT1`), then `ansT1U` satisfies the spec clause. -/
theorem specU_T1 (tr : Trace) (pub : List F) (memSz : Nat → Nat)
    (hT1 : ∀ r, HAct tr pub r → hidName (hostHid tr r) ∈ t1Hosts)
    (hnp : ∀ r, HAct tr pub r → (hostArgs tr r).length = nargsT1 (hidName (hostHid tr r)))
    (hcov : ∀ r, HAct tr pub r → ∀ (σ : St) b, TwoRun.rdSet σ (rdsT1 (hidName (hostHid tr r)) (hostArgs tr r)) b →
      ∃ x ∈ hostBytes tr pub r, x.1 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = b) :
    SpecU ansT1U tr pub memSz := by
  intro r hA s hsz hst hmem hms
  have hm := hT1 r hA
  have hn := hnp r hA
  have e0 := TwoRun.popArgs_ok (nargsT1 (hidName (hostHid tr r))) s
  rw [ansT1_arm hm e0, popsF_snd _ s (by omega)]
  have ha : (TwoRun.argsOf (nargsT1 (hidName (hostHid tr r))) s).toList = hostArgs tr r := by
    rw [argsOf_toList _ s (by omega)]
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [← hn, hst i h2]
      simp [List.getD_eq_getElem?_getD, h2]
  rw [ha, readByte_stack, memBytes_stack, hms, ← hn]
  obtain ⟨c1, c2⟩ := ansT1_congr (hostFieldsEq_stack s (s.stack.extract 0 (s.stack.size - (hostArgs tr r).length)))
    (hidName (hostHid tr r)) (hostArgs tr r) (readByte s) (memSz r)
  rw [c1, c2]
  obtain ⟨m1, m2⟩ := ansT1_mem hm s (hostArgs tr r) (mem := readByte s) (mem' := hostReadMem tr pub r) (memSz r)
    (fun b hb => hostReadMem_eq hmem (hcov r hA s b hb))
  rw [m1, m2]
  rfl

end Trace


#print axioms ansT1_arm
#print axioms ansT1_congr
#print axioms ansT1_mem
#print axioms specU_T1

end HostAns
end WasmBase
