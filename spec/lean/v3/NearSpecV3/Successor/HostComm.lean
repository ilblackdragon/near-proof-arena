import Lean
import NearSpecV3.Wasm.Exec
import NearSpecV3.Logged.Lockstep

/-!
# W12 — the interpreter flags commute with every host program that does not read them (O2/O3)

`St.curveHosts` and `St.globalActions` are set once at instantiation and read only at named sites:
`dispatchArm` (curve hosts), `callHost`'s exclusion guard and seven promise arms of `Host.lean`
(global actions). `setF oc og` overwrites the curve-host flag when `oc = some c` and the
global-actions flag when `og = some g`, and leaves every other field alone.

`CR φ x y`: running `y` from `φ t` is running `x` from `t` with `φ` applied to the resulting state
(`mapSt`), values and errors unchanged. `CR φ x x` says `x` does not observe what `φ` changes.

This file is the framework and the helper lemmas; the per-arm theorems are generated in
`HostCommArms.lean` and the machine steps in `HostCommStep.lean`. The pattern is the store
commutation of `Logged/WasmCR*.lean` (map `E σ`), with the flag map in place of `E σ`.
-/

namespace NearSpecV3.Successor.HostComm

open NearSpecV3.Wasm

/-- Overwrite the interpreter flags: the curve-host selector when `oc = some c`, the global-actions
flag when `og = some g`. -/
def setF (oc og : Option Bool) (s : St) : St :=
  { s with curveHosts := oc.getD s.curveHosts, globalActions := og.getD s.globalActions }

def mapSt {α : Type} (f : St → St) : EStateM.Result String St α → EStateM.Result String St α
  | .ok a s => .ok a (f s)
  | .error e s => .error e (f s)

structure CR {α : Type} (φ : St → St) (x y : HM α) : Prop where
  h : ∀ t, y.run (φ t) = mapSt φ (x.run t)

section
variable {φ : St → St}

theorem CR_pure {α : Type} (a : α) : CR φ (pure a) (pure a) := ⟨fun _ => rfl⟩
theorem CR_pure' {α : Type} {a b : α} (h : b = a) : CR φ (pure a) (pure b) := h ▸ ⟨fun _ => rfl⟩
theorem CR_throw {α : Type} (e : String) : CR φ (throw e : HM α) (throw e) := ⟨fun _ => rfl⟩
theorem CR_throw' {α : Type} {e e' : String} (h : e' = e) : CR φ (throw e : HM α) (throw e') :=
  h ▸ ⟨fun _ => rfl⟩

theorem CR_bind {α β : Type} {x y : HM α} {f g : α → HM β} (h1 : CR φ x y) (h2 : ∀ a, CR φ (f a) (g a)) :
    CR φ (x >>= f) (y >>= g) := by
  constructor; intro t
  have := h1.h t
  simp only [EStateM.run] at this ⊢
  show EStateM.bind y g (φ t) = mapSt φ (EStateM.bind x f t)
  unfold EStateM.bind
  rw [this]
  cases x t with
  | ok a s => exact (h2 a).h s
  | error e s => rfl

theorem CR_get_bind {β : Type} {f g : St → HM β} (h : ∀ t, CR φ (f t) (g (φ t))) :
    CR φ (get >>= f) (get >>= g) := by
  constructor; intro t; exact (h t).h t

theorem CR_set (u v : St) (h : v = φ u) : CR φ (set u) (set v) := ⟨fun _ => by subst h; rfl⟩

theorem CR_modify (f g : St → St) (h : ∀ t, g (φ t) = φ (f t)) : CR φ (modify f) (modify g) := by
  constructor; intro t
  show EStateM.Result.ok () (g (φ t)) = EStateM.Result.ok () (φ (f t)); rw [h]

theorem CR_ite {α : Type} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c') {x y x' y' : HM α}
    (h1 : CR φ x x') (h2 : CR φ y y') : CR φ (if c then x else y) (if c' then x' else y') := by
  subst hc; by_cases hc : c <;> simp only [hc, ite_true, ite_false] <;> assumption

theorem CR_dite {α : Type} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c') {x : c → HM α}
    {y : ¬c → HM α} {x' : c' → HM α} {y' : ¬c' → HM α}
    (h1 : ∀ h h', CR φ (x h) (x' h')) (h2 : ∀ h h', CR φ (y h) (y' h')) :
    CR φ (if h : c then x h else y h) (if h : c' then x' h else y' h) := by
  subst hc; by_cases hc : c <;> simp only [hc, dite_true, dite_false] <;> apply_assumption

theorem CR_forIn_list {β : Type} (l : List Nat) (b : β) (f g : Nat → β → HM (ForInStep β))
    (h : ∀ i b, CR φ (f i b) (g i b)) : CR φ (forIn l b f) (forIn l b g) := by
  induction l generalizing b with
  | nil => exact CR_pure b
  | cons a l ih =>
    simp only [List.forIn_cons]
    apply CR_bind (h a b); intro r
    cases r with
    | done b => exact CR_pure b
    | yield b => exact ih b

theorem CR_forIn {β : Type} (r : Std.Legacy.Range) (b : β) (f g : Nat → β → HM (ForInStep β))
    (h : ∀ i b, CR φ (f i b) (g i b)) : CR φ (forIn r b f) (forIn r b g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']; exact CR_forIn_list _ b f g h

/-- A commutation is a statement about every start state; read it at one. -/
theorem CR.run {x : HM α} (hc : CR φ x x) (t : St) : x.run (φ t) = mapSt φ (x.run t) := hc.h t

end

/-! ## `setF` is invisible to everything but the two flags -/

section
variable (oc og : Option Bool) (t : St)
@[simp] theorem F_stack : (setF oc og t).stack = t.stack := rfl
@[simp] theorem F_frames : (setF oc og t).frames = t.frames := rfl
@[simp] theorem F_pages : (setF oc og t).pages = t.pages := rfl
@[simp] theorem F_globals : (setF oc og t).globals = t.globals := rfl
@[simp] theorem F_table : (setF oc og t).table = t.table := rfl
@[simp] theorem F_tableMax : (setF oc og t).tableMax = t.tableMax := rfl
@[simp] theorem F_elems : (setF oc og t).elems = t.elems := rfl
@[simp] theorem F_datas : (setF oc og t).datas = t.datas := rfl
@[simp] theorem F_stackRem : (setF oc og t).stackRem = t.stackRem := rfl
@[simp] theorem F_gas : (setF oc og t).gas = t.gas := rfl
@[simp] theorem F_ctx : (setF oc og t).ctx = t.ctx := rfl
@[simp] theorem F_ret : (setF oc og t).ret = t.ret := rfl
@[simp] theorem F_balance : (setF oc og t).balance = t.balance := rfl
@[simp] theorem F_storageUsage : (setF oc og t).storageUsage = t.storageUsage := rfl
@[simp] theorem F_registers : (setF oc og t).registers = t.registers := rfl
@[simp] theorem F_regUsage : (setF oc og t).regUsage = t.regUsage := rfl
@[simp] theorem F_logs : (setF oc og t).logs = t.logs := rfl
@[simp] theorem F_totalLogLen : (setF oc og t).totalLogLen = t.totalLogLen := rfl
@[simp] theorem F_promises : (setF oc og t).promises = t.promises := rfl
@[simp] theorem F_trie : (setF oc og t).trie = t.trie := rfl
@[simp] theorem F_actions : (setF oc og t).actions = t.actions := rfl
@[simp] theorem F_dataCount : (setF oc og t).dataCount = t.dataCount := rfl
@[simp] theorem F_real : (setF oc og t).real = t.real := rfl
@[simp] theorem F_subsidized : (setF oc og t).subsidized = t.subsidized := rfl
@[simp] theorem F_memBytes : memBytes (setF oc og t) = memBytes t := rfl
@[simp] theorem F_readByte (a : Nat) : readByte (setF oc og t) a = readByte t a := rfl
@[simp] theorem F_readBytes (a n : Nat) : readBytes (setF oc og t) a n = readBytes t a n := rfl
@[simp] theorem F_readLE (a w : Nat) : readLE (setF oc og t) a w = readLE t a w := rfl
@[simp] theorem F_trieGet (k : ByteArray) : trieGet (setF oc og t) k = trieGet t k := rfl
@[simp] theorem F_dataIdOf (n : Nat) : dataIdOf (setF oc og t) n = dataIdOf t n := rfl
@[simp] theorem F_receiptReceiver (n : Nat) : receiptReceiver (setF oc og t) n = receiptReceiver t n := rfl
/-- The global-actions flag under a map that leaves it alone. -/
@[simp] theorem F_globalActions_none (oc : Option Bool) : (setF oc none t).globalActions = t.globalActions := rfl
@[simp] theorem F_curveHosts_none (og : Option Bool) : (setF none og t).curveHosts = t.curveHosts := rfl
theorem F_readByte' : readByte (setF oc og t) = readByte t := rfl
theorem F_trieGet' : trieGet (setF oc og t) = trieGet t := rfl
theorem F_dataIdOf' : dataIdOf (setF oc og t) = dataIdOf t := rfl
theorem F_receiptReceiver' : receiptReceiver (setF oc og t) = receiptReceiver t := rfl
@[simp] theorem F_popN : popN (setF oc og t) = ((popN t).1, setF oc og (popN t).2) := by
  unfold popN popV; simp only [F_stack]; cases t.stack.back?.getD (Val.i32 0) <;> rfl
end

theorem F_writeByte (oc og : Option Bool) (t : St) (a : Nat) (v : UInt8) :
    writeByte (setF oc og t) a v = setF oc og (writeByte t a v) := rfl

theorem forIn'_F {oc og : Option Bool} : ∀ (l : List Nat) (f : (x : Nat) → x ∈ l → St → St) (t : St)
    (_hf : ∀ x h t, f x h (setF oc og t) = setF oc og (f x h t)),
    (forIn' (m := Id) l (setF oc og t) fun x h s => ForInStep.yield (f x h s)) =
      setF oc og (forIn' (m := Id) l t fun x h s => ForInStep.yield (f x h s))
  | [], _, _, _ => rfl
  | x :: xs, f, t, hf => by
    simp only [List.forIn'_cons]
    rw [hf]
    exact forIn'_F xs (fun y hy => f y (List.mem_cons_of_mem _ hy)) _ (fun y hy t => hf y _ t)

theorem F_writeBytes (oc og : Option Bool) (t : St) (a : Nat) (d : ByteArray) :
    writeBytes (setF oc og t) a d = setF oc og (writeBytes t a d) := by
  unfold writeBytes
  simp only [Id.run, Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact forIn'_F _ _ _ (fun _ _ _ => rfl)

/-! ## The `cr` tactic -/

syntax "cr_call" : tactic
macro_rules | `(tactic| cr_call) => `(tactic| first | exact CR_pure _ | exact CR_throw _)

open Lean Elab Tactic Meta in
/-- `intro`, only on propositions. -/
elab "cr_intro" : tactic => do
  let g ← getMainGoal
  unless (← isProp (← g.getType)) do throwError "cr_intro: not a proposition"
  evalTactic (← `(tactic| intro))

/-- Rewrite `setF oc og t` away everywhere, also inside instance arguments (which `simp` skips). -/
macro "cr_rwF" : tactic => `(tactic| ((try rw [F_readByte']); (try rw [F_trieGet']); (try rw [F_dataIdOf']); (try rw [F_receiptReceiver']); (try rw [F_stack]); (try rw [F_frames]); (try rw [F_pages]); (try rw [F_globals]); (try rw [F_table]); (try rw [F_tableMax]); (try rw [F_elems]); (try rw [F_datas]); (try rw [F_stackRem]); (try rw [F_gas]); (try rw [F_ctx]); (try rw [F_ret]); (try rw [F_balance]); (try rw [F_storageUsage]); (try rw [F_registers]); (try rw [F_regUsage]); (try rw [F_logs]); (try rw [F_totalLogLen]); (try rw [F_promises]); (try rw [F_trie]); (try rw [F_actions]); (try rw [F_dataCount]); (try rw [F_real]); (try rw [F_subsidized]); (try rw [F_memBytes]); (try rw [F_readByte]); (try rw [F_trieGet]); (try rw [F_dataIdOf]); (try rw [F_receiptReceiver]); (try rw [F_readBytes]); (try rw [F_readLE]); (try rw [F_popN]); (try rw [F_globalActions_none]); (try rw [F_curveHosts_none])))

/-- Close the `modify` side condition `g (φ t) = φ (f t)`. -/
macro "cr_modclose" : tactic => `(tactic| first
  | rfl
  | (rcases t with ⟨⟩; rename_i real _ _ _; cases real <;> rfl)
  | (simp only [F_real]; split <;> rfl)
  | (cases hr : t.real <;> (simp only [F_real, hr, Option.isSome, ite_true, ite_false, Bool.false_eq_true,
      ↓reduceIte]) <;> rfl))

syntax "cr_step" : tactic
macro_rules | `(tactic| cr_step) => `(tactic| first
  | contradiction
  | ((with_reducible apply CR_get_bind); intro; cr_rwF; (try dsimp only [F_stack, F_frames, F_pages, F_globals, F_table,
      F_tableMax, F_elems, F_datas, F_stackRem, F_gas, F_ctx, F_ret, F_balance, F_storageUsage, F_registers,
      F_regUsage, F_logs, F_totalLogLen, F_promises, F_trie, F_actions, F_dataCount, F_real, F_subsidized,
      F_memBytes, F_readByte, F_trieGet, F_dataIdOf, F_receiptReceiver, F_globalActions_none, F_curveHosts_none]);
      (try simp only [F_readBytes, F_readLE, F_popN]))
  | ((with_reducible apply CR_pure'); rfl)
  | ((with_reducible apply CR_throw'); rfl)
  | ((with_reducible apply CR_set); first | rfl | simp only [F_writeBytes, F_writeByte])
  | ((with_reducible apply CR_modify); intro t; cr_modclose)
  | (with_reducible apply CR_ite _ _ rfl)
  | (with_reducible apply CR_dite _ _ rfl)
  | (with_reducible cr_call)
  | ((with_reducible apply CR_bind); first
      | ((with_reducible apply CR_modify); intro t; cr_modclose)
      | ((with_reducible apply CR_set); first | rfl | simp only [F_writeBytes, F_writeByte])
      | ((with_reducible apply CR_pure'); rfl)
      | (with_reducible cr_call)
      | (with_reducible apply CR_ite _ _ rfl)
      | (with_reducible apply CR_dite _ _ rfl)
      | (with_reducible apply CR_forIn)
      )
  | (with_reducible apply CR_forIn)
  | (split <;> try (rename_i hh; simp only [hh]))
  | cr_intro
  | (simp only []))

macro "cr" : tactic => `(tactic| repeat (any_goals cr_step))

/-! ## Helpers -/

section
variable (oc og : Option Bool)

theorem CR_withGas (f : Gas → Gas × Option String) : CR (setF oc og) (withGas f) (withGas f) := by
  unfold withGas; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_withGas)
theorem CR_payBaseH (c : Cost) : CR (setF oc og) (payBaseH c) (payBaseH c) := by unfold payBaseH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payBaseH)
theorem CR_payPerH (c : Cost) (n : Nat) : CR (setF oc og) (payPerH c n) (payPerH c n) := by unfold payPerH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payPerH)
theorem CR_payActionH (b bc u : Nat) : CR (setF oc og) (payActionH b bc u) (payActionH b bc u) := by
  unfold payActionH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payActionH)
theorem CR_burnH (x : Nat) : CR (setF oc og) (burnH x) (burnH x) := by unfold burnH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_burnH)
theorem CR_hErr {α : Type} (e : String) : CR (setF oc og) ((hErr e : HM α)) ((hErr e : HM α)) := by
  unfold hErr; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_hErr)
theorem CR_realOpH (r : TTN.RealStore) (f : TTN.RealStore → ByteArray → Gas → TTN.Out) (k : ByteArray) :
    CR (setF oc og) (realOpH r f k) (realOpH r f k) := by unfold realOpH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_realOpH)
theorem CR_observeH : CR (setF oc og) observeH observeH := by unfold observeH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_observeH)
theorem CR_realSetH (r : TTN.RealStore) (k : ByteArray) (v : Option ByteArray) :
    CR (setF oc og) (realSetH r k v) (realSetH r k v) := by unfold realSetH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_realSetH)
theorem CR_readMemH (p l : Nat) : CR (setF oc og) (readMemH p l) (readMemH p l) := by unfold readMemH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_readMemH)
theorem CR_writeMemH (p : Nat) (d : ByteArray) : CR (setF oc og) (writeMemH p d) (writeMemH p d) := by
  unfold writeMemH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_writeMemH)
theorem CR_regGetH (i : Nat) : CR (setF oc og) (regGetH i) (regGetH i) := by unfold regGetH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_regGetH)
theorem CR_regSetH (i : Nat) (d : ByteArray) (cb : Bool) : CR (setF oc og) (regSetH i d cb) (regSetH i d cb) := by
  unfold regSetH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_regSetH)
theorem CR_memOrRegH (p l : Nat) : CR (setF oc og) (memOrRegH p l) (memOrRegH p l) := by unfold memOrRegH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_memOrRegH)
theorem CR_getU128H (p : Nat) : CR (setF oc og) (getU128H p) (getU128H p) := by unfold getU128H; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_getU128H)
theorem CR_setU128H (p v : Nat) : CR (setF oc og) (setU128H p v) (setU128H p v) := by unfold setU128H; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_setU128H)
theorem CR_logLenExceeded {α : Type} (a : Nat) : CR (setF oc og) ((logLenExceeded a : HM α)) ((logLenExceeded a : HM α)) := by
  unfold logLenExceeded; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_logLenExceeded)
theorem CR_utf8H (l p : Nat) : CR (setF oc og) (utf8H l p) (utf8H l p) := by unfold utf8H; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_utf8H)
theorem CR_utf16H (l p : Nat) : CR (setF oc og) (utf16H l p) (utf16H l p) := by unfold utf16H; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_utf16H)
theorem CR_checkCanLogH : CR (setF oc og) (checkCanLogH) (checkCanLogH) := by unfold checkCanLogH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_checkCanLogH)
theorem CR_pushLogH (m : String) : CR (setF oc og) (pushLogH m) (pushLogH m) := by unfold pushLogH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_pushLogH)
theorem CR_guestPanic {α : Type} (m : String) : CR (setF oc og) ((guestPanic m : HM α)) ((guestPanic m : HM α)) := by
  unfold guestPanic; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_guestPanic)
theorem CR_readAccountIdH (l p : Nat) : CR (setF oc og) (readAccountIdH l p) (readAccountIdH l p) := by
  unfold readAccountIdH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_readAccountIdH)
theorem CR_pushAction (a : MAct) : CR (setF oc og) (pushAction a) (pushAction a) := by unfold pushAction; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_pushAction)
theorem CR_pushPromiseH (p : PromiseV) : CR (setF oc og) (pushPromiseH p) (pushPromiseH p) := by
  unfold pushPromiseH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_pushPromiseH)
theorem CR_promiseReceiptH (i : Nat) : CR (setF oc og) (promiseReceiptH i) (promiseReceiptH i) := by
  unfold promiseReceiptH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_promiseReceiptH)
theorem CR_payGasKeyAddH (sir : Bool) (a b n : Nat) : CR (setF oc og) (payGasKeyAddH sir a b n) (payGasKeyAddH sir a b n) := by
  unfold payGasKeyAddH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payGasKeyAddH)
theorem CR_payActionBaseH (f : Fee3) (sir : Bool) : CR (setF oc og) (payActionBaseH f sir) (payActionBaseH f sir) := by
  unfold payActionBaseH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payActionBaseH)
theorem CR_payActionPerByteH (f : Fee3) (n : Nat) (sir : Bool) : CR (setF oc og) (payActionPerByteH f n sir) (payActionPerByteH f n sir) := by
  unfold payActionPerByteH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payActionPerByteH)
theorem CR_payNewReceiptH (sir : Bool) (d : Array Bool) : CR (setF oc og) (payNewReceiptH sir d) (payNewReceiptH sir d) := by
  unfold payNewReceiptH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payNewReceiptH)
theorem CR_deductBalanceH (a : Nat) : CR (setF oc og) (deductBalanceH a) (deductBalanceH a) := by
  unfold deductBalanceH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_deductBalanceH)
theorem CR_popArgs (n : Nat) : CR (setF oc og) (popArgs n) (popArgs n) := by unfold popArgs; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_popArgs)
theorem CR_pushRet (v : Nat) (b : Bool) : CR (setF oc og) (pushRet v b) (pushRet v b) := by unfold pushRet; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_pushRet)
theorem CR_realPutH (k : ByteArray) (v : Option ByteArray) : CR (setF oc og) (realPutH k v) (realPutH k v) := by
  unfold realPutH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_realPutH)
theorem CR_realGetH (k : ByteArray) : CR (setF oc og) (realGetH k) (realGetH k) := by unfold realGetH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_realGetH)
theorem CR_realHasH (k : ByteArray) : CR (setF oc og) (realHasH k) (realHasH k) := by unfold realHasH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_realHasH)
theorem CR_thenDataIdsH (n : Nat) : CR (setF oc og) (thenDataIdsH n) (thenDataIdsH n) := by
  unfold thenDataIdsH; apply CR_modify; intro t
  cases hr : t.real
  · simp only [F_real, hr, Option.isSome]; rfl
  · simp only [F_real, hr, Option.isSome]; rfl
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_thenDataIdsH)
theorem CR_hashHost (a b : Cost) (h : ByteArray → ByteArray) (l p r : Nat) : CR (setF oc og) (hashHost a b h l p r) (hashHost a b h l p r) := by
  unfold hashHost; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_hashHost)
theorem CR_functionCallActionH (i ml mp al ap amt g w : Nat) : CR (setF oc og) (functionCallActionH i ml mp al ap amt g w) (functionCallActionH i ml mp al ap amt g w) := by
  unfold functionCallActionH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_functionCallActionH)
theorem CR_readContractIdH (b : Bool) (l p : Nat) : CR (setF oc og) (readContractIdH b l p) (readContractIdH b l p) := by
  unfold readContractIdH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_readContractIdH)
theorem CR_readContractIdDataH (b : Bool) (l p : Nat) : CR (setF oc og) (readContractIdDataH b l p) (readContractIdDataH b l p) := by
  unfold readContractIdDataH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_readContractIdDataH)
set_option maxHeartbeats 0 in
theorem CR_yieldCreateWithIdH (a : Vector Nat 9) : CR (setF oc og) (yieldCreateWithIdH a) (yieldCreateWithIdH a) := by
  unfold yieldCreateWithIdH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_yieldCreateWithIdH)
end

/-! The four helpers that read `globalActions` commute only with maps that leave it alone
(`og = none`). -/
section
variable (oc : Option Bool)
theorem CR_deployGlobalH (a : Vector Nat 3) (b : Bool) : CR (setF oc none) (deployGlobalH a b) (deployGlobalH a b) := by
  unfold deployGlobalH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_deployGlobalH)
theorem CR_useGlobalH (b : Bool) (a : Vector Nat 3) : CR (setF oc none) (useGlobalH b a) (useGlobalH b a) := by
  unfold useGlobalH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_useGlobalH)
theorem CR_setStateInitDataH (r i : Nat) (k v : ByteArray) : CR (setF oc none) (setStateInitDataH r i k v) (setStateInitDataH r i k v) := by
  unfold setStateInitDataH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_setStateInitDataH)
theorem CR_stateInitH (b : Bool) (a : Vector Nat 4) : CR (setF oc none) (stateInitH b a) (stateInitH b a) := by
  unfold stateInitH; cr
macro_rules | `(tactic| cr_call) => `(tactic| apply CR_stateInitH)
end

#print axioms CR_regSetH
#print axioms CR_stateInitH

end NearSpecV3.Successor.HostComm
