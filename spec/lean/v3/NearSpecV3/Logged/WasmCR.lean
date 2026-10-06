import Lean
import NearSpecV3.Wasm.Exec

/-!
# The WASM machine reads the trie store only in the storage host functions

`St.E σ s` replaces the store function of the trie-backed `External` (`TTN.RealStore.store`) by `σ`.
`CR x y` (for host computations): running `y` on `E σ t` gives `x`'s result on `t`, with the
final state's store replaced by `σ`. Every host function that does not touch the trie store
satisfies `CR h h` for every `σ` (`CR_hostCall`), and every machine step that does not call one of
the storage host functions commutes with `E σ` (`step_E`). With `σ := t.real.store` this also says
such steps keep the store field.
-/

namespace NearSpecV3.Logged.W

open NearSpecV3.Wasm

def E (σ : TTN.Store) (s : St) : St := { s with real := s.real.map fun r => { r with store := σ } }

def mapSt {α : Type} (f : St → St) : EStateM.Result String St α → EStateM.Result String St α
  | .ok a s => .ok a (f s)
  | .error e s => .error e (f s)

structure CR {α : Type} (σ : TTN.Store) (x y : HM α) : Prop where
  h : ∀ t, y.run (E σ t) = mapSt (E σ) (x.run t)

section
variable {σ : TTN.Store}

theorem CR_pure {α : Type} (a : α) : CR σ (pure a) (pure a) := ⟨fun _ => rfl⟩
theorem CR_pure' {α : Type} {a b : α} (h : b = a) : CR σ (pure a) (pure b) := h ▸ ⟨fun _ => rfl⟩
theorem CR_throw {α : Type} (e : String) : CR σ (throw e : HM α) (throw e) := ⟨fun _ => rfl⟩
theorem CR_throw' {α : Type} {e e' : String} (h : e' = e) : CR σ (throw e : HM α) (throw e') :=
  h ▸ ⟨fun _ => rfl⟩

theorem CR_bind {α β : Type} {x y : HM α} {f g : α → HM β} (h1 : CR σ x y) (h2 : ∀ a, CR σ (f a) (g a)) :
    CR σ (x >>= f) (y >>= g) := by
  constructor; intro t
  have := h1.h t
  simp only [EStateM.run] at this ⊢
  show EStateM.bind y g (E σ t) = mapSt (E σ) (EStateM.bind x f t)
  unfold EStateM.bind
  rw [this]
  cases x t with
  | ok a s => exact (h2 a).h s
  | error e s => rfl

theorem CR_get_bind {β : Type} {f g : St → HM β} (h : ∀ t, CR σ (f t) (g (E σ t))) :
    CR σ (get >>= f) (get >>= g) := by
  constructor; intro t; exact (h t).h t

theorem CR_set (u v : St) (h : v = E σ u) : CR σ (set u) (set v) := ⟨fun _ => by subst h; rfl⟩

theorem CR_modify (f g : St → St) (h : ∀ t, g (E σ t) = E σ (f t)) : CR σ (modify f) (modify g) := by
  constructor; intro t
  show EStateM.Result.ok () (g (E σ t)) = EStateM.Result.ok () (E σ (f t)); rw [h]

theorem CR_ite {α : Type} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c') {x y x' y' : HM α}
    (h1 : CR σ x x') (h2 : CR σ y y') : CR σ (if c then x else y) (if c' then x' else y') := by
  subst hc; by_cases hc : c <;> simp only [hc, ite_true, ite_false] <;> assumption

theorem CR_dite {α : Type} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c = c') {x : c → HM α}
    {y : ¬c → HM α} {x' : c' → HM α} {y' : ¬c' → HM α}
    (h1 : ∀ h h', CR σ (x h) (x' h')) (h2 : ∀ h h', CR σ (y h) (y' h')) :
    CR σ (if h : c then x h else y h) (if h : c' then x' h else y' h) := by
  subst hc; by_cases hc : c <;> simp only [hc, dite_true, dite_false] <;> apply_assumption

theorem CR_forIn_list {β : Type} (l : List Nat) (b : β) (f g : Nat → β → HM (ForInStep β))
    (h : ∀ i b, CR σ (f i b) (g i b)) : CR σ (forIn l b f) (forIn l b g) := by
  induction l generalizing b with
  | nil => exact CR_pure b
  | cons a l ih =>
    simp only [List.forIn_cons]
    apply CR_bind (h a b); intro r
    cases r with
    | done b => exact CR_pure b
    | yield b => exact ih b

theorem CR_forIn {β : Type} (r : Std.Legacy.Range) (b : β) (f g : Nat → β → HM (ForInStep β))
    (h : ∀ i b, CR σ (f i b) (g i b)) : CR σ (forIn r b f) (forIn r b g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']; exact CR_forIn_list _ b f g h

end

theorem E_writeByte (σ) (t : St) (a : Nat) (v : UInt8) : writeByte (E σ t) a v = E σ (writeByte t a v) := rfl

theorem forIn'_E {σ} : ∀ (l : List Nat) (f : (x : Nat) → x ∈ l → St → St) (t : St)
    (_hf : ∀ x h t, f x h (E σ t) = E σ (f x h t)),
    (forIn' (m := Id) l (E σ t) fun x h s => ForInStep.yield (f x h s)) =
      E σ (forIn' (m := Id) l t fun x h s => ForInStep.yield (f x h s))
  | [], _, _, _ => rfl
  | x :: xs, f, t, hf => by
    simp only [List.forIn'_cons]
    rw [hf]
    exact forIn'_E xs (fun y hy => f y (List.mem_cons_of_mem _ hy)) _ (fun y hy t => hf y _ t)

theorem E_writeBytes (σ) (t : St) (a : Nat) (d : ByteArray) : writeBytes (E σ t) a d = E σ (writeBytes t a d) := by
  unfold writeBytes
  simp only [Id.run, Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact forIn'_E _ _ _ (fun _ _ _ => rfl)


/-! ## `E` is invisible to everything but the store -/

section
variable (σ : TTN.Store) (t : St)
@[simp] theorem E_stack : (E σ t).stack = t.stack := rfl
@[simp] theorem E_frames : (E σ t).frames = t.frames := rfl
@[simp] theorem E_pages : (E σ t).pages = t.pages := rfl
@[simp] theorem E_globals : (E σ t).globals = t.globals := rfl
@[simp] theorem E_table : (E σ t).table = t.table := rfl
@[simp] theorem E_tableMax : (E σ t).tableMax = t.tableMax := rfl
@[simp] theorem E_elems : (E σ t).elems = t.elems := rfl
@[simp] theorem E_datas : (E σ t).datas = t.datas := rfl
@[simp] theorem E_stackRem : (E σ t).stackRem = t.stackRem := rfl
@[simp] theorem E_gas : (E σ t).gas = t.gas := rfl
@[simp] theorem E_ctx : (E σ t).ctx = t.ctx := rfl
@[simp] theorem E_ret : (E σ t).ret = t.ret := rfl
@[simp] theorem E_balance : (E σ t).balance = t.balance := rfl
@[simp] theorem E_storageUsage : (E σ t).storageUsage = t.storageUsage := rfl
@[simp] theorem E_registers : (E σ t).registers = t.registers := rfl
@[simp] theorem E_regUsage : (E σ t).regUsage = t.regUsage := rfl
@[simp] theorem E_logs : (E σ t).logs = t.logs := rfl
@[simp] theorem E_totalLogLen : (E σ t).totalLogLen = t.totalLogLen := rfl
@[simp] theorem E_promises : (E σ t).promises = t.promises := rfl
@[simp] theorem E_trie : (E σ t).trie = t.trie := rfl
@[simp] theorem E_actions : (E σ t).actions = t.actions := rfl
@[simp] theorem E_dataCount : (E σ t).dataCount = t.dataCount := rfl
@[simp] theorem E_subsidized : (E σ t).subsidized = t.subsidized := rfl
@[simp] theorem E_real_isSome : (E σ t).real.isSome = t.real.isSome := by unfold E; cases t.real <;> rfl
@[simp] theorem E_memBytes : memBytes (E σ t) = memBytes t := rfl
@[simp] theorem E_readByte (a : Nat) : readByte (E σ t) a = readByte t a := rfl
@[simp] theorem E_readBytes (a n : Nat) : readBytes (E σ t) a n = readBytes t a n := by
  unfold readBytes; simp only [E_readByte]
@[simp] theorem E_readLE (a w : Nat) : readLE (E σ t) a w = readLE t a w := by
  unfold readLE; simp only [E_readByte]
@[simp] theorem E_trieGet (k : ByteArray) : trieGet (E σ t) k = trieGet t k := rfl
@[simp] theorem E_dataIdOf (n : Nat) : dataIdOf (E σ t) n = dataIdOf t n := rfl
@[simp] theorem E_receiptReceiver (n : Nat) : receiptReceiver (E σ t) n = receiptReceiver t n := rfl
@[simp] theorem E_popN : popN (E σ t) = ((popN t).1, E σ (popN t).2) := by
  unfold popN popV; simp only [E_stack]; cases t.stack.back?.getD (Val.i32 0) <;> rfl
end

/-! ## The `cr` tactic -/

syntax "cr_call" : tactic
macro_rules | `(tactic| cr_call) => `(tactic| first | exact CR_pure _ | exact CR_throw _)

open Lean Elab Tactic Meta in
/-- `intro`, only on propositions. -/
elab "cr_intro" : tactic => do
  let g ← getMainGoal
  unless (← isProp (← g.getType)) do throwError "cr_intro: not a proposition"
  evalTactic (← `(tactic| intro))

syntax "cr_step" : tactic
macro_rules | `(tactic| cr_step) => `(tactic| first
  | contradiction
  | ((with_reducible apply CR_get_bind); intro; simp only [E_stack, E_frames, E_pages, E_globals, E_table,
      E_tableMax, E_elems, E_datas, E_stackRem, E_gas, E_ctx, E_ret, E_balance, E_storageUsage, E_registers,
      E_regUsage, E_logs, E_totalLogLen, E_promises, E_trie, E_actions, E_dataCount, E_subsidized,
      E_real_isSome, E_memBytes, E_readByte, E_readBytes, E_readLE, E_trieGet, E_dataIdOf,
      E_receiptReceiver, E_popN])
  | ((with_reducible apply CR_pure'); rfl)
  | ((with_reducible apply CR_throw'); rfl)
  | ((with_reducible apply CR_set); first | rfl | simp only [E_writeBytes, E_writeByte])
  | ((with_reducible apply CR_modify); intro t; first | rfl | (rcases t with ⟨⟩; rename_i real _; cases real <;> rfl))
  | (with_reducible apply CR_ite _ _ rfl)
  | (with_reducible apply CR_dite _ _ rfl)
  | (with_reducible cr_call)
  | ((with_reducible apply CR_bind); first
      | ((with_reducible apply CR_modify); intro t; first | rfl | (rcases t with ⟨⟩; rename_i real _; cases real <;> rfl))
      | ((with_reducible apply CR_set); first | rfl | simp only [E_writeBytes, E_writeByte])
      | ((with_reducible apply CR_pure'); rfl)
      | (with_reducible cr_call)
      | (with_reducible apply CR_ite _ _ rfl)
      | (with_reducible apply CR_dite _ _ rfl)
      | (with_reducible apply CR_forIn))
  | (with_reducible apply CR_forIn)
  | (split <;> try (rename_i hh; simp only [hh]))
  | cr_intro
  | (simp only []))

macro "cr" : tactic => `(tactic| repeat (any_goals cr_step))

end NearSpecV3.Logged.W
