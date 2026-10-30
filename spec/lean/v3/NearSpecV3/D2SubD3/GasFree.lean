import NearSpecV3.ChunkValidationD2

/-!
# D2 ⊂ D3, step 1: with a `FunctionCall`-free hook the chunk burns no function-call gas

`checkD3` adds a per-chunk cap `out.wasmGas ≤ G_α` that `checkD2` does not have. `wasmGas` is the sum
of the receipts' `gas_burnt_for_function_call` (`AR.gasFC`), and only the `FunctionCall` hook ever
sets it: every other action takes the running `AR` and returns it, `AR.fail` of it, or a record
update that leaves `gasFC` alone. So under a hook that never succeeds on `.fcall` (`d2Hooks`), the
chunk's `wasmGas` is 0 and the cap holds.

`PostE x P` is the postcondition "if `x` succeeds, its value satisfies `P`".
-/

namespace NearSpecV3.D2
open NearSpec NearSpecV3

def PostE {α : Type} (x : Except String α) (P : α → Prop) : Prop := ∀ a, x = .ok a → P a

namespace PostE

theorem pure' {α : Type} {P : α → Prop} {a : α} (h : P a) : PostE (pure a : Except String α) P :=
  fun _ e => by cases e; exact h

theorem throw' {α : Type} {P : α → Prop} (e : String) : PostE (throw e : Except String α) P :=
  fun _ h => by cases h

theorem bind {α β : Type} {x : Except String α} {f : α → Except String β} {Q : α → Prop}
    {P : β → Prop} (hx : PostE x Q) (hf : ∀ a, Q a → PostE (f a) P) : PostE (x >>= f) P := by
  intro b h
  cases hx' : x with
  | error e => rw [hx'] at h; cases h
  | ok a => rw [hx'] at h; exact hf a (hx a hx') b h

theorem bind_any {α β : Type} {x : Except String α} {f : α → Except String β} {P : β → Prop}
    (hf : ∀ a, PostE (f a) P) : PostE (x >>= f) P :=
  bind (Q := fun _ => True) (fun _ _ => trivial) fun a _ => hf a

theorem ite' {α : Type} {P : α → Prop} (c : Prop) [Decidable c] {x y : Except String α}
    (hx : PostE x P) (hy : PostE y P) : PostE (if c then x else y) P := by
  split <;> assumption

theorem mono {α : Type} {x : Except String α} {P Q : α → Prop} (h : PostE x Q)
    (hq : ∀ a, Q a → P a) : PostE x P := fun a e => hq a (h a e)

end PostE

/-- A hook that preserves the running `gas_burnt_for_function_call` whenever it succeeds. -/
def GasFree (h : ActionHooks) : Prop :=
  ∀ c st ar b, PostE (h.functionCall c st ar b) fun p => p.2.gasFC = ar.gasFC

theorem d2Hooks_gasFree : GasFree d2Hooks := fun _ _ _ _ _ h => by cases h

/-- Closers for one call of a function already proved to preserve `gasFC` (extended below). -/
syntax "post_close" : tactic
macro_rules | `(tactic| post_close) => `(tactic| fail "post_close")

/-- Walk a `do` block whose every exit returns the running `AR` (`res`), `res.fail` or a
`{ res with … }` update that keeps `gasFC`. -/
macro "post_walk" : tactic => `(tactic|
  repeat' (first
    | (exact PostE.throw' _)
    | post_close
    | (with_reducible apply PostE.pure'; first | rfl | simp only [AR.fail])
    | (with_reducible apply PostE.bind_any; intro)
    | (with_reducible apply PostE.ite' _ ?_ ?_)
    | (dsimp only)
    | (split)))


section
variable (c : ActCtx) (st : ActSt) (res : AR)

theorem actTransfer_gasFC (dep : Nat) : PostE (actTransfer c st res dep) fun p => p.2.gasFC = res.gasFC := by
  unfold actTransfer; post_walk
theorem actDeleteAccount_gasFC (b : Bytes) : PostE (actDeleteAccount c st res b) fun p => p.2.gasFC = res.gasFC := by
  unfold actDeleteAccount; post_walk
theorem actAddKey_gasFC (pk : PublicKey) (ak : AK) : PostE (actAddKey c st res pk ak) fun p => p.2.gasFC = res.gasFC := by
  unfold actAddKey; post_walk
theorem actDeleteKey_gasFC (pk : PublicKey) : PostE (actDeleteKey c st res pk) fun p => p.2.gasFC = res.gasFC := by
  unfold actDeleteKey; post_walk
theorem actStake_gasFC (s : Nat) (pk : PublicKey) : PostE (actStake c st res s pk) fun p => p.2.gasFC = res.gasFC := by
  unfold actStake; post_walk
theorem actDeploy_gasFC (code : Bytes) : PostE (actDeploy c st res code) fun p => p.2.gasFC = res.gasFC := by
  unfold actDeploy; post_walk
theorem actToGasKey_gasFC (pk : PublicKey) (d : Nat) : PostE (actToGasKey c st res pk d) fun p => p.2.gasFC = res.gasFC := by
  unfold actToGasKey; post_walk
theorem actFromGasKey_gasFC (pk : PublicKey) (d : Nat) : PostE (actFromGasKey c st res pk d) fun p => p.2.gasFC = res.gasFC := by
  unfold actFromGasKey; post_walk
theorem actCreateAccount_gasFC : PostE (actCreateAccount c st res) fun p => p.2.gasFC = res.gasFC := by
  unfold actCreateAccount; post_walk
theorem actDelegate_gasFC (d : Delegate) : PostE (actDelegate c st res d) fun p => p.2.gasFC = res.gasFC := by
  unfold actDelegate; post_walk
end


macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actTransfer_gasFC _ _ _ _) fun _ h => ?_; exact h.trans rfl))
macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actDeleteAccount_gasFC _ _ _ _) fun _ h => ?_; exact h.trans rfl))
macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actAddKey_gasFC _ _ _ _ _) fun _ h => ?_; exact h.trans rfl))
macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actDeleteKey_gasFC _ _ _ _) fun _ h => ?_; exact h.trans rfl))
macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actStake_gasFC _ _ _ _ _) fun _ h => ?_; exact h.trans rfl))
macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actDeploy_gasFC _ _ _ _) fun _ h => ?_; exact h.trans rfl))
macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actToGasKey_gasFC _ _ _ _ _) fun _ h => ?_; exact h.trans rfl))
macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actFromGasKey_gasFC _ _ _ _ _) fun _ h => ?_; exact h.trans rfl))
macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actCreateAccount_gasFC _ _ _) fun _ h => ?_; exact h.trans rfl))
macro_rules | `(tactic| post_close) => `(tactic| (refine PostE.mono (actDelegate_gasFC _ _ _ _) fun _ h => ?_; exact h.trans rfl))

/-- **Every action keeps `gasFC = 0`** under a gas-free hook. -/
theorem applyAction_gasFC (h : ActionHooks) (hg : GasFree h) (c : ActCtx) (st : ActSt) (act : Act) :
    PostE (applyAction h c st act) fun p => p.2.gasFC = 0 := by
  unfold applyAction
  have hfc := hg
  post_walk
  all_goals first
    | (refine PostE.mono (hfc _ _ _ _) fun _ h => ?_; exact h.trans rfl)
    | post_close
    | exact PostE.throw' _
    | skip

example (c : ActCtx) (st : ActSt) (d : Nat) (g : Nat) :
    PostE (actTransfer c st { gasBurnt := g, gasUsed := g, compute := g, ok := true, newReceipts := [], proposals := [], tokensBurnt := 0 } d)
      fun p => p.snd.gasFC = 0 := by
  refine PostE.mono (actTransfer_gasFC _ _ _ _) fun _ h => ?_
  exact h.trans rfl

end NearSpecV3.D2
