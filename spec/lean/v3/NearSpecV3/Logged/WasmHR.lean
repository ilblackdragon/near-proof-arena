import NearSpecV3.Logged.WasmHostL

/-!
# Storage host mirrors = originals

`StOK σ t`: the trie store of `t` (if any) is `σ`. `HR σ g y x`: for every such `t`, the mirror `y`
run on the erased state `E dummy t` against the store `g` gives the original's result on `t`
(state erased), and the original's final state still has store `σ`. Rules for binds, `get`/`set`/
`modify`, lifted store-free host code (`HR_liftH`, from `CR`), and the store operations.
-/

namespace NearSpecV3.Logged.W

open NearSpecV3.Wasm NearSpecV3.Wasm.TTN

def StOK (σ : TTN.Store) (t : St) : Prop := ∀ r, t.real = some r → r.store = σ

def finalSt {α : Type} : EStateM.Result String St α → St
  | .ok _ s => s
  | .error _ s => s

structure HR {α : Type} (σ : TTN.Store) (g : NearSpec.Bytes → Option NearSpec.Bytes) (y : HMM α) (x : HM α) :
    Prop where
  h : ∀ t, StOK σ t →
    SM.run g ((y.run).run (E dummy t)) = .ok (toPair (mapSt (E dummy) (x.run t))) ∧ StOK σ (finalSt (x.run t))

section
variable {σ : TTN.Store} {g : NearSpec.Bytes → Option NearSpec.Bytes}

theorem E_of_StOK {t : St} (h : StOK σ t) : E σ t = t := by
  unfold E; cases hr : t.real with
  | none => simp [hr]
  | some r => have := h r hr; simp [hr, ← this]

theorem StOK_E (t : St) : StOK σ (E σ t) := by
  intro r hr; unfold E at hr; cases h : t.real <;> simp [h] at hr; subst hr; rfl

theorem finalSt_mapSt {α : Type} (f : St → St) (r : EStateM.Result String St α) :
    finalSt (mapSt f r) = f (finalSt r) := by cases r <;> rfl

theorem HR_liftH {α : Type} {h : HM α} (h1 : CR dummy h h) (h2 : CR σ h h) : HR σ g (liftH h) h := by
  constructor; intro t ht
  constructor
  · show SM.run g (pure (toPair (h.run (E dummy t)))) = _
    rw [h1.h t]; rfl
  · have := h2.h t
    rw [E_of_StOK ht] at this
    rw [this, finalSt_mapSt]; exact StOK_E _

theorem HR_pure {α : Type} (a : α) : HR σ g (pure a) (pure a) := by
  constructor; intro t ht; exact ⟨rfl, ht⟩

theorem HR_throw {α : Type} (e : String) : HR σ g (throw e : HMM α) (throw e) := by
  constructor; intro t ht; exact ⟨rfl, ht⟩

theorem HR_bind {α β : Type} {y : HMM α} {x : HM α} {f' : α → HMM β} {f : α → HM β}
    (h1 : HR σ g y x) (h2 : ∀ a, HR σ g (f' a) (f a)) : HR σ g (y >>= f') (x >>= f) := by
  constructor; intro t ht
  obtain ⟨r1, p1⟩ := h1.h t ht
  show SM.run g ((ExceptT.bind y f').run.run (E dummy t)) = _ ∧ _
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.run, bind, StateT.bind] at r1 ⊢
  sorry

end

end NearSpecV3.Logged.W
