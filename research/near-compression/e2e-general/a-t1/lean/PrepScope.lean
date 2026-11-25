import WasmBase.Main.WasmViewT1

/-!
# A-T2 PREP scoping: the Wasm view's parameters were uninhabited (kernel-checked finding)

**Status after A-T3 (2026-11-25).** The finding stands for any encoder that sees stores
(`encRest_total_empty` below).  `WasmView.WasmViewParams` was restated store-blind (lane E's
soundness fix S1: `encRest_blind`, `encRest_inj` modulo stores), and the structure is now
inhabited by T1's record (`WasmViewT1.wasmViewParams_nonempty`, checked at the end of this file).

Checked with `lake env lean` against the built `WasmBase` package (outside every lake target, as
lane I's `StmtEval.lean`); no definition of the repository changes.

`WasmBase.WasmView.WasmViewParams` asks for an **injective** byte encoder
`encRest : WRest → Bytes` of the Wasm component's remainder (`encRest_inj`).  The remainder
`WRest.other (q, cc)` contains the whole query `q : CallArgs`, and `q.real.store` is a
`TTN.Store = ByteArray → Option ByteArray` — a function on an infinite type.  By Cantor's
argument there is no injection from such a function space into the countable `Bytes`, so:

* `wasmViewParams_empty : WasmViewParams → False` — no parameter record exists;
* every theorem of `WasmView` / `TmplWasm` quantified over `Pv : WasmViewParams` (`wasmD_binding`,
  `viewImpl_hwasm`, `segSoundWasmRel_of`, `wasmHolds_honest`, ...) is vacuously true: the honest
  non-vacuity results are about a parameter record that cannot be built;
* the same argument applies to every commitment of a component that carries a `VmQ`
  (`= CallArgs`): `vmD_coll : ∀ V : ViewImpl, Coll V.vmD` — the `hvm : Coll V.vmD → Bad` premise
  of lane E's `viewImpl_binding_bad` can only be met with a provable `Bad`.

This is why PREP (`.pre → preConf q`) cannot bind the code through the `.pre` record's only
non-constant field, `vmCtxDigest = bdigest (encRest (.other (q, .pre)))`: the encoder it would have
to open does not exist.  The fix is a statement change (the remainder must not carry the
function-typed store, or the binding must be stated on a domain of finitely supported stores);
see `../README.md` §9.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace WasmBase.PrepScope

open NearSpecV3.Wasm NearSpecV3.Wasm.CallCut
open NearSpecV3.E2E.Bnd (ViewImpl Coll)
open WasmBase.WasmView

/-- **Cantor**: no injection from `α → Bool` into `α`. -/
theorem cantor_no_inj {α : Type} (f : (α → Bool) → α) (hf : ∀ a b, f a = f b → a = b) : False := by
  classical
  let D : α → Bool := fun x => decide (¬ ∃ g, f g = x ∧ g x = true)
  by_cases h : ∃ g, f g = f D ∧ g (f D) = true
  · obtain ⟨g, hg, hgx⟩ := h
    have hgD : g = D := hf g D hg
    rw [hgD] at hgx
    exact (of_decide_eq_true hgx) ⟨D, rfl, hgx⟩
  · exact h ⟨D, rfl, decide_eq_true h⟩

/-- Bytes into byte arrays, injectively. -/
def toBA (l : ArenaCore.Bytes) : ByteArray := ⟨⟨l⟩⟩

theorem toBA_inj {a b : ArenaCore.Bytes} (h : toBA a = toBA b) : a = b := by
  have := congrArg (fun x : ByteArray => x.data.toList) h
  simpa [toBA] using this

/-- A store that answers exactly on the set `b`. -/
def storeOf (b : ByteArray → Bool) : TTN.Store := fun x => if b x then some .empty else none

theorem storeOf_inj {b b' : ByteArray → Bool} (h : storeOf b = storeOf b') : b = b' := by
  funext x
  have hx := congrFun h x
  simp only [storeOf] at hx
  cases hb : b x <;> cases hb' : b' x <;> simp_all

/-- The query `q0` with its store replaced. -/
def qWith (q0 : CallArgs) (b : ByteArray → Bool) : CallArgs :=
  { q0 with real := { q0.real with store := storeOf b } }

theorem qWith_inj (q0 : CallArgs) {b b' : ByteArray → Bool} (h : qWith q0 b = qWith q0 b') :
    b = b' := by
  have := congrArg (fun q : CallArgs => q.real.store) h
  exact storeOf_inj this

/-- **No injective remainder encoder exists** (given any query, e.g. T1's): the A-T2 form of
`encRest_inj`, which made the A-T2 `WasmViewParams` empty. -/
theorem encRest_total_empty_of (q0 : CallArgs) (encRest : WRest → ArenaCore.Bytes)
    (encRest_inj : ∀ a b, encRest a = encRest b → a = b) : False :=
  cantor_no_inj (fun b => toBA (encRest (.other (qWith q0 b, .pre)))) (by
    intro b b' h
    have h1 := encRest_inj _ _ (toBA_inj h)
    have h2 : (qWith q0 b, CallConf.pre) = (qWith q0 b', CallConf.pre) := WRest.other.inj h1
    exact qWith_inj q0 (congrArg Prod.fst h2))

/-- A query (any will do). -/
def q0 : CallArgs :=
  { cfg := pv86, code := .empty, method := "", ctx := {},
    real := { store := fun _ => none, root := .empty } }

/-- **A total-injective remainder encoder is impossible** (A-T2's `wasmViewParams_empty`). -/
theorem encRest_total_empty (encRest : WRest → ArenaCore.Bytes)
    (encRest_inj : ∀ a b, encRest a = encRest b → a = b) : False :=
  encRest_total_empty_of q0 encRest encRest_inj

/-- **Every `vmAcc` commitment collides**: `VmV = List (VmQ × Run)` carries the store, and `vmD`
maps it into `Bytes`. -/
theorem vmD_coll_of (q0 : CallArgs) (r0 : Run) (V : ViewImpl) : Coll V.vmD := by
  classical
  by_cases hc : Coll V.vmD
  · exact hc
  · exfalso
    apply cantor_no_inj (fun b => toBA (V.vmD [(qWith q0 b, r0)]))
    intro b b' h
    have hv := toBA_inj h
    by_cases he : ([(qWith q0 b, r0)] : List (CallArgs × Run)) = [(qWith q0 b', r0)]
    · have := congrArg (fun l : List (CallArgs × Run) => (l.headD (q0, r0)).1) he
      exact qWith_inj q0 this
    · exact absurd ⟨_, _, he, hv⟩ hc

/-- **Every `vmAcc` commitment of every view collides.** -/
theorem vmD_coll (V : ViewImpl) : Coll V.vmD := vmD_coll_of q0 (.line "") V

end WasmBase.PrepScope

#print axioms WasmBase.PrepScope.encRest_total_empty_of
#print axioms WasmBase.PrepScope.encRest_total_empty
-- A-T3: the store-blind structure is inhabited
#print axioms WasmBase.WasmViewT1.wasmViewParams_nonempty
#print axioms WasmBase.PrepScope.vmD_coll_of
#print axioms WasmBase.PrepScope.vmD_coll
