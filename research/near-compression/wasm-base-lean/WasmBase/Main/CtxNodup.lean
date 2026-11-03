import WasmBase.SpecLemmas
import WasmBase.M2Ctx

/-!
# WasmBase.Main.CtxNodup — the checked function list has no duplicates (E2E M4b, S1)

The boundary view recomputes a caller's checked-function index from its defined function
(`Ctx.kOf fn = X.M.fns.idxOf fn`, `Main/SegRows.lean`), which inverts `Ctx.fnOf` only if
`X.M.fns` has no duplicates (`Main/SegView.lean:kOf_fnOf`).  `ModFacts` does not record it, so
`SegView`'s theorems take `X.M.fns.Nodup` as a hypothesis on `X`; this file discharges it for the
two contexts the proofs are instantiated with:

* `closureFns_nodup`: the call-graph closure only appends a function it does not contain;
* `checkModule_fns`, `checkModuleM2_fns`: both checkers' function list is `closureFns p entry`;
* **`Ctx.ofCheck_fns_nodup`**, **`M2Ctx.toCtx_fns_nodup`**.
-/

namespace WasmBase
open NearSpecV3.Wasm

/-- An invariant of a pure `for … in l` loop: kept by every body step, whether it breaks or not. -/
theorem forIn_list_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, P b → P (f a b).run.value) : ∀ (l : List α) (init : β), P init → P (forIn l init f).run
  | [], init, h0 => by simpa using h0
  | a :: l, init, h0 => by
    rw [List.forIn_cons]
    have := hf a init h0
    cases hfa : f a init with
    | done b => rw [hfa] at this; exact this
    | yield b => rw [hfa] at this; exact forIn_list_inv P f hf l b this

/-- **The closure has no duplicates.** -/
theorem closureFns_nodup (p : Prepared) (entry : Nat) : (closureFns p entry).Nodup := by
  unfold closureFns
  simp
  refine forIn_list_inv (fun st : List Nat × List Nat => st.1.Nodup) _ ?_ _ _ (by simp)
  rintro a ⟨fns, todo⟩ (h : fns.Nodup)
  cases todo with
  | nil => exact h
  | cons fn rest =>
    show (Id.run (forIn (m := Id) ((Option.map (calleesOf p) p.funcs[fn]?).getD []) (fns, rest) _)).1.Nodup
    refine forIn_list_inv (fun st : List Nat × List Nat => st.1.Nodup) _ ?_ _ _ h
    rintro c ⟨fs, td⟩ (hf : fs.Nodup)
    by_cases hc : c ∈ fs
    · simp only [hc, ite_true]; exact hf
    · simp only [hc, ite_false]
      show (fs ++ [c]).Nodup
      rw [List.nodup_append]
      exact ⟨hf, by simp, by intro x hx y hy e; simp at hy; subst hy; subst e; exact hc hx⟩

theorem checkModule_fns {cfg : NearCfg} {p : Prepared} {entry : Nat} {M : ModOut}
    (h : checkModule cfg p entry = some M) : M.fns = closureFns p entry := by
  unfold checkModule at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · simp at h

theorem checkModuleM2_fns {cfg : NearCfg} {p : Prepared} {entry : Nat} {MH : ModOutH}
    (h : checkModuleM2 cfg p entry = some MH) : MH.mod.fns = closureFns p entry := by
  unfold checkModuleM2 at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · simp at h

/-- The base context's function list has no duplicates. -/
theorem Ctx.ofCheck_fns_nodup {cfg : NearCfg} {p : Prepared} {fn : Nat} {M : ModOut} {g0 : Nat}
    (h : checkModule cfg p fn = some M) : (Ctx.ofCheck cfg p fn M g0 h).M.fns.Nodup := by
  show M.fns.Nodup
  rw [checkModule_fns h]; exact closureFns_nodup p fn

/-- The M2 context's function list has no duplicates. -/
theorem M2Ctx.toCtx_fns_nodup (X : M2Ctx) : X.toCtx.M.fns.Nodup := by
  show X.MH.mod.fns.Nodup
  rw [checkModuleM2_fns X.hM]; exact closureFns_nodup X.p X.fn

#print axioms closureFns_nodup
#print axioms Ctx.ofCheck_fns_nodup
#print axioms M2Ctx.toCtx_fns_nodup

end WasmBase
