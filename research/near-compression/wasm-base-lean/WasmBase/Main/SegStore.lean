import NearSpecV3.Logged.WasmRun
import NearSpecV3.E2E.StoreBlind

/-!
# WasmBase.Main.SegStore — a Wasm segment keeps the store function (A-T3)

Lane E's store-canonical obligation `SB.TmplRelC` asks a Wasm leaf to produce a **canonical**
output configuration (every store is the context's `sf I`).  The Wasm machine never writes the
trie store function `TTN.RealStore.store` (storage writes go to the overlay), so a segment from a
state with store `σ` ends in a state with store `σ`:

* `step_resOK` — one interpreter step from a state with store `σ` (`Logged.W.StOK σ`) has every
  result state with store `σ` (`ResOK σ`): a non-storage step commutes with the store map
  (`Logged.W.E_step`), a storage host call keeps it (`Logged.W.callHostL_spec`, with the byte-list
  store `gOf σ` that agrees with `σ`, `gOf_agrees`);
* **`seg_setSt`** — `setSt σ s = s → seg cfg p n s = .cont sN → setSt σ sN = sN`;
* `enter_setSt` — the same for a function entry (`Logged.W.E_enter`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace WasmBase.SegStore

open NearSpecV3.Wasm NearSpecV3.Logged.W
open NearSpecV3.E2E.SB (setSt setRes)

/-- `ByteArray.toList`'s loop, in closed form. -/
theorem toList_loop (bs : ByteArray) :
    ∀ n i r, bs.size - i = n → ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro n
  induction n with
  | zero =>
    intro i r h
    rw [ByteArray.toList.loop.eq_1]
    have : ¬ i < bs.size := by omega
    rw [if_neg this]
    have hd : bs.data.toList.drop i = [] := by
      apply List.drop_eq_nil_of_le
      simp only [Array.length_toList]
      exact Nat.le_of_not_lt this
    rw [hd, List.append_nil]
  | succ n ih =>
    intro i r h
    rw [ByteArray.toList.loop.eq_1]
    have hi : i < bs.size := by omega
    rw [if_pos hi, ih (i + 1) _ (by omega)]
    have hl : i < bs.data.toList.length := by simpa using hi
    rw [List.drop_eq_getElem_cons hl]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    congr 2
    simp only [ByteArray.get!, Array.getElem_toList]
    rw [getElem!_pos bs.data i hi]

theorem toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  show ByteArray.toList.loop bs 0 [] = _
  rw [toList_loop bs _ 0 [] rfl]
  simp

/-- A byte-list store answering as `σ`. -/
def gOf (σ : TTN.Store) : NearSpec.Bytes → Option NearSpec.Bytes :=
  fun l => (σ (TTN.toBA' l)).map ByteArray.toList

theorem toBA'_toList (b : ByteArray) : TTN.toBA' b.toList = b := by
  rw [toList_eq]; rfl

theorem gOf_agrees (σ : TTN.Store) : TTN.StoreAgrees σ (gOf σ) := by
  intro h
  simp only [gOf, toBA'_toList, Option.map_map]
  cases σ h with
  | none => rfl
  | some b => simp only [Option.map_some, Function.comp_apply, toBA'_toList]

theorem setSt_eq_E (σ : TTN.Store) (s : St) : setSt σ s = E σ s := rfl

theorem stOK_of (σ : TTN.Store) {s : St} (h : setSt σ s = s) : StOK σ s := by
  rw [StOK_iff_E, ← setSt_eq_E]; exact h

theorem of_stOK (σ : TTN.Store) {s : St} (h : StOK σ s) : setSt σ s = s := by
  rw [setSt_eq_E]; exact E_of_StOK h

/-- **One step keeps the store.** -/
theorem step_resOK (cfg : NearCfg) (p : Prepared) {σ : TTN.Store} {s : St} (h : StOK σ s) :
    ResOK σ (step cfg p s) := by
  cases hsp : stepPre p s with
  | none =>
    have e := E_step (σ := σ) cfg p hsp
    rw [E_of_StOK h] at e
    exact e.symm
  | some q =>
    obtain ⟨s1, name⟩ := q
    rw [step_of_stepPre cfg p s s1 name hsp]
    have hs1 : StOK σ s1 := by
      have e := @E_stepPre σ s p
      rw [E_of_StOK h, hsp] at e
      simp only [Option.map_some] at e
      have e2 : s1 = E σ s1 := by injection e with e; injection e
      rw [e2]; exact StOK_E _
    exact (callHostL_spec (gOf_agrees σ) hs1 name (stepPre_storage hsp)).2

/-- **A segment keeps the store.** -/
theorem seg_setSt (cfg : NearCfg) (p : Prepared) {σ : TTN.Store} :
    ∀ (n : Nat) {s sN : St}, setSt σ s = s → NearSpecV3.Wasm.seg cfg p n s = .cont sN →
      setSt σ sN = sN
  | 0, s, sN, hs, h => by
    simp only [NearSpecV3.Wasm.seg, Res.cont.injEq] at h
    subst h; exact hs
  | n + 1, s, sN, hs, h => by
    simp only [NearSpecV3.Wasm.seg] at h
    have hr := step_resOK cfg p (stOK_of σ hs)
    generalize hst : step cfg p s = r at h hr
    cases r with
    | cont s' =>
      have hs' : setSt σ s' = s' := by
        unfold ResOK mapRes at hr; injection hr
      exact seg_setSt cfg p n hs' h
    | fin _ => cases h
    | abort _ _ => cases h
    | unmodeled _ => cases h

theorem setRes_eq_mapRes (σ : TTN.Store) (r : Res) : setRes σ r = mapRes (E σ) r := by
  cases r <;> rfl

/-- **A function entry keeps the store.** -/
theorem enter_setSt (p : Prepared) (fi : Nat) {σ : TTN.Store} {s : St} (hs : setSt σ s = s) :
    setRes σ (enter p s fi) = enter p s fi := by
  rw [setRes_eq_mapRes, ← E_enter (σ := σ), ← setSt_eq_E, hs]

#print axioms toList_eq
#print axioms gOf_agrees
#print axioms step_resOK
#print axioms seg_setSt
#print axioms enter_setSt

end WasmBase.SegStore
