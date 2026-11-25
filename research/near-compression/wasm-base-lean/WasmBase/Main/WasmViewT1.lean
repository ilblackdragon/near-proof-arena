import WasmBase.Main.TmplWasm
import WasmBase.M2Ctx

/-!
# WasmBase.Main.WasmViewT1 — an explicit Wasm-view parameter record (A-T3 non-vacuity)

A-T2 found that the old `WasmViewParams` was **uninhabited** (`a-t1/lean/PrepScope.lean`:
`encRest_inj` asked for an injective encoding of a type containing the function-typed trie store),
so every theorem over it was vacuous.  After the store-blind restatement (`WasmView` §7,
lane E's S1), this file builds the record T1 runs under and proves it exists, so the problem
cannot recur unnoticed: any future change that makes the structure empty breaks this file.

* `ctxM2` — **the real static context**: the entry kind's function (`start`, or the resolved
  method), the M2 checker `checkModuleM2 cfg p (fi − |imports|)` (the module check every lane A
  segment theorem assumes, `M2Ctx`), packed as a `Ctx` by `M2Ctx.toCtx`; `ctxM2_ok` is `CtxOK`.
  It reads `q.cfg` and `q.method` only, so `ctxOf_blind` is `rfl`.
* `encRestT1` — the remainder through lane E's **store-blind serialisers** (`ViewSer.argsN`, `stN`,
  `confN`, prefix-free `Ser`), tagged by constructor: `encRestT1_blind`, `encRestT1_inj` (injective
  modulo stores: `argsN_eq`, `stN_eq`, `confN_eq`).
* `ccT1` — a `CodeCommit` with root `bdigest (Ser.enc records)`.  The circuit's root is the
  stacked-PCS commitment of the padded matrix, which has no Lean model; any binding commitment
  instantiates the field (its collision event is `CodeCommit.Coll`).
* T1's template heights: CODE 32, FUNC 4 (`t1-template-k13.json`).
* **`wasmViewParams_nonempty : Nonempty WasmViewParams`**.
* `vT1` — lane E's store-blind view `SB.vSB` with lane A's Wasm component `wasmD wasmViewParamsT1`:
  `vT1_blind` (`StoreBlind`), `vT1_clear` (`ClearCall`), `vT1_wasm` (the Wasm premise of
  `SB.e2e_sound_t1_relC_bind` holds with `Bad = Sha384Coll`).  So the store-canonical theorem
  `TmplWasm.segSoundWasmRelC_of` is about a satisfiable set of side conditions.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace WasmBase.WasmViewT1

open NearSpecV3.Wasm hiding P
open NearSpecV3.Wasm.CallCut
open NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.Enc
open NearSpecV3.E2E.SB (setArgs setSt setConf CodeCommit StoreBlind CollOn WStripped vSB)
open WasmBase.WasmView WasmBase.TmplWasm

/-- The function index (`enter`'s `fi`, imports included) an entry kind enters. -/
def entryOf (q : CallArgs) (p : Prepared) : EntK → Option Nat
  | .start _ => p.m.start
  | .method =>
    match resolve p q.method with
    | .ok mi => some mi
    | _ => none

/-- **The static context of an entry**: `checkModuleM2` on the entry's defined-function index. -/
def ctxM2 (q : CallArgs) (p : Prepared) (k : EntK) : Option Ctx :=
  match entryOf q p k with
  | none => none
  | some fi =>
    match h : checkModuleM2 q.cfg p (fi - p.m.imports.size) with
    | some MH => some (M2Ctx.toCtx ⟨q.cfg, p, fi - p.m.imports.size, MH, 0, h⟩)
    | none => none

theorem ctxM2_blind (t : TTN.Store) (q : CallArgs) (p : Prepared) (k : EntK) :
    ctxM2 (setArgs t q) p k = ctxM2 q p k := rfl

set_option synthInstance.maxSize 4096 in
/-- The remainder through the store-blind serialisers, tagged by constructor. -/
def encRestT1 : WRest → ArenaCore.Bytes
  | .air q p k s => 0 :: Ser.enc (argsN q, p, k, stN s)
  | .other w => 1 :: Ser.enc (argsN w.1, confN w.2)

theorem stripSt_eq (s : St) : stripSt s = setSt blankStore s := rfl

set_option synthInstance.maxSize 4096 in
theorem encRestT1_blind (t : TTN.Store) (a : WRest) : encRestT1 (setW t a) = encRestT1 a := by
  cases a with
  | air q p k s => simp only [setW, encRestT1, SB.argsN_setArgs, SB.stN_setSt]
  | other w => simp only [setW, encRestT1, SB.argsN_setArgs, SB.confN_setConf]

set_option synthInstance.maxSize 4096 in
theorem encRestT1_inj (a b : WRest) (h : encRestT1 a = encRestT1 b) : stripW a = stripW b := by
  cases a with
  | air q p k s =>
    cases b with
    | air q' p' k' s' =>
      simp only [encRestT1, List.cons.injEq, true_and] at h
      have e := Ser.pf.inj h
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, rfl, rfl, e4⟩ := e
      have h1 := argsN_eq e1
      have h4 := stN_eq e4
      rw [SB.stripArgs_eq, SB.stripArgs_eq] at h1
      rw [stripSt_eq, stripSt_eq] at h4
      simp only [stripW, setW, h1, h4]
    | other w => simp [encRestT1] at h
  | other w =>
    cases b with
    | air q p k s => simp [encRestT1] at h
    | other w' =>
      simp only [encRestT1, List.cons.injEq, true_and] at h
      have e := Ser.pf.inj h
      simp only [Prod.mk.injEq] at e
      have h1 := argsN_eq e.1
      have h2 := confN_eq e.2
      rw [SB.stripArgs_eq, SB.stripArgs_eq] at h1
      rw [SB.stripConf_eq, SB.stripConf_eq] at h2
      simp only [stripW, setW, h1, h2]

set_option synthInstance.maxSize 4096 in
/-- A record commitment: `bdigest` of the prefix-free encoding of the padded records. -/
def ccT1 : CodeCommit (List (List Nat)) := ⟨fun r => bdigest (Ser.enc r), fun _ => bdigest_length _⟩

/-- **T1's Wasm-view parameters.** -/
def wasmViewParamsT1 : WasmViewParams where
  ctxOf := ctxM2
  ctxOf_blind := ctxM2_blind
  codeC := ccT1
  funcC := ccT1
  hCode := 32
  hFunc := 4
  encRest := encRestT1
  encRest_blind := encRestT1_blind
  encRest_inj := encRestT1_inj

/-- **The Wasm-view parameter structure is inhabited** (A-T2's `wasmViewParams_empty` was about
the old, store-sensitive structure). -/
theorem wasmViewParams_nonempty : Nonempty WasmViewParams := ⟨wasmViewParamsT1⟩

/-- **`CtxOK`** for T1's parameters: the context is for the call's own module and config. -/
theorem ctxM2_ok : CtxOK wasmViewParamsT1 := by
  intro q p k X h
  simp only [wasmViewParamsT1, ctxM2] at h
  split at h
  · cases h
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h

/-- Lane E's store-blind view with lane A's Wasm component. -/
noncomputable def vT1 (lB : NearSpec.Bytes → Nat) (κ : Intake → List NearSpec.Bytes) (stD : StV → NearSpec.Bytes) : ViewImpl :=
  { vSB lB κ stD with wasmD := wasmD wasmViewParamsT1 }

theorem vT1_blind (lB : NearSpec.Bytes → Nat) (κ : Intake → List NearSpec.Bytes) (stD : StV → NearSpec.Bytes) :
    StoreBlind (vT1 lB κ stD) := by
  intro x
  cases x with
  | base c => rfl
  | call I c K q cc =>
    have e := wasmD_set wasmViewParamsT1 blankStore (some (q, cc))
    simp only [Option.map_some, setC] at e
    simp only [ViewImpl.bnd, vT1, vSB, SB.stripR, SB.setR, SB.setArgs_ctx, split, SB.vmSB_blind, e, ViewE.clearE]

theorem vT1_clear (lB : NearSpec.Bytes → Nat) (κ : Intake → List NearSpec.Bytes) (stD : StV → NearSpec.Bytes) :
    ClearCall (vT1 lB κ stD) := fun _ _ _ _ _ _ => rfl

theorem vT1_wasm (lB : NearSpec.Bytes → Nat) (κ : Intake → List NearSpec.Bytes) (stD : StV → NearSpec.Bytes) :
    CollOn WStripped (vT1 lB κ stD).wasmD → Sha384Coll :=
  viewImpl_hwasm wasmViewParamsT1 (vT1 lB κ stD) rfl _ id

#print axioms encRestT1_blind
#print axioms encRestT1_inj
#print axioms wasmViewParams_nonempty
#print axioms ctxM2_ok
#print axioms vT1_blind
#print axioms vT1_clear
#print axioms vT1_wasm

end WasmBase.WasmViewT1
