import NearSpecV3.Successor.TierMono
import NearSpecV3.Successor.TierStoreAuth
import NearSpecV3.Logged.D3LSpec

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O4 — storage resolution: the legacy engine against the recorder engine

`.runtimeLimits` and `.storageResolution` differ in one flag, `storageResolution`. It switches the
validation shell's driver from `legacyDriver` (main transition `D2.applyNewChunkD2` with the
action hooks `D3.d3Hooks cfg`, merged-value size bound `w.size`) to `recorderDriver cfg`
(main transition `StorageExecution.run`, the chunk-scoped recorder). The driver change touches
four places of the shell:

| phase | legacy driver | recorder driver |
|---|---|---|
| decode | `decodeWitnessFile` | `decodeWitnessFileV` (also the `near-arena-cwitness-v3` file format) |
| decode | — | `w.code_response_size` exclusion (cold-fetched code > 64 MiB) |
| apply | `applyNewChunkD2 (d3Hooks cfg)` | `StorageExecution.run cfg … false .coldPartial` |
| outputs | `w.size` exclusion: `base + 2000 · removals ≤ 4,000,000` | none |

Everything else is the same term.

## Statement

`O4Witness w`: the witness file is in the original `near-arena-witness-v3` format (the legacy
driver does not read the compressed format; it rejects such a file with `decode: wrong witness
format`) and its contract codes fit one `ContractCodeResponse` (the recorder driver excludes the
others before deciding anything; the legacy driver would exclude them too, by `w.size`, but only
after the main transition, so a legacy *reject* found earlier would not be preserved). Both are
conditions on the witness file alone.

**The counterexample, and the fix (2026-10-30).** Without a storage precondition the step is false
on 26 nearcore-valid chunks (`storage-limit-fixtures`, nearcore `ok`): every narrower legacy tier
rejected them with `MissingTrieValue` (or `StorageInconsistentState(MissingTrieValue)`) because it
runs the receipts nearcore postpones at `main_storage_proof_size_soft_limit`, while
`.storageResolution` accepts them. The legacy side was wrong. The narrower legacy tiers now report
a legacy reject on a witness above the legacy storage bound (`legacyMergedBytes w > 4,000,000`) as
the `w.size` exclusion (`Config.withStorageExclusion`); the signed statement of record is
unchanged (it already decides those errors with the recorder engine, `withReshardHandover`).
`checkD2CoreG_ok_bound` proves the legacy shell never accepts above that bound, so above it every
narrower legacy tier result is an exclusion.

`EngineRef base x y`: the engine-level relation. Where the legacy main transition `x` rejects on
a witness within the storage bound (`base ≤ 4,000,000`), the recorder `y` rejects with the same
string; where `x` returns an output inside the legacy size bound, `y` returns the same output.
Legacy exclusions, rejects above the bound and outputs over the size bound constrain nothing.

`EngineAgree cfg`: `EngineRef` holds on every main-transition input the shell builds (the store is
`mkHStore merged`, the trie is the revealed pre-state), with both outputs' observation-only fields
erased (`obsClear`; finding G0: the recorder reports `committed`/`compute`, the legacy engine does
not, so without the erasure `EngineAgree` was false on every legacy accept).

**Shell theorem (proved):** `checkD2CoreGWith_legacy_recorder` —
`EngineAgree cfg → O4Witness w → legacyMergedBytes w ≤ 4,000,000 →
Refines (checkD2CoreG …) (checkD2CoreGWith (recorderDriver cfg) …)`.

**Tier theorem (proved, conditional on the engine):** `relSuccessor_runtimeLimits_storageResolution_of`
— `EngineAgree → O4Witness w → Refines (.runtimeLimits c w) (.storageResolution c w)`, no size
premise (above the bound the left is an exclusion).

The engine agreement itself is open; see `docs/evidence/lean-chunk-completion/tier-refinement-w12/README.md` §7
for its decomposition and the one known gap (`EngineAgree` is false if ContractData removals alone
push the recorder over the soft limit before a legacy reject: `merged ≤ 4,000,000 <
merged + 2000 · removals`; no corpus or fixture case does this).
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The witness-file domain -/

/-- The `near-arena-cwitness-v3` prefix test of `decodeWitnessFileV`. -/
def isCWitnessFile (w : Bytes) : Bool :=
  w.take (witnessTagC.length + 4) == ([22, 0, 0, 0] ++ witnessTagC)

/-- O4's condition on the witness file: the original format, and contract codes that fit one
`ContractCodeResponse`. -/
def O4Witness (w : Bytes) : Prop :=
  isCWitnessFile w = false ∧
    ∀ sw codes, decodeWitnessFile w = .ok (sw, codes) →
      codeResponseBytes codes ≤ maxContractCodeResponseBytes

theorem decodeWitnessFileV_of_not_c (w : Bytes) (h : isCWitnessFile w = false) :
    decodeWitnessFileV w = decodeWitnessFile w := by
  unfold decodeWitnessFileV
  unfold isCWitnessFile at h
  simp only [h, Bool.false_eq_true, ↓reduceIte]

/-! ## Observation fields (finding G0, 2026-10-30)

`MainOutD2` carries three observation-only fields (`committed`, `compute`, `detail`). The legacy
engine leaves them `none`; the recorder engine reports `committed := some …` and
`compute := some …` on every accept. So the first statement of `EngineRef` (`y = .ok out`) could
never hold on a legacy accept, and `EngineAgree` as first stated was false outright (the conditional
theorems were vacuous). No check reads these fields: the shell copies them into its `Observable`,
which the `Unit`-valued checkers discard. `checkD2CoreWith_clearObs` and
`checkD2CoreGWith_clearObs` prove that erasing them (`ExecutionDriver.clearObs`) leaves both
`Unit`-valued shells unchanged, and the engine relation is now stated on `obsClear`-ed outputs. -/

/-- The main-transition output with its observation-only fields erased. -/
def obsClear (o : MainOutD2) : MainOutD2 := { o with committed := none, compute := none, detail := none }

/-- The driver whose main transition reports no observation fields. -/
def ExecutionDriver.clearObs (d : ExecutionDriver) : ExecutionDriver :=
  { d with apply := fun h p e t vu ps rs txs cg => (d.apply h p e t vu ps rs txs cg).map obsClear }

theorem except_map_bind_obs {β : Type} (x : Except String MainOutD2) (K : MainOutD2 → Except String β) :
    (x.map obsClear >>= K) = (x >>= fun o => K (obsClear o)) := by cases x <;> rfl

theorem umap_bind {α β : Type} (x : Except String α) {f g : α → Except String β}
    (h : ∀ a, (f a).map (fun _ => ()) = (g a).map (fun _ => ())) :
    (x >>= f).map (fun _ => ()) = (x >>= g).map (fun _ => ()) := by
  cases x with
  | error e => rfl
  | ok a => exact h a

theorem umap_pure {β : Type} (a b : β) :
    (pure a : Except String β).map (fun _ => ()) = (pure b : Except String β).map (fun _ => ()) := rfl

theorem umap_ite_join {β : Type} (c : Prop) [Decidable c] (x₁ x₂ : Except String Unit)
    {K K' : Unit → Except String β} (hK : ∀ v, (K v).map (fun _ => ()) = (K' v).map (fun _ => ())) :
    (if c then x₁ >>= K else x₂ >>= K).map (fun _ => ()) =
      (if c then x₁ >>= K' else x₂ >>= K').map (fun _ => ()) := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact umap_bind _ hK
  · simp only [hc, ite_false]; exact umap_bind _ hK

theorem umap_ite_skip {β : Type} (c : Prop) [Decidable c] (x : Except String Unit)
    {K K' : Except String β} (hK : K.map (fun _ => ()) = K'.map (fun _ => ())) :
    (if c then x >>= (fun _ => K) else K).map (fun _ => ()) =
      (if c then x >>= (fun _ => K') else K').map (fun _ => ()) := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact umap_bind _ fun _ => hK
  · simp only [hc, ite_false]; exact hK

theorem umap_ite {β : Type} (c : Prop) [Decidable c] {t t' e e' : Except String β}
    (ht : t.map (fun _ => ()) = t'.map (fun _ => ())) (he : e.map (fun _ => ()) = e'.map (fun _ => ())) :
    (if c then t else e).map (fun _ => ()) = (if c then t' else e').map (fun _ => ()) := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact ht
  · simp only [hc, ite_false]; exact he

macro "umap_walk" : tactic => `(tactic|
  repeat (first
    | (exact umap_pure _ _)
    | (with_reducible rfl)
    | (refine umap_bind _ fun _ => ?_)
    | (refine umap_ite_join _ _ _ fun _ => ?_)
    | (refine umap_ite_skip _ _ ?_)
    | (refine umap_ite _ ?_ ?_)
    | (split <;> (try dsimp only)) ))

set_option maxHeartbeats 16000000 in
theorem checkD2CoreWith_clearObs (d : ExecutionDriver) (hooks : ActionHooks) (a : Bool) (c w : Bytes)
    (g : Option Nat) :
    checkD2CoreWith d.clearObs hooks a c w g = checkD2CoreWith d hooks a c w g := by
  unfold checkD2CoreWith checkD2CoreWithObs
  simp only [ExecutionDriver.clearObs, except_map_bind_obs, obsClear]
  umap_walk

set_option maxHeartbeats 16000000 in
theorem checkD2CoreGWith_clearObs (d : ExecutionDriver) (hooks : ActionHooks) (a : Bool) (c w : Bytes)
    (g : Option Nat) :
    checkD2CoreGWith d.clearObs hooks a c w g = checkD2CoreGWith d hooks a c w g := by
  unfold checkD2CoreGWith
  rw [checkD2CoreWith_clearObs]
  simp only [ExecutionDriver.clearObs, except_map_bind_obs, obsClear]
  rfl

/-! ## The engine relation -/

/-- The legacy shell's size bound (`legacyDriver.sizeOk`). -/
def legacySizeOk (base removals : Nat) : Bool := base + 2000 * removals ≤ 4000000

/-- Engine-level refinement: a legacy reject is a recorder reject with the same string; a legacy
output inside the size bound is the recorder's output. -/
def EngineRef (base : Nat) (x y : Except String MainOutD2) : Prop :=
  (∀ e, x = .error e → isExclusion e = false → base ≤ legacyStorageBound → y = .error e) ∧
    (∀ out, x = .ok out → legacySizeOk base out.cdRemovals = true → y = .ok out)

/-- The merged witness size the legacy shell bounds. -/
def mergedBytes (merged : List Bytes) : Nat := (merged.map List.length).foldl (· + ·) 0

/-- **The engine obligation of O4**: on every main-transition input the shells build, the recorder
engine refines the legacy engine (`EngineRef`). -/
def EngineAgree (cfg : Wasm.NearCfg) : Prop :=
  ∀ (merged : List Bytes) (p : Prims) (e : Env) (vu : Option ValidatorUpdateFacts)
    (ps : List (Bytes × Nat)) (rs : List Rcpt) (txs : List (TxD2 × Bool)) (cg : Congestion),
    e.store = mkHStore merged →
    EngineRef (mergedBytes merged)
      ((applyNewChunkD2 (D3.d3Hooks cfg) p e (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg).map obsClear)
      ((StorageExecution.run cfg p e (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg false .coldPartial).map
        obsClear)

/-! ## Engine phase E0: the legacy engine is its logged mirror

`Logged.R_applyNewChunkD2` (with `HooksR_d3` and `HInv_mkHStore`) says the legacy main transition on
the revealed pre-state is the logged mirror `applyNewChunkD2L (d3HooksL cfg)` run against the
witness store. The recorder engine is built from the same logged operations (`StorageExecution.logged`),
so the remaining engine obligation is stated against the mirror (`EngineAgreeL`). -/

/-- The engine obligation against the logged mirror of the legacy engine. -/
def EngineAgreeL (cfg : Wasm.NearCfg) : Prop :=
  ∀ (merged : List Bytes) (p : Prims) (e : Env) (vu : Option ValidatorUpdateFacts)
    (ps : List (Bytes × Nat)) (rs : List Rcpt) (txs : List (TxD2 × Bool)) (cg : Congestion),
    e.store = mkHStore merged →
    EngineRef (mergedBytes merged)
      ((Logged.LM.ev e.store e.preRoot (applyNewChunkD2L (D3.d3HooksL cfg) p e vu ps rs txs cg)).map obsClear)
      ((StorageExecution.run cfg p e (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg false .coldPartial).map
        obsClear)

/-- **E0.** The legacy main transition on the shell's inputs is its logged mirror. -/
theorem applyNewChunkD2_eq_logged (cfg : Wasm.NearCfg) (merged : List Bytes) (p : Prims) (e : Env)
    (vu : Option ValidatorUpdateFacts) (ps : List (Bytes × Nat)) (rs : List Rcpt) (txs : List (TxD2 × Bool))
    (cg : Congestion) (he : e.store = mkHStore merged) :
    applyNewChunkD2 (D3.d3Hooks cfg) p e (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg =
      Logged.LM.ev e.store e.preRoot (applyNewChunkD2L (D3.d3HooksL cfg) p e vu ps rs txs cg) := by
  have hs : Logged.HInv e.store := by rw [he]; exact Logged.HInv_mkHStore merged
  have h := Logged.R_applyNewChunkD2 (s := e.store) (root := e.preRoot) (D3.d3Hooks cfg) (D3.d3HooksL cfg)
    e.store (Logged.HooksR_d3 cfg) hs p e vu ps rs txs cg
  unfold Logged.R at h
  rw [Except.map_id] at h
  exact h

theorem engineAgree_of_logged (cfg : Wasm.NearCfg) (h : EngineAgreeL cfg) : EngineAgree cfg := by
  intro merged p e vu ps rs txs cg he
  rw [applyNewChunkD2_eq_logged cfg merged p e vu ps rs txs cg he]
  exact h merged p e vu ps rs txs cg he

/-! ## Engine phase E1 (primitive): a logged read is the mirror's read

Every storage read of the recorder engine goes through `StorageExecution.logged`, which runs a
logged-mirror program against the witness store and only adds the read keys to the recorder. -/

/-- The recorder after a logged program's reads. -/
def recordReads (e : Env) (keys : List Bytes) (rec : Wasm.TTN.Recorder) : Wasm.TTN.Recorder :=
  keys.foldl (fun acc h => match e.codeOf h with
    | some bytes => acc.record (D3.toBA h) bytes.length
    | none => acc) rec

/-- **E1.** `logged x` returns the mirror's result `LM.ev e.store e.preRoot x` and changes only the
recorder. -/
theorem logged_run {α : Type} (x : Logged.LM α) (r : StorageExecution.Recording) (e : Env) :
    (StorageExecution.logged x).run r e =
      (Logged.LM.ev e.store e.preRoot x).map fun a =>
        (a, { r with recorder := recordReads e (Logged.SM.reads (hGet e.store) (x e.preRoot)) r.recorder }) := by
  unfold StorageExecution.logged
  simp only [Logged.SM.runR_eq, Logged.LM.ev]
  rfl

/-! ## The engine simulation relation (foundation for the remaining phases)

`SimE e P x y`: from every recorder state satisfying the invariant `P`, the recorder computation
`y` returns the logged mirror's value `LM.ev e.store e.preRoot x` (in a state satisfying `P`), or,
where the mirror rejects, the same error; a mirror exclusion constrains nothing. -/

open StorageExecution in
/-- `φ` maps the mirror's values to the recorder's (as `Logged.R`'s `φ`: the mirror's overlays
carry a dummy trie, the recorder's the revealed pre-state). -/
def SimE {α β : Type} (e : Env) (P : Recording → Prop) (φ : α → β) (x : Logged.LM α) (y : M β) : Prop :=
  ∀ r, P r → match Logged.LM.ev e.store e.preRoot x with
    | .ok a => ∃ r', (y.run r) e = .ok (φ a, r') ∧ P r'
    | .error err => isExclusion err = true ∨ (y.run r) e = .error err

namespace SimE
open StorageExecution

theorem pure {α β : Type} {e : Env} {P : Recording → Prop} (φ : α → β) (a : α) :
    SimE e P φ (Pure.pure a) (Pure.pure (φ a) : M β) := fun r hr => ⟨r, rfl, hr⟩

theorem bind {α α' β β' : Type} {e : Env} {P : Recording → Prop} {φ : α → α'} {ψ : β → β'}
    {x : Logged.LM α} {y : M α'} {f : α → Logged.LM β} {g : α' → M β'}
    (hxy : SimE e P φ x y) (hfg : ∀ a, SimE e P ψ (f a) (g (φ a))) :
    SimE e P ψ (x >>= f) (y >>= g) := by
  intro r hr
  have h1 := hxy r hr
  rw [Logged.LM.ev_bind]
  cases hx : Logged.LM.ev e.store e.preRoot x with
  | error err =>
    rw [hx] at h1
    rcases h1 with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show (y.run r e >>= fun p => (g p.1).run p.2 e) = _
      rw [h]; rfl
  | ok a =>
    rw [hx] at h1
    obtain ⟨r', hy, hr'⟩ := h1
    have h2 := hfg a r' hr'
    show match Logged.LM.ev e.store e.preRoot (f a) with
      | .ok b => ∃ r'', (y.run r e >>= fun p => (g p.1).run p.2 e) = .ok (ψ b, r'') ∧ P r''
      | .error err => isExclusion err = true ∨ (y.run r e >>= fun p => (g p.1).run p.2 e) = .error err
    rw [hy]
    exact h2

/-- A logged read: the invariant must survive the recorder update. -/
theorem logged {α : Type} {e : Env} {P : Recording → Prop} (x : Logged.LM α)
    (hP : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder }) :
    SimE e P id x (StorageExecution.logged x) := by
  intro r hr
  rw [logged_run]
  cases Logged.LM.ev e.store e.preRoot x with
  | error err => exact Or.inr rfl
  | ok a => exact ⟨_, rfl, hP r _ hr⟩

/-- A bookkeeping-only state update (pipeline, observation) that keeps the invariant. -/
theorem modify {e : Env} {P : Recording → Prop} (f : Recording → Recording)
    (hP : ∀ r, P r → P (f r)) :
    SimE e P id (Pure.pure ()) (MonadState.modifyGet fun r => ((), f r) : M Unit) := by
  intro r hr
  exact ⟨f r, rfl, hP r hr⟩

theorem ite {α β : Type} {e : Env} {P : Recording → Prop} {φ : α → β} (c : Prop) [Decidable c]
    {x x' : Logged.LM α} {y y' : M β} (h : c → SimE e P φ x y) (h' : ¬c → SimE e P φ x' y') :
    SimE e P φ (if c then x else x') (if c then y else y') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h hc
  · simp only [hc, ite_false]; exact h' hc

theorem foldlM {γ α β : Type} {e : Env} {P : Recording → Prop} {φ : α → β}
    {f : α → γ → Logged.LM α} {g : β → γ → M β} (hfg : ∀ a c, SimE e P φ (f a c) (g (φ a) c)) :
    ∀ (l : List γ) (a : α), SimE e P φ (l.foldlM f a) (l.foldlM g (φ a))
  | [], a => SimE.pure φ a
  | c :: l, a => by
    simp only [List.foldlM_cons]
    exact SimE.bind (hfg a c) fun a' => foldlM hfg l a'

end SimE

/-- The top-level bridge: a simulation of the whole main transition from the initial recorder state
gives the engine obligation (`EngineAgreeL`, hence `EngineAgree` by `engineAgree_of_logged`). -/
theorem engineAgreeL_of_simE (cfg : Wasm.NearCfg) (P : StorageExecution.Recording → Prop)
    (hinit : P { observe := cfg.observeDetail })
    (h : ∀ (merged : List Bytes) (p : Prims) (e : Env) (vu : Option ValidatorUpdateFacts)
      (ps : List (Bytes × Nat)) (rs : List Rcpt) (txs : List (TxD2 × Bool)) (cg : Congestion),
      e.store = mkHStore merged →
      SimE e P obsClear (applyNewChunkD2L (D3.d3HooksL cfg) p e vu ps rs txs cg)
        (obsClear <$> StorageExecution.applyNewChunkD2 { globalActions := false, codePolicy := .coldPartial } cfg p e
          (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg)) :
    EngineAgreeL cfg := by
  intro merged p e vu ps rs txs cg he
  have hs := h merged p e vu ps rs txs cg he _ hinit
  have hmap : ∀ {β γ : Type} (f : β → γ) (y : StorageExecution.M β) (r : StorageExecution.Recording),
      (f <$> y).run r e = (y.run r e).map fun q => (f q.1, q.2) := by
    intro β γ f y r
    simp only [StateT.run_map]
    rfl
  rw [hmap] at hs
  refine ⟨fun err hx hne _ => ?_, fun out hx _ => ?_⟩
  · cases hl : Logged.LM.ev e.store e.preRoot (applyNewChunkD2L (D3.d3HooksL cfg) p e vu ps rs txs cg) with
    | ok a => rw [hl] at hx; cases hx
    | error err' =>
      rw [hl] at hx hs
      cases hx
      rcases hs with hs | hs
      · rw [hne] at hs; cases hs
      · unfold StorageExecution.run
        cases hy : (StorageExecution.applyNewChunkD2 { globalActions := false, codePolicy := .coldPartial } cfg p e
          (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg).run { observe := cfg.observeDetail } e with
        | ok q => rw [hy] at hs; cases hs
        | error err'' => rw [hy] at hs; cases hs; rfl
  · cases hl : Logged.LM.ev e.store e.preRoot (applyNewChunkD2L (D3.d3HooksL cfg) p e vu ps rs txs cg) with
    | error err' => rw [hl] at hx; cases hx
    | ok a =>
      rw [hl] at hx hs
      cases hx
      obtain ⟨r', hy, _⟩ := hs
      unfold StorageExecution.run
      cases hy' : (StorageExecution.applyNewChunkD2 { globalActions := false, codePolicy := .coldPartial } cfg p e
          (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg).run { observe := cfg.observeDetail } e with
      | error err'' => rw [hy'] at hy; cases hy
      | ok q =>
        rw [hy'] at hy
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hy
        simp only [Except.map, hy.1]

#print axioms engineAgreeL_of_simE
#print axioms SimE.bind
#print axioms SimE.logged
#print axioms SimE.foldlM

/-! ## Lockstep steps for the driver change -/

theorem Refines.bind_ok {α β : Type} {x : Except String α} {f g : α → Except String β}
    (hfg : ∀ a, x = .ok a → Refines (f a) (g a)) : Refines (x >>= f) (x >>= g) := by
  cases hx : x with
  | error e => exact Refines.refl _
  | ok a => exact hfg a hx

theorem Refines.throw_bind'' {α β : Type} (e : String) (f g : α → Except String β) :
    Refines ((throw e : Except String α) >>= f) ((throw e : Except String α) >>= g) :=
  Or.inl rfl

/-- A guard on the right only, known to pass. -/
theorem Refines.check_bind_right {β : Type} {x : Except String β} (b : Bool) (m : String) (hb : b = true)
    {g : Unit → Except String β} (h : Refines x (g ())) : Refines x (check b m >>= g) := by
  subst hb; exact h

/-- The main-transition step: the legacy `apply` followed by the legacy size guard, against the
recorder `apply` followed by the recorder's trivial guard. -/
theorem Refines.engine_bind {β : Type} {base : Nat} {x y : Except String MainOutD2}
    (h : EngineRef base x y) (hb : base ≤ legacyStorageBound) (m m' : String) (hm : isExclusion m = true)
    {K K' : MainOutD2 → Except String β} (hK : ∀ out, Refines (K out) (K' out)) :
    Refines (x >>= fun out => check (legacySizeOk base out.cdRemovals) m >>= fun _ => K out)
      (y >>= fun out => check true m' >>= fun _ => K' out) := by
  cases hx : x with
  | error e =>
    cases he : isExclusion e
    · rw [h.1 e hx he hb]; exact Refines.refl _
    · exact Or.inr ⟨e, rfl, he⟩
  | ok out =>
    cases hs : legacySizeOk base out.cdRemovals
    · exact Or.inr ⟨m, by simp [check, hs], hm⟩
    · rw [h.2 out hx hs]
      change Refines (check (legacySizeOk base out.cdRemovals) m >>= fun _ => K out)
        (check true m' >>= fun _ => K' out)
      rw [hs]; exact hK out


/-- The lockstep walk of `refines_lockstep` plus the main-transition step `Refines.engine_bind`. -/
macro "o4_lockstep" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact Refines.refl _)
    | (exact Refines.throw_bind _ _ _)
    | (exact Refines.throw_bind'' _ _ _)
    | (with_reducible assumption)
    | (refine Refines.engine_bind (‹EngineAgree _› _ _ _ _ _ _ _ _ rfl) ‹_› _ _ (by ood_tac) fun _ => ?_)
    | ((refine Refines.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Refines.ite_bind_join _ _ _ fun _ => ?_)
    | (refine Refines.ite_bind_skip _ _ ?_)
    | (refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine Refines.bind (by with_reducible assumption) fun _ => ?_); try dsimp only)
    | (refine Refines.check_bind_left _ _ (by ood_tac) fun _ => ?_)
    | (refine Refines.check_bind_right _ _ rfl ?_)
    | ((refine Refines.bind (Refines.check_pure _ _ (by ood_tac)) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind (Refines.forIn_congr _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

/-- `legacyMergedBytes` on a decoded witness. -/
theorem legacyMergedBytes_of_decode {w sw : Bytes} {codes : List Bytes} {sw' : StateWitnessD2}
    (hd : decodeWitnessFile w = .ok (sw, codes)) (hdw : decodeStateWitnessD2 sw = .ok sw') :
    legacyMergedBytes w = mergedBytes (sw'.main.values ++ codes) := by
  simp only [legacyMergedBytes, hd, hdw, mergedBytes]

theorem checkD2CoreWithObs_legacy_recorder (cfg : Wasm.NearCfg) (hE : EngineAgree cfg)
    (c w : Bytes) (hw : O4Witness w) (hB : legacyMergedBytes w ≤ legacyStorageBound) (g : Option Nat) :
    Refines (checkD2CoreWithObs legacyDriver.clearObs (D3.d3Hooks cfg) true c w g)
      (checkD2CoreWithObs (recorderDriver cfg).clearObs (D3.d3Hooks cfg) true c w g) := by
  unfold checkD2CoreWithObs
  simp only [ExecutionDriver.clearObs, legacyDriver, recorderDriver, Bool.false_eq_true, ↓reduceIte,
    Bool.not_true, decodeWitnessFileV_of_not_c w hw.1]
  refine Refines.bind' rfl fun cl => ?_
  refine Refines.bind_ok fun ⟨sw, codes⟩ hd => ?_
  refine Refines.check_bind_right _ _ (decide_eq_true (hw.2 sw codes hd)) ?_
  simp only [Bool.not_false, ↓reduceIte]
  refine Refines.bind' rfl fun _ => ?_
  refine Refines.bind_ok fun sw' hdw => ?_
  have hb : mergedBytes (sw'.main.values ++ codes) ≤ legacyStorageBound := by
    rw [← legacyMergedBytes_of_decode hd hdw]; exact hB
  o4_lockstep

theorem checkD2CoreWith_legacy_recorder (cfg : Wasm.NearCfg) (hE : EngineAgree cfg)
    (c w : Bytes) (hw : O4Witness w) (hB : legacyMergedBytes w ≤ legacyStorageBound) (g : Option Nat) :
    Refines (checkD2CoreWith legacyDriver (D3.d3Hooks cfg) true c w g)
      (checkD2CoreWith (recorderDriver cfg) (D3.d3Hooks cfg) true c w g) := by
  rw [← checkD2CoreWith_clearObs legacyDriver, ← checkD2CoreWith_clearObs (recorderDriver cfg)]
  exact Refines.map _ (checkD2CoreWithObs_legacy_recorder cfg hE c w hw hB g)

set_option maxHeartbeats 16000000 in
/-- **O4, shell level.** The genesis-capable shell at the legacy driver (`checkD2CoreG`) is refined
by the same shell at the recorder driver, given the engine agreement, on witness files in the
original format whose codes fit one code response. -/
theorem checkD2CoreGWith_legacy_recorder (cfg : Wasm.NearCfg) (hE : EngineAgree cfg)
    (c w : Bytes) (hw : O4Witness w) (hB : legacyMergedBytes w ≤ legacyStorageBound) (g : Option Nat) :
    Refines (checkD2CoreG (D3.d3Hooks cfg) true c w g)
      (checkD2CoreGWith (recorderDriver cfg) (D3.d3Hooks cfg) true c w g) := by
  have hW : Refines (checkD2CoreWith legacyDriver.clearObs (D3.d3Hooks cfg) true c w g)
      (checkD2CoreWith (recorderDriver cfg).clearObs (D3.d3Hooks cfg) true c w g) := by
    rw [checkD2CoreWith_clearObs, checkD2CoreWith_clearObs]
    exact checkD2CoreWith_legacy_recorder cfg hE c w hw hB g
  rw [← legacy_genesis_eq, ← checkD2CoreGWith_clearObs legacyDriver,
    ← checkD2CoreGWith_clearObs (recorderDriver cfg)]
  unfold checkD2CoreGWith
  simp only [ExecutionDriver.clearObs, legacyDriver, recorderDriver, Bool.false_eq_true, ↓reduceIte,
    Bool.not_true, decodeWitnessFileV_of_not_c w hw.1]
  simp only [ExecutionDriver.clearObs, legacyDriver, recorderDriver, Bool.false_eq_true, ↓reduceIte] at hW
  refine Refines.bind' rfl fun cl => ?_
  refine Refines.bind_ok fun ⟨sw, codes⟩ hd => ?_
  refine Refines.check_bind_right _ _ (decide_eq_true (hw.2 sw codes hd)) ?_
  simp only [Bool.not_false, ↓reduceIte]
  refine Refines.bind' rfl fun _ => ?_
  refine Refines.bind_ok fun sw' hdw => ?_
  have hb : mergedBytes (sw'.main.values ++ codes) ≤ legacyStorageBound := by
    rw [← legacyMergedBytes_of_decode hd hdw]; exact hB
  o4_lockstep

/-! ## Above the storage bound the legacy shell never accepts

Its `w.size` guard is necessary for acceptance on both the genesis and the non-genesis path, and its
base is `legacyMergedBytes`. So above the bound every legacy result is an error, and the narrower
legacy tiers' `withStorageExclusion` makes it an exclusion. -/

/-- `x` never returns a value. -/
def NoAcc {α : Type} (x : Except String α) : Prop := ∀ a, x ≠ .ok a

theorem NoAcc.bind {α β : Type} {x : Except String α} {f : α → Except String β}
    (h : ∀ a, x = .ok a → NoAcc (f a)) : NoAcc (x >>= f) := by
  intro b hb
  cases hx : x with
  | error e => rw [hx] at hb; cases hb
  | ok a => rw [hx] at hb; exact h a hx b hb

theorem NoAcc.throw {α : Type} (e : String) : NoAcc (throw e : Except String α) := by
  intro a h; cases h

theorem NoAcc.error {α : Type} (e : String) : NoAcc (Except.error e : Except String α) := by
  intro a h; cases h

theorem NoAcc.size_bind {β : Type} {base r : Nat} (hbig : legacyStorageBound < base) (m : String)
    (f : Unit → Except String β) :
    NoAcc (check (decide (base + 2000 * r ≤ 4000000)) m >>= f) := by
  have : decide (base + 2000 * r ≤ 4000000) = false := by
    unfold legacyStorageBound at hbig; simp only [decide_eq_false_iff_not]; omega
  rw [this]; exact NoAcc.bind fun a h => by cases h

theorem NoAcc.ite {α : Type} (c : Prop) [Decidable c] {x y : Except String α}
    (hx : c → NoAcc x) (hy : ¬c → NoAcc y) : NoAcc (if c then x else y) := by
  by_cases h : c
  · simp only [h, ite_true]; exact hx h
  · simp only [h, ite_false]; exact hy h

theorem NoAcc.map {α β : Type} {x : Except String α} (f : α → β) (h : NoAcc x) : NoAcc (x.map f) := by
  intro b hb
  cases hx : x with
  | error e => rw [hx] at hb; cases hb
  | ok a => exact h a hx

macro "noacc_walk" : tactic => `(tactic|
  repeat (first
    | (exact NoAcc.size_bind ‹_› _ _)
    | (exact NoAcc.throw _)
    | (exact NoAcc.error _)
    | (with_reducible assumption)
    | (refine NoAcc.bind fun _ _ => ?_)
    | (refine NoAcc.ite _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

theorem checkD2CoreWithObs_legacy_noacc (h : ActionHooks) (c w : Bytes) (g : Option Nat)
    (hB : legacyStorageBound < legacyMergedBytes w) :
    NoAcc (checkD2CoreWithObs legacyDriver h true c w g) := by
  unfold checkD2CoreWithObs
  simp only [legacyDriver, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  refine NoAcc.bind fun cl _ => ?_
  refine NoAcc.bind fun ⟨sw, codes⟩ hd => ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine NoAcc.bind fun _ _ => ?_
  refine NoAcc.bind fun sw' hdw => ?_
  have hbig : legacyStorageBound < mergedBytes (sw'.main.values ++ codes) := by
    rw [← legacyMergedBytes_of_decode hd hdw]; exact hB
  noacc_walk

set_option maxHeartbeats 16000000 in
theorem checkD2CoreG_noacc (h : ActionHooks) (c w : Bytes) (g : Option Nat)
    (hB : legacyStorageBound < legacyMergedBytes w) :
    NoAcc (checkD2CoreG h true c w g) := by
  have hW : NoAcc (checkD2CoreWith legacyDriver h true c w g) :=
    NoAcc.map _ (checkD2CoreWithObs_legacy_noacc h c w g hB)
  rw [← legacy_genesis_eq]
  unfold checkD2CoreGWith
  simp only [legacyDriver, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hW ⊢
  refine NoAcc.bind fun cl _ => ?_
  refine NoAcc.bind fun ⟨sw, codes⟩ hd => ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine NoAcc.bind fun _ _ => ?_
  refine NoAcc.bind fun sw' hdw => ?_
  have hbig : legacyStorageBound < mergedBytes (sw'.main.values ++ codes) := by
    rw [← legacyMergedBytes_of_decode hd hdw]; exact hB
  noacc_walk

/-- **The legacy genesis-capable shell accepts only within the storage bound.** -/
theorem checkD2CoreG_ok_bound (h : ActionHooks) (c w : Bytes) (g : Option Nat)
    (hok : checkD2CoreG h true c w g = .ok ()) : legacyMergedBytes w ≤ legacyStorageBound := by
  rcases Nat.lt_or_ge legacyStorageBound (legacyMergedBytes w) with hB | hB
  · exact absurd hok (checkD2CoreG_noacc h c w g hB ())
  · exact hB

/-! ## Tier level -/


/-- The two tiers run the same Wasm configuration. -/
theorem runtimeLimits_storageResolution_wasm :
    (Tier.cfg .runtimeLimits).wasm = (Tier.cfg .storageResolution).wasm := rfl

/-- The `.runtimeLimits` checker is the genesis-capable shell at the legacy driver, behind the
storage-proof precondition. -/
theorem tier_runtimeLimits_eq (c w : Bytes) :
    Tier.checker .runtimeLimits c w = withStorageExclusion
      (checkD2CoreG (D3.d3Hooks (Tier.cfg .storageResolution).wasm) true c w (some maxGasBurnt)) c w := rfl

/-- Above the storage bound the storage precondition excludes every legacy result. -/
theorem withStorageExclusion_big {r : Except String Unit} {c w : Bytes} (hr : NoAcc r)
    (hB : legacyStorageBound < legacyMergedBytes w) :
    ∃ e, withStorageExclusion r c w = .error e ∧ isExclusion e = true := by
  cases r with
  | ok u => exact absurd rfl (hr u)
  | error e =>
    cases he : isExclusion e
    · exact ⟨legacyStorageExclusion, by simp [withStorageExclusion, he, storageCrossed_of_big hB], by decide⟩
    · exact ⟨e, by simp [withStorageExclusion, he], he⟩

/-- The storage precondition only turns rejects into an exclusion, so it keeps a refinement. -/
theorem withStorageExclusion_refines {r y : Except String Unit} (c w : Bytes) (h : Refines r y) :
    Refines (withStorageExclusion r c w) y := by
  rcases withStorageExclusion_cases r c w with hs | ⟨e, _, _, _, hs⟩
  · rw [hs]; exact h
  · rw [hs]; exact Or.inr ⟨_, rfl, by decide⟩


/-- The `.storageResolution` checker is the same shell at the recorder driver. -/
theorem tier_storageResolution_eq (c w : Bytes) :
    Tier.checker .storageResolution c w =
      checkD2CoreGWith (recorderDriver (Tier.cfg .storageResolution).wasm)
        (D3.d3Hooks (Tier.cfg .storageResolution).wasm) true c w (some maxGasBurnt) := rfl

/-- **O4, tier level, given the engine agreement.** `.runtimeLimits ⊑ .storageResolution` on every
witness file in the original format whose codes fit one code response: wherever the legacy-engine
tier accepts or rejects, the storage-resolution tier returns exactly the same result. -/
theorem relSuccessor_runtimeLimits_storageResolution_of
    (hE : EngineAgree (Tier.cfg .storageResolution).wasm) (c w : Bytes) (hw : O4Witness w) :
    Refines (Tier.checker .runtimeLimits c w) (Tier.checker .storageResolution c w) := by
  rw [tier_runtimeLimits_eq]
  by_cases hB : legacyMergedBytes w ≤ legacyStorageBound
  · refine withStorageExclusion_refines c w ?_
    rw [tier_storageResolution_eq]
    exact checkD2CoreGWith_legacy_recorder _ hE c w hw hB _
  · obtain ⟨e, he, hx⟩ := withStorageExclusion_big (checkD2CoreG_noacc _ c w _ (Nat.lt_of_not_le hB))
      (Nat.lt_of_not_le hB)
    exact Or.inr ⟨e, he, hx⟩

/-- The verdict-level reading. -/
theorem verdict_runtimeLimits_storageResolution_of
    (hE : EngineAgree (Tier.cfg .storageResolution).wasm) (c w : Bytes) (hw : O4Witness w)
    (hd : (checkVerdict (Tier.checker .runtimeLimits) c w).inDomain = true) :
    checkVerdict (Tier.checker .storageResolution) c w = checkVerdict (Tier.checker .runtimeLimits) c w :=
  Refines.verdict (relSuccessor_runtimeLimits_storageResolution_of hE c w hw) hd

#print axioms engineAgree_of_logged
#print axioms logged_run
#print axioms checkD2CoreWithObs_legacy_recorder
#print axioms checkD2CoreGWith_legacy_recorder
#print axioms checkD2CoreG_ok_bound
#print axioms relSuccessor_runtimeLimits_storageResolution_of
#print axioms verdict_runtimeLimits_storageResolution_of

end NearSpecV3.Successor
