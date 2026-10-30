import NearSpecV3.Successor.TierMono
import NearSpecV3.Successor.TierStoreAuth

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

`EngineRef base x y`: the engine-level relation. Where the legacy main transition `x` rejects,
the recorder `y` rejects with the same string; where `x` returns an output inside the legacy
size bound, `y` returns the same output. Legacy exclusions, and legacy outputs over the size bound
(the shell excludes those), constrain nothing.

`EngineAgree cfg`: `EngineRef` holds on every main-transition input the shell builds (the store is
`mkHStore merged`, the trie is the revealed pre-state).

**Shell theorem (proved):** `checkD2CoreGWith_legacy_recorder` —
`EngineAgree cfg → O4Witness w → Refines (checkD2CoreG …) (checkD2CoreGWith (recorderDriver cfg) …)`.

**Tier theorem (proved, conditional on the engine):** `relSuccessor_runtimeLimits_storageResolution_of`.

The engine agreement itself is the open part; see the end of the file and
`docs/evidence/lean-chunk-completion/tier-refinement-w12/README.md` §7.
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

/-! ## The engine relation -/

/-- The legacy shell's size bound (`legacyDriver.sizeOk`). -/
def legacySizeOk (base removals : Nat) : Bool := base + 2000 * removals ≤ 4000000

/-- Engine-level refinement: a legacy reject is a recorder reject with the same string; a legacy
output inside the size bound is the recorder's output. -/
def EngineRef (base : Nat) (x y : Except String MainOutD2) : Prop :=
  (∀ e, x = .error e → isExclusion e = false → y = .error e) ∧
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
      (applyNewChunkD2 (D3.d3Hooks cfg) p e (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg)
      (StorageExecution.run cfg p e (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg false .coldPartial)

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
    (h : EngineRef base x y) (m m' : String) (hm : isExclusion m = true)
    {K K' : MainOutD2 → Except String β} (hK : ∀ out, Refines (K out) (K' out)) :
    Refines (x >>= fun out => check (legacySizeOk base out.cdRemovals) m >>= fun _ => K out)
      (y >>= fun out => check true m' >>= fun _ => K' out) := by
  cases hx : x with
  | error e =>
    cases he : isExclusion e
    · rw [h.1 e hx he]; exact Refines.refl _
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
    | (refine Refines.engine_bind (‹EngineAgree _› _ _ _ _ _ _ _ _ rfl) _ _ (by ood_tac) fun _ => ?_)
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

theorem checkD2CoreWithObs_legacy_recorder (cfg : Wasm.NearCfg) (hE : EngineAgree cfg)
    (c w : Bytes) (hw : O4Witness w) (g : Option Nat) :
    Refines (checkD2CoreWithObs legacyDriver (D3.d3Hooks cfg) true c w g)
      (checkD2CoreWithObs (recorderDriver cfg) (D3.d3Hooks cfg) true c w g) := by
  unfold checkD2CoreWithObs
  simp only [legacyDriver, recorderDriver, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    decodeWitnessFileV_of_not_c w hw.1]
  refine Refines.bind' rfl fun cl => ?_
  refine Refines.bind_ok fun ⟨sw, codes⟩ hd => ?_
  refine Refines.check_bind_right _ _ (decide_eq_true (hw.2 sw codes hd)) ?_
  simp only [Bool.not_false, ↓reduceIte]
  o4_lockstep

theorem checkD2CoreWith_legacy_recorder (cfg : Wasm.NearCfg) (hE : EngineAgree cfg)
    (c w : Bytes) (hw : O4Witness w) (g : Option Nat) :
    Refines (checkD2CoreWith legacyDriver (D3.d3Hooks cfg) true c w g)
      (checkD2CoreWith (recorderDriver cfg) (D3.d3Hooks cfg) true c w g) :=
  Refines.map _ (checkD2CoreWithObs_legacy_recorder cfg hE c w hw g)

set_option maxHeartbeats 16000000 in
/-- **O4, shell level.** The genesis-capable shell at the legacy driver (`checkD2CoreG`) is refined
by the same shell at the recorder driver, given the engine agreement, on witness files in the
original format whose codes fit one code response. -/
theorem checkD2CoreGWith_legacy_recorder (cfg : Wasm.NearCfg) (hE : EngineAgree cfg)
    (c w : Bytes) (hw : O4Witness w) (g : Option Nat) :
    Refines (checkD2CoreG (D3.d3Hooks cfg) true c w g)
      (checkD2CoreGWith (recorderDriver cfg) (D3.d3Hooks cfg) true c w g) := by
  have hW := checkD2CoreWith_legacy_recorder cfg hE c w hw g
  rw [← legacy_genesis_eq]
  unfold checkD2CoreGWith
  simp only [legacyDriver, recorderDriver, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
    decodeWitnessFileV_of_not_c w hw.1]
  simp only [legacyDriver, recorderDriver, Bool.false_eq_true, ↓reduceIte] at hW
  refine Refines.bind' rfl fun cl => ?_
  refine Refines.bind_ok fun ⟨sw, codes⟩ hd => ?_
  refine Refines.check_bind_right _ _ (decide_eq_true (hw.2 sw codes hd)) ?_
  simp only [Bool.not_false, ↓reduceIte]
  o4_lockstep

/-! ## Tier level -/

/-- The two tiers run the same Wasm configuration. -/
theorem runtimeLimits_storageResolution_wasm :
    (Tier.cfg .runtimeLimits).wasm = (Tier.cfg .storageResolution).wasm := rfl

/-- The `.runtimeLimits` checker is the genesis-capable shell at the legacy driver. -/
theorem tier_runtimeLimits_eq (c w : Bytes) :
    Tier.checker .runtimeLimits c w =
      checkD2CoreG (D3.d3Hooks (Tier.cfg .storageResolution).wasm) true c w (some maxGasBurnt) := rfl

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
  rw [tier_runtimeLimits_eq, tier_storageResolution_eq]
  exact checkD2CoreGWith_legacy_recorder _ hE c w hw _

/-- The verdict-level reading. -/
theorem verdict_runtimeLimits_storageResolution_of
    (hE : EngineAgree (Tier.cfg .storageResolution).wasm) (c w : Bytes) (hw : O4Witness w)
    (hd : (checkVerdict (Tier.checker .runtimeLimits) c w).inDomain = true) :
    checkVerdict (Tier.checker .storageResolution) c w = checkVerdict (Tier.checker .runtimeLimits) c w :=
  Refines.verdict (relSuccessor_runtimeLimits_storageResolution_of hE c w hw) hd

#print axioms checkD2CoreWithObs_legacy_recorder
#print axioms checkD2CoreGWith_legacy_recorder
#print axioms relSuccessor_runtimeLimits_storageResolution_of
#print axioms verdict_runtimeLimits_storageResolution_of

end NearSpecV3.Successor
