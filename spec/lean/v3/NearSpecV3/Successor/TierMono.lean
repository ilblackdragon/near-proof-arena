import NearSpecV3.Successor.TierProofs
import NearSpecV3.Successor.GenesisOverlap

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 — tier refinement (`relSuccessor_*_mono`)

Configuration-level refinement lemmas (`checkSuccessor_segment_mono`, `checkSuccessor_gas_mono`,
`checkSuccessor_genesis_mono`), the named tier pairs they prove outright, the resharding driver on
the whole-state shells, the reduction of each wide tier's inclusion in `.allFeatures` to named
obligations, and the list of those obligations (end of file). The verdict-level reading of every
`Refines` is `Tier.verdict_of_refines`: where the lower tier decides, the higher tier returns the
same verdict.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## The genesis overlap as a refinement -/

theorem checkD2CoreWith_refines_GWith (d : ExecutionDriver) (hd : d.resharding = false)
    (h : ActionHooks) (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWith d h a c w g) (checkD2CoreGWith d h a c w g) := by
  rcases checkD2CoreGWith_overlap d hd h a c w g with he | he
  · rw [he]; exact Refines.refl _
  · right
    refine ⟨notGenesisError, ?_, by decide⟩
    unfold checkD2CoreWith
    rw [he]
    rfl

theorem checkD2Core_refines_G (h : ActionHooks) (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2Core h a c w g) (checkD2CoreG h a c w g) :=
  checkD2CoreWith_refines_GWith legacyDriver rfl h a c w g

/-! ## The resharding driver on the whole-state shells

`reshardingDriver` is `recorderDriver` with `resharding := true` (which lifts `c.same_layout` and
`c.no_split_gate` in `checkD2CoreWithObs`) and a real `splitApply`. Its `implicitKind` is still the
signed `applyOldChunk`, so `splitApply` is unreachable on these shells. -/

theorem Refines.ok_bind {α β : Type} (a : α) {f g : α → Except String β} (h : Refines (f a) (g a)) :
    Refines ((Except.ok a : Except String α) >>= f) ((Except.ok a : Except String α) >>= g) := h

/-- `refines_lockstep` plus the reduction of a bind on a known `ok` value. -/
macro "refines_lockstep'" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact Refines.refl _)
    | (exact Refines.throw_bind _ _ _)
    | (with_reducible assumption)
    | ((with_reducible refine Refines.ok_bind _ ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine Refines.bind (by with_reducible assumption) fun _ => ?_); try dsimp only)
    | (refine Refines.check_bind_left _ _ (by ood_tac) fun _ => ?_)
    | ((refine Refines.bind (Refines.check_pure _ _ (by ood_tac)) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

theorem checkD2CoreWithObs_resharding_mono (d : ExecutionDriver) (hr : d.resharding = false)
    (hik : d.implicitKind = fun _ _ _ => .ok .applyOldChunk)
    (sa' : PTrie → Bytes → RetainMode → Except String Bytes)
    (h : ActionHooks) (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWithObs d h a c w g)
      (checkD2CoreWithObs { d with resharding := true, splitApply := sa' } h a c w g) := by
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  dsimp only at hr hik
  subst hr hik
  unfold checkD2CoreWithObs
  dsimp only
  simp only [Bool.not_false, Bool.not_true, ↓reduceIte]
  refines_lockstep'

theorem checkD2CoreWith_resharding_mono (d : ExecutionDriver) (hr : d.resharding = false)
    (hik : d.implicitKind = fun _ _ _ => .ok .applyOldChunk)
    (sa' : PTrie → Bytes → RetainMode → Except String Bytes)
    (h : ActionHooks) (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWith d h a c w g)
      (checkD2CoreWith { d with resharding := true, splitApply := sa' } h a c w g) :=
  Refines.map _ (checkD2CoreWithObs_resharding_mono d hr hik sa' h a c w g)

theorem checkD2CoreGWith_resharding_mono (d : ExecutionDriver) (hr : d.resharding = false)
    (hik : d.implicitKind = fun _ _ _ => .ok .applyOldChunk)
    (sa' : PTrie → Bytes → RetainMode → Except String Bytes)
    (h : ActionHooks) (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreGWith d h a c w g)
      (checkD2CoreGWith { d with resharding := true, splitApply := sa' } h a c w g) := by
  have hW := checkD2CoreWith_resharding_mono d hr hik sa' h a c w g
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, bl, ik, sa⟩ := d
  dsimp only at hr hik hW
  subst hr hik
  unfold checkD2CoreGWith
  dsimp only
  refines_lockstep'

theorem checkD2CoreGWith_reshardingDriver_mono (cfg : Wasm.NearCfg) (globals : Bool)
    (policy : CodeWitnessPolicy) (seg : Bool) (h : ActionHooks) (a : Bool) (c w : Bytes)
    (g : Option Nat) :
    Refines (checkD2CoreGWith { recorderDriver cfg globals policy with segmentUnbounded := seg } h a c w g)
      (checkD2CoreGWith { reshardingDriver cfg globals policy with segmentUnbounded := seg } h a c w g) :=
  checkD2CoreGWith_resharding_mono _ rfl rfl splitRootE h a c w g

/-- `.curveHosts ⊑ .resharding` on every claim whose segment contains a genesis block (both tiers
then run the genesis-capable shell, and the resharding driver only adds lifts there). The
non-genesis half is `ReshardCoreExtendsWith` below, an open obligation. -/
theorem relSuccessor_resharding_mono_genesis (c w : Bytes) (hg : segmentHasGenesis c = true) :
    Refines (Tier.checker .curveHosts c w) (Tier.checker .resharding c w) := by
  unfold Tier.checker checkSuccessor
  simp only [Tier.cfg, signedCfg, hg, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    Bool.true_or, Bool.or_true]
  exact checkD2CoreGWith_reshardingDriver_mono _ _ _ _ _ _ _ _ _

/-! ## Configuration-level lemmas -/

/-- Lifting `c.segment` never changes a decided verdict, at any configuration. -/
theorem checkSuccessor_segment_mono (cfg : ProtocolCfg) (c w : Bytes) :
    Refines (checkSuccessor cfg c w) (checkSuccessor { cfg with segmentUnbounded := true } c w) := by
  unfold checkSuccessor
  dsimp only
  split
  · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
    · exact Refines.map _ (checkReshardCoreObs_segment_mono _ _ _ _ _ _)
    · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · exact checkD2CoreGWith_segment_mono _ _ _ _ _ _
        · exact checkD2CoreWith_segment_mono _ _ _ _ _ _
      · exact Refines.refl _
  · exact Refines.refl _

/-- Lifting the serialized-witness bound to the compressed-size bound (Gate B) never changes a
decided verdict, at any configuration. -/
theorem checkSuccessor_witness_mono (cfg : ProtocolCfg) (c w : Bytes) :
    Refines (checkSuccessor cfg c w) (checkSuccessor { cfg with witnessUnbounded := true } c w) := by
  unfold checkSuccessor
  dsimp only
  split
  · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
    · exact Refines.map _ (checkReshardCoreObs_witness_mono _ _ _ _ _ _)
    · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · exact checkD2CoreGWith_witness_mono _ _ _ _ _ _
        · exact checkD2CoreWith_witness_mono _ _ _ _ _ _
      · exact Refines.refl _
  · exact Refines.refl _

/-- Lifting the `numShards ≤ 64` layout bound (Gate B) never changes a decided verdict. -/
theorem checkSuccessor_layout_mono (cfg : ProtocolCfg) (c w : Bytes) :
    Refines (checkSuccessor cfg c w) (checkSuccessor { cfg with layoutUnbounded := true } c w) := by
  unfold checkSuccessor
  dsimp only
  split
  · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
    · exact Refines.map _ (checkReshardCoreObs_layout_mono _ _ _ _ _ _)
    · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · exact checkD2CoreGWith_layout_mono _ _ _ _ _ _
        · exact checkD2CoreWith_layout_mono _ _ _ _ _ _
      · exact Refines.refl _
  · exact Refines.refl _

/-- Weakening the per-chunk gas bound never changes a decided verdict, at any configuration. -/
theorem checkSuccessor_gas_mono (cfg : ProtocolCfg) (g : Option Nat) (hg : CapLe cfg.gasCap g)
    (hh : cfg.reshardHandover = false) (c w : Bytes) :
    Refines (checkSuccessor cfg c w) (checkSuccessor { cfg with gasCap := g } c w) := by
  unfold checkSuccessor
  dsimp only
  simp only [hh, Bool.false_eq_true, ↓reduceIte]
  split
  · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
    · exact Refines.map _ (checkReshardCoreObs_gas_mono _ _ _ _ _ _ _ hg)
    · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · exact checkD2CoreGWith_gas_mono _ _ _ _ _ _ _ hg
        · exact checkD2CoreWith_gas_mono _ _ _ _ _ _ _ hg
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · exact Refines.storage _ (checkD2CoreG_gas_mono _ _ _ _ _ _ hg)
        · exact Refines.storage _ (checkD2Core_gas_mono _ _ _ _ _ _ hg)
  · exact Refines.refl _

/-- Switching on the genesis-aware main transition never changes a decided verdict, at any
configuration without resharding (W10 overlap). With resharding on, the genesis-capable prefix keeps
`c.same_layout` and `c.no_split_gate` while the non-genesis resharding driver lifts them, so the
statement is restricted; every named tier with resharding already sets the genesis flag. -/
theorem checkSuccessor_genesis_mono (cfg : ProtocolCfg) (hr : cfg.resharding = false)
    (hh : cfg.reshardHandover = false) (c w : Bytes) :
    Refines (checkSuccessor cfg c w)
      (checkSuccessor { cfg with genesisMainTransition := true } c w) := by
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg, wu, lu, rh⟩ := cfg
  dsimp only at hr hh
  subst hr hh
  cases gen
  · unfold checkSuccessor
    dsimp only
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    split
    · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · exact checkD2CoreWith_refines_GWith _ rfl _ _ _ _ _
      · exact Refines.storage _ (checkD2Core_refines_G _ _ _ _ _)
    · exact Refines.refl _
  · exact Refines.refl _

/-! ## Named tier pairs, fully proved -/

theorem gAlpha_le_maxGasBurnt : D3.gAlpha ≤ maxGasBurnt := by decide

/-- `checkD3Core ⊑ .protoGas`: where the signed statement's legacy core decides, the protocol-gas tier
agrees. Since the UQ-010 resharding hand-over (2026-10-29) the signed tier itself is *wider* than
`.protoGas` on resharding claims (it decides them; `.protoGas` keeps the legacy exclusions), so the
pair is stated on the core (at `signedCfg`: `checkD3Core` behind the narrower legacy tiers'
storage-proof precondition, `checkSuccessor_signedCore`). -/
theorem relSuccessor_protoGas_mono (c w : Bytes) :
    Refines (checkSuccessor signedCfg c w) (Tier.checker .protoGas c w) :=
  checkSuccessor_gas_mono signedCfg (some maxGasBurnt) gAlpha_le_maxGasBurnt rfl c w

/-- `.floats ⊑ .floatsProtoGas`. -/
theorem relSuccessor_floatsProtoGas_mono (c w : Bytes) :
    Refines (Tier.checker .floats c w) (Tier.checker .floatsProtoGas c w) :=
  checkSuccessor_gas_mono (Tier.cfg .floats) (some maxGasBurnt) gAlpha_le_maxGasBurnt rfl c w

/-- `checkD3Core ⊑ .genesis` (W10): the genesis tier agrees with the signed statement's legacy core
wherever that core decides (stated on the core for the reason given at `relSuccessor_protoGas_mono`). -/
theorem relSuccessor_genesis_mono (c w : Bytes) :
    Refines (checkSuccessor signedCfg c w) (Tier.checker .genesis c w) :=
  checkSuccessor_genesis_mono signedCfg rfl rfl c w

/-- `.floatsProtoGas ⊑ .genesisFloatsProtoGas` (W10). -/
theorem relSuccessor_genesisFloatsProtoGas_mono (c w : Bytes) :
    Refines (Tier.checker .floatsProtoGas c w) (Tier.checker .genesisFloatsProtoGas c w) :=
  checkSuccessor_genesis_mono (Tier.cfg .floatsProtoGas) rfl rfl c w

/-- `.protoGas ⊑ .genesisFloatsProtoGas` needs floats; `.signed ⊑ .protoGas ⊑ ·` composes with
the genesis lift at the protocol-gas configuration. -/
theorem relSuccessor_signed_genesisProtoGas (c w : Bytes) :
    Refines (checkSuccessor signedCfg c w)
      (checkSuccessor { signedCfg with gasCap := some maxGasBurnt, genesisMainTransition := true } c w) :=
  Refines.trans (relSuccessor_protoGas_mono c w) (checkSuccessor_genesis_mono protocolGasCfg rfl rfl c w)

/-- A decided verdict is preserved by any refinement: the verdict-level form of every lemma above. -/
theorem Tier.verdict_of_refines {t t' : Tier} {c w : Bytes}
    (h : Refines (Tier.checker t c w) (Tier.checker t' c w)) (hd : Tier.domainPredicate t c w = true) :
    checkVerdict (Tier.checker t') c w = checkVerdict (Tier.checker t) c w :=
  Refines.verdict h hd

/-! ## Loading limits: a correction, inert where every module fits

`loadingLimits` is not an exclusion lift. When a prepared module's instance allocation does not fit
the pinned pooling allocator, `runCallWithLimits` returns a zero-gas failed call instead of running
it, so a verdict can move between accept and reject. On every call whose module fits (or fails to
prepare), it is the signed `runCall`. -/

theorem runCallWithLimits_eq_of_fits (cfg : Wasm.NearCfg) (code : ByteArray) (method : String)
    (ctx : Wasm.CallCtx) (fuel : Nat) (blockLevel full : Bool) (real : Option Wasm.TTN.RealStore)
    (hfit : ∀ p, Wasm.prepare cfg code blockLevel = .ok p → Wasm.instanceAllocationFits p.m = true) :
    Wasm.runCallWithLimits cfg code method ctx fuel blockLevel full real =
      Wasm.runCall cfg code method ctx fuel blockLevel full real := by
  unfold Wasm.runCallWithLimits
  cases hl : cfg.loadingLimits
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i p hp
      simp only [hfit p hp, ↓reduceIte]
    · rfl

/-! ## Runtime-error branches of the pinned runner (W03, UQ-014)

Dispositions, with pinned-source citations and whole-chunk fixtures, are in
`docs/evidence/lean-chunk-completion/runtime-errors/README.md`. In short:

* `LoadingError`: the only content-determined cause at PV86 is the pooling allocator's instance
  size (`runCallWithLimits`, modelled). The allocator's memory and table checks cannot fail after
  preparation. Every other cause (cache corruption, a foreign artifact, mmap/allocation failure)
  is host state, not chunk content.
* `LinkError` at `instantiate_pre` is the import check (`link`, modelled). The other
  constructions (`memory export missing`, `failed to acquire execution slot`, instantiation
  resources, the gas-hook burn) are unreachable after preparation or depend on host concurrency
  and resources.
* `WasmUnknownError`: unreachable. Every wasmtime 45 trap is classified, and the two
  `nondeterministic trap` codes need epoch interruption or atomics, which PV86 never enables.

The theorem below is the ordering half of the modelled `LoadingError`. nearcore deserializes the
module (`Module::deserialize`, where the allocator check runs) before charging the loading fee,
linking imports or resolving the method (`wasmtime_runner/mod.rs:744-745` runs before the fee at
`:797-808`, and the method is resolved in `prepare`, `:874-905`). So an
over-limit module gives the same zero-gas failure whatever the method, prepaid gas, deposit or
imports. -/

theorem runCallWithLimits_loading_precedes (cfg : Wasm.NearCfg) (code : ByteArray) (method : String)
    (ctx : Wasm.CallCtx) (fuel : Nat) (blockLevel full : Bool) (real : Option Wasm.TTN.RealStore)
    (p : Wasm.Prepared) (hl : cfg.loadingLimits = true) (hp : Wasm.prepare cfg code blockLevel = .ok p)
    (hnf : Wasm.instanceAllocationFits p.m = false) :
    Wasm.runCallWithLimits cfg code method ctx fuel blockLevel full real =
      .line ("abort 0 0 " ++ Wasm.instanceLoadingError ++
        (if full then " || compute 0 || logs  || actions  || trie " else "")) := by
  unfold Wasm.runCallWithLimits
  simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp, hnf]

/-! ## Global actions: the routing part of O3

With `globals = true` the recorder driver routes receipts by `Rcpt.targetShard` and builds the
outgoing-receipts root from it. On receipts that are not distribution receipts this is the D2
routing, so on such lists the two drivers' outgoing roots coincide. -/

/-- A distribution receipt (the only receipt body whose target is not its receiver's shard). -/
def rcptIsDistribution (r : Rcpt) : Bool :=
  match r.body with
  | .distribution _ => true
  | _ => false

theorem targetShard_of_not_distribution (r : Rcpt) (l : Layout) (h : rcptIsDistribution r = false) :
    r.targetShard l = l.shardOf r.recv := by
  unfold Rcpt.targetShard
  unfold rcptIsDistribution at h
  split
  · rename_i d hd; rw [hd] at h; cases h
  · rfl

theorem routedShard_of_not_distribution (r : Rcpt) (l : Layout) (h : rcptIsDistribution r = false) :
    r.routedShard l = l.shardOf r.recv := by
  unfold Rcpt.routedShard
  unfold rcptIsDistribution at h
  split
  · rename_i d hd; rw [hd] at h; cases h
  · rfl

theorem recorderDriver_outgoingRoot_globals (cfg : Wasm.NearCfg) (policy : CodeWitnessPolicy)
    (l : Layout) (rs : List Rcpt) (h : ∀ r ∈ rs, rcptIsDistribution r = false) :
    (recorderDriver cfg true policy).outgoingRoot l rs = outgoingReceiptsRootD2 l rs := by
  simp only [recorderDriver, ↓reduceIte, outgoingReceiptsRootD2]
  congr 1
  apply List.map_congr_left
  intro shard _
  congr 3
  apply List.filter_congr
  intro r hr
  rw [routedShard_of_not_distribution r l (h r hr)]

theorem recorderDriver_receiptShard_globals (cfg : Wasm.NearCfg) (policy : CodeWitnessPolicy)
    (l : Layout) (r : Rcpt) (h : rcptIsDistribution r = false) :
    (recorderDriver cfg true policy).receiptShard l r = (recorderDriver cfg false policy).receiptShard l r := by
  simp only [recorderDriver, ↓reduceIte, Bool.false_eq_true]
  exact routedShard_of_not_distribution r l h

/-! ## Composition: the wide tiers into `.allFeatures`, reduced to named obligations

`Lift cfg cfg'` is the refinement statement for one configuration step. The three named wide tiers
reach `.allFeatures` by adding the features they lack; `c.segment` is proved
(`checkSuccessor_segment_mono`), the others are the open obligations listed below. Each theorem
reduces `relSuccessor_*_mono` for a wide tier to exactly those obligations at exactly those
configurations. The Gate-B steps `.allFeatures` adds (`c.segment`, no gas bound, the compressed
witness bound, the layout bound) are discharged by `Lift.gateB`. -/

/-- One configuration step refines. -/
def Lift (cfg cfg' : ProtocolCfg) : Prop := ∀ c w, Refines (checkSuccessor cfg c w) (checkSuccessor cfg' c w)

theorem Lift.trans {a b c : ProtocolCfg} (h₁ : Lift a b) (h₂ : Lift b c) : Lift a c :=
  fun x y => Refines.trans (h₁ x y) (h₂ x y)

theorem Lift.segment (cfg : ProtocolCfg) : Lift cfg { cfg with segmentUnbounded := true } :=
  fun c w => checkSuccessor_segment_mono cfg c w

theorem Lift.witness (cfg : ProtocolCfg) : Lift cfg { cfg with witnessUnbounded := true } :=
  fun c w => checkSuccessor_witness_mono cfg c w

theorem Lift.layout (cfg : ProtocolCfg) : Lift cfg { cfg with layoutUnbounded := true } :=
  fun c w => checkSuccessor_layout_mono cfg c w

theorem Lift.gas (cfg : ProtocolCfg) (g : Option Nat) (hg : CapLe cfg.gasCap g)
    (hh : cfg.reshardHandover = false) :
    Lift cfg { cfg with gasCap := g } :=
  fun c w => checkSuccessor_gas_mono cfg g hg hh c w

/-- The Gate-B lifts `.allFeatures` adds on top of the named features: `c.segment`, the protocol
gas bound removed (`gasCap := none`), the compressed witness bound and the layout bound. All four
are proved, at any configuration whose gas bound is `some _` or `none` and that does not use the
signed statement's resharding hand-over (every wide tier). -/
theorem Lift.gateB (cfg : ProtocolCfg) (hh : cfg.reshardHandover = false) :
    Lift cfg { cfg with segmentUnbounded := true, gasCap := none, witnessUnbounded := true,
                        layoutUnbounded := true } :=
  (((Lift.segment cfg).trans (Lift.gas _ none (by cases h : cfg.gasCap <;> simp [CapLe, h]) hh)).trans
    (Lift.witness _)).trans (Lift.layout _)

/-- `.resharding ⊑ .allFeatures`, given the global-action lift at the resharding configuration. -/
theorem relSuccessor_resharding_allFeatures_of
    (hGA : Lift (Tier.cfg .resharding) { Tier.cfg .resharding with globalActions := true }) (c w : Bytes) :
    Refines (Tier.checker .resharding c w) (Tier.checker .allFeatures c w) :=
  (hGA.trans (Lift.gateB _ rfl)) c w

/-- Verdict-level refinement: where `x` accepts, `y` accepts; where `x` rejects, `y` rejects (with
any reason). The resharding step needs this weaker form: `ReshardCore` checks a malformed layout in a
different order from `checkD2CoreWithObs`, so a reject can carry a different error string (fixture
`resharding-fixtures/cases/seed23-02-h10062-s5-c.child_layout_is_parent`: `slot count` vs
`shard not in layout`). -/
def VRefines (x y : Except String Unit) : Prop :=
  (x = .ok () → y = .ok ()) ∧
    (∀ e, x = .error e → isExclusion e = false → ∃ e', y = .error e' ∧ isExclusion e' = false)

theorem Refines.toV {x y : Except String Unit} (h : Refines x y) : VRefines x y := by
  rcases h with rfl | ⟨e, rfl, he⟩
  · exact ⟨id, fun e hx hne => ⟨e, hx, hne⟩⟩
  · refine ⟨fun h => (by cases h), fun e' hx hne => ?_⟩
    cases hx
    rw [he] at hne
    cases hne

theorem VRefines.trans {x y z : Except String Unit} (h₁ : VRefines x y) (h₂ : VRefines y z) :
    VRefines x z := by
  refine ⟨fun hx => h₂.1 (h₁.1 hx), fun e hx hne => ?_⟩
  obtain ⟨e', hy, hne'⟩ := h₁.2 e hx hne
  exact h₂.2 e' hy hne'

/-- One configuration step refines at verdict level. -/
def VLift (cfg cfg' : ProtocolCfg) : Prop :=
  ∀ c w, VRefines (checkSuccessor cfg c w) (checkSuccessor cfg' c w)

theorem VLift.trans {a b c : ProtocolCfg} (h₁ : VLift a b) (h₂ : VLift b c) : VLift a c :=
  fun x y => VRefines.trans (h₁ x y) (h₂ x y)

theorem Lift.toV {a b : ProtocolCfg} (h : Lift a b) : VLift a b := fun c w => (h c w).toV

/-- `.curveHosts ⊑ .allFeatures` at verdict level, given the resharding lift (verdict level, see
`VRefines`) and the global-action lift. -/
theorem relSuccessor_curveHosts_allFeatures_of
    (hR : VLift (Tier.cfg .curveHosts) (Tier.cfg .resharding))
    (hGA : Lift (Tier.cfg .resharding) { Tier.cfg .resharding with globalActions := true }) (c w : Bytes) :
    VRefines (Tier.checker .curveHosts c w) (Tier.checker .allFeatures c w) :=
  ((hR.trans hGA.toV).trans (Lift.gateB _ rfl).toV) c w

/-- `.globalActions ⊑ .allFeatures` at verdict level, given the curve-host lift and the
resharding lift (verdict level) at the global-action configurations. -/
theorem relSuccessor_globalActions_allFeatures_of
    (hC : Lift (Tier.cfg .globalActions) { Tier.cfg .globalActions with curveHosts := true })
    (hR : VLift { Tier.cfg .globalActions with curveHosts := true }
      { Tier.cfg .globalActions with curveHosts := true, resharding := true }) (c w : Bytes) :
    VRefines (Tier.checker .globalActions c w) (Tier.checker .allFeatures c w) :=
  ((hC.toV.trans hR).trans (Lift.gateB _ rfl).toV) c w

/-! ## Remaining obligations (W12)

Proved here, with no premise: `c.segment`, the gas bound (including its removal), the Gate-B witness
and layout lifts (all configurations; composed as `Lift.gateB`),
the genesis main transition (all configurations without resharding; W10 overlap including the common
prefix), the resharding driver on the whole-state shells, and the named pairs
`.signed ⊑ .protoGas`, `.floats ⊑ .floatsProtoGas`, `.signed ⊑ .genesis`,
`.floatsProtoGas ⊑ .genesisFloatsProtoGas`, and `.curveHosts ⊑ .resharding` on segments containing
a genesis block.

Status 2026-10-30 (`TierFloats.lean`, `TierHooks.lean`, `TierRefine.lean`; evidence
`docs/evidence/lean-chunk-completion/tier-refinement-w12/`): O1 is proved on the legacy engine,
which covers every named pair that differs in `floats`. O5 is discharged for the named tiers. The
rest are open, each checked empirically (`docs/evidence/lean-chunk-completion/tier-proofs/`):

* **O1 floats** — proved on the legacy engine: `Lift.floats_legacy` (`TierRefine.lean`), from
  `Wasm.prepare_floats`, `Wasm.runCallWithLimits_floats`, `d3Hooks_floats` and
  `checkD2Core_hooks_mono`/`checkD2CoreG_hooks_mono`. Named pairs: `relSuccessor_floats_mono`,
  `relSuccessor_protoGas_floatsProtoGas`, `relSuccessor_genesis_genesisFloatsProtoGas`. Still
  open: `Lift cfg { cfg with floats := true }` on whole-state configurations (no named pair needs it).
* **O2 curve hosts** — `Lift cfg { cfg with curveHosts := true }`. `successorDispatch_extends`
  (`Wasm/Exec.lean`) is the host-table step; missing is its propagation through `runCall`, `St`
  and the trie-backed runtime.
* **O3 global actions** — `Lift cfg { cfg with globalActions := true }` on whole-state
  configurations. Proved: routing and the outgoing-receipts root agree on lists without
  distribution receipts (`recorderDriver_receiptShard_globals`, `recorderDriver_outgoingRoot_globals`).
  Missing: the global codecs (`pRcptGlobal`, `pTxD2Global`) decode every witness the D2 codecs decode
  to the same value; `validateRouting`'s `globalTarget` never excludes a non-distribution receipt
  (`shardOf` lands in `shardIds`); `StorageExecution.run` monotone in `globals`.
* **O4 storage resolution** — the step from the legacy main transition (`applyNewChunkD2`, merged
  value size bound) to `recorderDriver` (`StorageExecution.run`, W08 pipeline code rule). This is a
  change of engine, not a guard: the refinement needs an agreement theorem between the two runtimes
  on the legacy domain. Since 2026-10-30 (`TierO4.lean`): proved at shell and tier level given the
  engine agreement (`relSuccessor_runtimeLimits_storageResolution_of`, premise `EngineAgree`, witness
  condition `O4Witness`), after fixing the narrower legacy tiers' rejects above the storage bound
  (`Config.withStorageExclusion`; 26 nearcore-valid `storage-limit-fixtures` chunks). The engine
  agreement is open. Until 2026-10-27 it was false without a layout restriction: on the honest,
  nearcore-valid fixture `resharding-fixtures/cases/seed11-02-h10077-s2` (a V3 layout after a split,
  one layout across the claim's epochs, non-empty outgoing buffers) every legacy-engine tier,
  `.signed` included, rejected with `InvalidBandwidthRequests`. The legacy `bandwidthRequests`
  (`D2/Queues.lean`) now applies the V3 parent chaining for a V3 layout, and
  `Logged.R_bandwidthRequestsV3` relates it to the recorder engine's `bandwidthRequestsV3L`; every
  tier accepts the fixture. The legacy buffer forwarding still reports a non-empty buffer outside the
  layout as `c.same_layout` (an exclusion, not a reject) where `forwardFromBufferV3L` forwards it.
* **O5 loading limits** — not a lift (a semantic correction). Since 2026-10-27 `Wasm.pv86`, and so
  `signedCfg` and every tier, sets the flag, so no named tier pair differs in it
  (`Tier.cfg_loadingLimits`, `relSuccessor_runtimeLimits_mono`, `TierRefine.lean`). The restricted
  statement is `runCallWithLimits_eq_of_fits`.
* **O6 resharding, non-genesis** — `VRefines (checkD2CoreWith recorderDriver …)
  (checkReshardCore reshardingDriver …)` on segments without a genesis block: `ReshardCore` walks the
  segment per block layout and must reduce to `checkD2CoreWithObs` when every epoch has one layout
  and no split gate is set. Only the verdict-level form can hold (see `VRefines`).
* **O7 complete-code witness** — since W08 (2026-10-29) the complete policy is the cold
  validator's resolution plus a hash check on witness bytes (`CodeResolution.complete_eq_cold`),
  so the 178 warm-cache rejects (`w.code_complete`) are gone, and an untimely pipelined preparation
  is a race exclusion under both policies (`complete_untimely_ood`, `TierRefine.lean`). The
  chunk-level refinement is still open.
-/

#print axioms checkSuccessor_segment_mono
#print axioms checkSuccessor_gas_mono
#print axioms checkSuccessor_witness_mono
#print axioms checkSuccessor_layout_mono
#print axioms Lift.gateB
#print axioms checkSuccessor_genesis_mono
#print axioms relSuccessor_protoGas_mono
#print axioms relSuccessor_floatsProtoGas_mono
#print axioms relSuccessor_genesis_mono
#print axioms relSuccessor_genesisFloatsProtoGas_mono
#print axioms checkD2CoreGWith_reshardingDriver_mono
#print axioms relSuccessor_resharding_mono_genesis
#print axioms runCallWithLimits_eq_of_fits
#print axioms runCallWithLimits_loading_precedes
#print axioms relSuccessor_resharding_allFeatures_of
#print axioms relSuccessor_curveHosts_allFeatures_of
#print axioms relSuccessor_globalActions_allFeatures_of
#print axioms checkD2CoreG_overlap
#print axioms Refines.toV
#print axioms recorderDriver_outgoingRoot_globals
#print axioms recorderDriver_receiptShard_globals

end NearSpecV3.Successor
