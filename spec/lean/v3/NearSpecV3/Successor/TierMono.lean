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
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, bl, ik, sa⟩ := d
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
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, bl, ik, sa⟩ := d
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

/-- Weakening the per-chunk gas bound never changes a decided verdict, at any configuration. -/
theorem checkSuccessor_gas_mono (cfg : ProtocolCfg) (g : Option Nat) (hg : CapLe cfg.gasCap g)
    (c w : Bytes) :
    Refines (checkSuccessor cfg c w) (checkSuccessor { cfg with gasCap := g } c w) := by
  unfold checkSuccessor
  dsimp only
  split
  · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
    · exact Refines.map _ (checkReshardCoreObs_gas_mono _ _ _ _ _ _ _ hg)
    · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · exact checkD2CoreGWith_gas_mono _ _ _ _ _ _ _ hg
        · exact checkD2CoreWith_gas_mono _ _ _ _ _ _ _ hg
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · exact checkD2CoreG_gas_mono _ _ _ _ _ _ hg
        · exact checkD2Core_gas_mono _ _ _ _ _ _ hg
  · exact Refines.refl _

/-- Switching on the genesis-aware main transition never changes a decided verdict, at any
configuration without resharding (W10 overlap). With resharding on, the genesis-capable prefix keeps
`c.same_layout` and `c.no_split_gate` while the non-genesis resharding driver lifts them, so the
statement is restricted; every named tier with resharding already sets the genesis flag. -/
theorem checkSuccessor_genesis_mono (cfg : ProtocolCfg) (hr : cfg.resharding = false) (c w : Bytes) :
    Refines (checkSuccessor cfg c w)
      (checkSuccessor { cfg with genesisMainTransition := true } c w) := by
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg⟩ := cfg
  dsimp only at hr
  subst hr
  cases gen
  · unfold checkSuccessor
    dsimp only
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    split
    · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · exact checkD2CoreWith_refines_GWith _ rfl _ _ _ _ _
      · exact checkD2Core_refines_G _ _ _ _ _
    · exact Refines.refl _
  · exact Refines.refl _

/-! ## Named tier pairs, fully proved -/

theorem gAlpha_le_maxGasBurnt : D3.gAlpha ≤ maxGasBurnt := by decide

/-- `.signed ⊑ .protoGas`: where the signed checker decides, the protocol-gas tier agrees. -/
theorem relSuccessor_protoGas_mono (c w : Bytes) :
    Refines (Tier.checker .signed c w) (Tier.checker .protoGas c w) :=
  checkSuccessor_gas_mono signedCfg (some maxGasBurnt) gAlpha_le_maxGasBurnt c w

/-- `.floats ⊑ .floatsProtoGas`. -/
theorem relSuccessor_floatsProtoGas_mono (c w : Bytes) :
    Refines (Tier.checker .floats c w) (Tier.checker .floatsProtoGas c w) :=
  checkSuccessor_gas_mono (Tier.cfg .floats) (some maxGasBurnt) gAlpha_le_maxGasBurnt c w

/-- `.signed ⊑ .genesis` (W10): the genesis tier agrees with `checkD3` wherever `checkD3` decides. -/
theorem relSuccessor_genesis_mono (c w : Bytes) :
    Refines (Tier.checker .signed c w) (Tier.checker .genesis c w) :=
  checkSuccessor_genesis_mono signedCfg rfl c w

/-- `.floatsProtoGas ⊑ .genesisFloatsProtoGas` (W10). -/
theorem relSuccessor_genesisFloatsProtoGas_mono (c w : Bytes) :
    Refines (Tier.checker .floatsProtoGas c w) (Tier.checker .genesisFloatsProtoGas c w) :=
  checkSuccessor_genesis_mono (Tier.cfg .floatsProtoGas) rfl c w

/-- `.protoGas ⊑ .genesisFloatsProtoGas` needs floats; `.signed ⊑ .protoGas ⊑ ·` composes with
the genesis lift at the protocol-gas configuration. -/
theorem relSuccessor_signed_genesisProtoGas (c w : Bytes) :
    Refines (Tier.checker .signed c w)
      (checkSuccessor { signedCfg with gasCap := some maxGasBurnt, genesisMainTransition := true } c w) :=
  Refines.trans (relSuccessor_protoGas_mono c w) (checkSuccessor_genesis_mono protocolGasCfg rfl c w)

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

/-! ## Composition: the wide tiers into `.allFeatures`, reduced to named obligations

`Lift cfg cfg'` is the refinement statement for one configuration step. The three named wide tiers
reach `.allFeatures` by adding the features they lack; `c.segment` is proved
(`checkSuccessor_segment_mono`), the others are the open obligations listed below. Each theorem
reduces `relSuccessor_*_mono` for a wide tier to exactly those obligations at exactly those
configurations. -/

/-- One configuration step refines. -/
def Lift (cfg cfg' : ProtocolCfg) : Prop := ∀ c w, Refines (checkSuccessor cfg c w) (checkSuccessor cfg' c w)

theorem Lift.trans {a b c : ProtocolCfg} (h₁ : Lift a b) (h₂ : Lift b c) : Lift a c :=
  fun x y => Refines.trans (h₁ x y) (h₂ x y)

theorem Lift.segment (cfg : ProtocolCfg) : Lift cfg { cfg with segmentUnbounded := true } :=
  fun c w => checkSuccessor_segment_mono cfg c w

/-- `.resharding ⊑ .allFeatures`, given the global-action lift at the resharding configuration. -/
theorem relSuccessor_resharding_allFeatures_of
    (hGA : Lift (Tier.cfg .resharding) { Tier.cfg .resharding with globalActions := true }) (c w : Bytes) :
    Refines (Tier.checker .resharding c w) (Tier.checker .allFeatures c w) :=
  (hGA.trans (Lift.segment _)) c w

/-- `.curveHosts ⊑ .allFeatures`, given the global-action and resharding lifts. -/
theorem relSuccessor_curveHosts_allFeatures_of
    (hR : Lift (Tier.cfg .curveHosts) (Tier.cfg .resharding))
    (hGA : Lift (Tier.cfg .resharding) { Tier.cfg .resharding with globalActions := true }) (c w : Bytes) :
    Refines (Tier.checker .curveHosts c w) (Tier.checker .allFeatures c w) :=
  ((hR.trans hGA).trans (Lift.segment _)) c w

/-- `.globalActions ⊑ .allFeatures`, given the curve-host and resharding lifts at the
global-action configurations. -/
theorem relSuccessor_globalActions_allFeatures_of
    (hC : Lift (Tier.cfg .globalActions) { Tier.cfg .globalActions with curveHosts := true })
    (hR : Lift { Tier.cfg .globalActions with curveHosts := true }
      { Tier.cfg .globalActions with curveHosts := true, resharding := true }) (c w : Bytes) :
    Refines (Tier.checker .globalActions c w) (Tier.checker .allFeatures c w) :=
  ((hC.trans hR).trans (Lift.segment _)) c w

/-! ## Remaining obligations (W12)

Proved here, with no premise: `c.segment` (all configurations), the gas bound (all configurations),
the genesis main transition (all configurations without resharding; W10 overlap including the common
prefix), the resharding driver on the whole-state shells, and the named pairs
`.signed ⊑ .protoGas`, `.floats ⊑ .floatsProtoGas`, `.signed ⊑ .genesis`,
`.floatsProtoGas ⊑ .genesisFloatsProtoGas`, and `.curveHosts ⊑ .resharding` on segments containing
a genesis block.

Open, each checked empirically (`docs/evidence/lean-chunk-completion/tier-proofs/`), none proved:

* **O1 floats** — `Lift cfg { cfg with floats := true }`. `NearCfg.floats` occurs only in the three
  `Prepare` guards `!cfg.floats && …`; the missing piece is the induction over `prepare`, the
  interpreter and the chunk runtime showing that no other site reads it.
* **O2 curve hosts** — `Lift cfg { cfg with curveHosts := true }`. `successorDispatch_extends`
  (`Wasm/Exec.lean`) is the host-table step; missing is its propagation through `runCall`, `St`
  and the trie-backed runtime.
* **O3 global actions** — `Lift cfg { cfg with globalActions := true }` on whole-state
  configurations. Missing: the global codecs (`pRcptGlobal`, `pTxD2Global`) decode every witness the
  D2 codecs decode to the same value; `targetShard = shardOf ∘ recv` on non-global receipts (so
  routing and the outgoing-receipts root agree); `StorageExecution.run` monotone in `globals`.
* **O4 storage resolution** — the step from the legacy main transition (`applyNewChunkD2`, merged
  value size bound) to `recorderDriver` (`StorageExecution.run`, W08 pipeline code rule). This is a
  change of engine, not a guard: the refinement needs an agreement theorem between the two runtimes
  on the legacy domain.
* **O5 loading limits** — not a lift (a semantic correction). The restricted statement is
  `runCallWithLimits_eq_of_fits`; the chunk-level form (every executed module fits ⇒ the flag is
  inert) needs the same propagation as O2.
* **O6 resharding, non-genesis** — `Refines (checkD2CoreWith recorderDriver …)
  (checkReshardCore reshardingDriver …)` on segments without a genesis block: `ReshardCore` walks the
  segment per block layout and must reduce to `checkD2CoreWithObs` when every epoch has one layout
  and no split gate is set.
* **O7 complete-code witness** — not a lift, and not in the join: on warm-cache chunks it rejects
  (`w.code_complete`) where every other whole-state tier excludes or accepts; the counterexample
  family is in the evidence.
-/

#print axioms checkSuccessor_segment_mono
#print axioms checkSuccessor_gas_mono
#print axioms checkSuccessor_genesis_mono
#print axioms relSuccessor_protoGas_mono
#print axioms relSuccessor_floatsProtoGas_mono
#print axioms relSuccessor_genesis_mono
#print axioms relSuccessor_genesisFloatsProtoGas_mono
#print axioms checkD2CoreGWith_reshardingDriver_mono
#print axioms relSuccessor_resharding_mono_genesis
#print axioms runCallWithLimits_eq_of_fits
#print axioms relSuccessor_resharding_allFeatures_of
#print axioms relSuccessor_curveHosts_allFeatures_of
#print axioms relSuccessor_globalActions_allFeatures_of
#print axioms checkD2CoreG_overlap

end NearSpecV3.Successor
