import NearSpecV3.Successor.TierHooks

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 — obligations O1 (floats) and O5 (loading limits), at configuration and tier level

* **O1.** `Lift.floats_legacy`: on every configuration that runs the legacy engine (no storage
  resolution, global actions, complete-code witness or resharding), switching floats on refines.
  Chain: `prepare_floats` (`TierFloats.lean`: preparation changes only where the float-free run
  reported `outOfDomain`) → `runCallWithLimits_floats` (the interpreter never reads the flag) →
  `d3Hooks_floats` (the hook refines) → `checkD2Core_hooks_mono` / `checkD2CoreG_hooks_mono`
  (`TierHooks.lean`: the legacy pipeline only binds the hook's result).
  Named pairs: `.signed ⊑ .floats`, `.protoGas ⊑ .floatsProtoGas`,
  `.genesis ⊑ .genesisFloatsProtoGas`, and the compositions into `.genesisFloatsProtoGas` and
  `.runtimeLimits`.
  Not covered: floats on the whole-state (recorder) engine. No named tier pair needs it (every
  whole-state tier already sets floats); it would need the same propagation through
  `StorageExecution`.
* **O5.** Every named tier sets `loadingLimits` (`Tier.cfg_loadingLimits`), so no named pair
  differs in it, and `.genesisFloatsProtoGas` and `.runtimeLimits` are the same configuration
  (`runtimeLimits_cfg_eq`, `relSuccessor_runtimeLimits_mono`). The flag is a semantic correction,
  not a lift, so `Lift cfg { cfg with loadingLimits := true }` is false in general (a module that
  does not fit the pooling allocator moves the verdict); its call-level inertness on fitting modules
  is `runCallWithLimits_eq_of_fits` (`TierMono.lean`).
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

theorem ProtocolCfg.wasm_floats (cfg : ProtocolCfg) (h : cfg.floats = false) :
    ({ cfg with floats := true } : ProtocolCfg).wasm = { cfg.wasm with floats := true } := by
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg, wu, lu, rh⟩ := cfg
  simp only at h
  subst h
  rfl

theorem ProtocolCfg.floats_true_eq (cfg : ProtocolCfg) (h : cfg.floats = true) :
    ({ cfg with floats := true } : ProtocolCfg) = cfg := by
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg, wu, lu, rh⟩ := cfg
  simp only at h
  subst h
  rfl

/-- On a configuration without the whole-state features, the root is the legacy engine with the
D3 hooks (without the signed statement's UQ-010 hand-over, `reshardHandover = false`). -/
theorem checkSuccessor_legacy_eq (cfg : ProtocolCfg) (hs : cfg.storageResolution = false)
    (hg : cfg.globalActions = false) (hc : cfg.completeCodeWitness = false)
    (hr : cfg.resharding = false) (hh : cfg.reshardHandover = false) (c w : Bytes) :
    checkSuccessor cfg c w =
      if cfg.protocolVersion = 86 then
        (if cfg.genesisMainTransition then checkD2CoreG (D3.d3Hooks cfg.wasm) true c w cfg.gasCap
         else checkD2Core (D3.d3Hooks cfg.wasm) true c w cfg.gasCap)
      else .error (unsupportedPvError cfg.protocolVersion) := by
  unfold checkSuccessor
  split
  · rename_i h
    simp only [hs, hg, hc, hr, hh, h, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  · rename_i h
    split
    · exact absurd ‹_› h
    · rfl

/-- **O1 on the legacy engine.** On every configuration that runs `checkD2Core`/`checkD2CoreG`,
switching floats on never changes a decided verdict. -/
theorem Lift.floats_legacy (cfg : ProtocolCfg) (hs : cfg.storageResolution = false)
    (hg : cfg.globalActions = false) (hc : cfg.completeCodeWitness = false)
    (hr : cfg.resharding = false) (hrh : cfg.reshardHandover = false) :
    Lift cfg { cfg with floats := true } := by
  intro c w
  cases hf : cfg.floats
  · have hh : HooksRefine (D3.d3Hooks cfg.wasm)
        (D3.d3Hooks ({ cfg with floats := true } : ProtocolCfg).wasm) := by
      rw [ProtocolCfg.wasm_floats cfg hf]
      exact d3Hooks_floats _
    rw [checkSuccessor_legacy_eq cfg hs hg hc hr hrh c w,
      checkSuccessor_legacy_eq { cfg with floats := true } hs hg hc hr hrh c w]
    refine Refines.ite_congr _ (fun _ => Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
      (fun _ => Refines.refl _)
    · exact checkD2CoreG_hooks_mono hh _ _ _ _
    · exact checkD2Core_hooks_mono hh _ _ _ _
  · rw [ProtocolCfg.floats_true_eq cfg hf]
    exact Refines.refl _

/-- `checkD3Core ⊑ .floats` (O1). Stated on the signed statement's legacy core: since the UQ-010
hand-over (2026-10-29) `.signed` itself decides resharding and over-bound claims that `.floats`
excludes, so it is wider than `.floats` there (`TierMono.relSuccessor_protoGas_mono`). -/
theorem relSuccessor_floats_mono (c w : Bytes) :
    Refines (D3.checkD3Core c w) (Tier.checker .floats c w) :=
  Lift.floats_legacy signedCfg rfl rfl rfl rfl rfl c w

/-- `.protoGas ⊑ .floatsProtoGas` (O1). -/
theorem relSuccessor_protoGas_floatsProtoGas (c w : Bytes) :
    Refines (Tier.checker .protoGas c w) (Tier.checker .floatsProtoGas c w) :=
  Lift.floats_legacy protocolGasCfg rfl rfl rfl rfl rfl c w

/-- `.genesis ⊑ .genesisFloatsProtoGas` (O1, then the gas bound). -/
theorem relSuccessor_genesis_genesisFloatsProtoGas (c w : Bytes) :
    Refines (Tier.checker .genesis c w) (Tier.checker .genesisFloatsProtoGas c w) :=
  Refines.trans (Lift.floats_legacy (Tier.cfg .genesis) rfl rfl rfl rfl rfl c w)
    (checkSuccessor_gas_mono { Tier.cfg .genesis with floats := true } (some maxGasBurnt)
      gAlpha_le_maxGasBurnt rfl c w)

/-- `checkD3Core ⊑ .genesisFloatsProtoGas`: the signed statement's legacy core refines the widest
legacy-engine tier. -/
theorem relSuccessor_signed_genesisFloatsProtoGas (c w : Bytes) :
    Refines (D3.checkD3Core c w) (Tier.checker .genesisFloatsProtoGas c w) :=
  Refines.trans (relSuccessor_genesis_mono c w) (relSuccessor_genesis_genesisFloatsProtoGas c w)

/-- `.floats ⊑ .genesisFloatsProtoGas`. -/
theorem relSuccessor_floats_genesisFloatsProtoGas (c w : Bytes) :
    Refines (Tier.checker .floats c w) (Tier.checker .genesisFloatsProtoGas c w) :=
  Refines.trans (relSuccessor_floatsProtoGas_mono c w) (relSuccessor_genesisFloatsProtoGas_mono c w)

/-! ## O5: loading limits -/

/-- Every named tier carries the pinned loading rule. -/
theorem Tier.cfg_loadingLimits (t : Tier) : (Tier.cfg t).loadingLimits = true := by
  cases t <;> rfl

theorem runtimeLimits_cfg_eq : Tier.cfg .runtimeLimits = Tier.cfg .genesisFloatsProtoGas := rfl

/-- `.genesisFloatsProtoGas ⊑ .runtimeLimits` (both ways: the same configuration). -/
theorem relSuccessor_runtimeLimits_mono (c w : Bytes) :
    Refines (Tier.checker .genesisFloatsProtoGas c w) (Tier.checker .runtimeLimits c w) := by
  unfold Tier.checker
  rw [runtimeLimits_cfg_eq]
  exact Refines.refl _

/-- `checkD3Core ⊑ .runtimeLimits`. -/
theorem relSuccessor_signed_runtimeLimits (c w : Bytes) :
    Refines (D3.checkD3Core c w) (Tier.checker .runtimeLimits c w) :=
  Refines.trans (relSuccessor_signed_genesisFloatsProtoGas c w) (relSuccessor_runtimeLimits_mono c w)

#print axioms Wasm.sectionBody_floats
#print axioms Wasm.earlyPass_floats
#print axioms Wasm.prepare_floats
#print axioms Wasm.run_floats
#print axioms functionCallWith_mono
#print axioms callRel_floats
#print axioms Wasm.runCallWithLimits_floats
#print axioms d3Hooks_floats
#print axioms checkD2Core_hooks_mono
#print axioms checkD2CoreG_hooks_mono
#print axioms checkSuccessor_legacy_eq
#print axioms Lift.floats_legacy
#print axioms relSuccessor_floats_mono
#print axioms relSuccessor_protoGas_floatsProtoGas
#print axioms relSuccessor_genesis_genesisFloatsProtoGas
#print axioms relSuccessor_signed_genesisFloatsProtoGas
#print axioms relSuccessor_floats_genesisFloatsProtoGas
#print axioms Tier.cfg_loadingLimits
#print axioms relSuccessor_runtimeLimits_mono
#print axioms relSuccessor_signed_runtimeLimits

/-! ## O7: the complete-code policy against the cold validator, at the code-resolution step

`completeCodeGlobal` differs from `globalActions` only in `CodeWitnessPolicy` (`.complete` vs
`.coldPartial`), read once per call by `resolveCodeBytes`. Since W08 (2026-10-29) `.complete` is
the cold validator's own resolution plus an explicit hash check on witness bytes
(`CodeResolution.complete_eq_cold`). Before W08, `.complete` accepted a call whose code only a
committed in-chunk deploy serves although its preparation was pipelined before that deploy
(`timely = false`), a nearcore thread race. Both policies now send that case to the race
exclusion: -/

theorem complete_untimely_ood (code : Bytes) :
    resolveCodeBytes .complete { witness := fun _ => none, committed := [code] } .absent
      (sha256 code) false = .error raceExclusion := by
  simp [resolveCodeBytes, resolveCompleteCode]

theorem coldPartial_untimely_ood (code : Bytes) :
    resolveCodeBytes .coldPartial { witness := fun _ => none, committed := [code] } .absent
      (sha256 code) false = .error raceExclusion := by
  simp [resolveCodeBytes, resolveColdCode]

#print axioms complete_untimely_ood
#print axioms coldPartial_untimely_ood

/-- On the race arm both policies report the same exclusion, for any sources. -/
theorem complete_untimely_ood_general (sources : CodeSources) (pre : PrestateCode) (hash code : Bytes)
    (hw : sources.witness hash = none)
    (hc : sources.current.find? (fun c => sha256 c == hash) = none)
    (hd : (sources.committed ++ sources.attempted).find? (fun c => sha256 c == hash) = some code) :
    resolveCodeBytes .complete sources pre hash false = .error raceExclusion ∧
      resolveCodeBytes .coldPartial sources pre hash false = .error raceExclusion := by
  refine ⟨?_, ?_⟩
  · simp [resolveCodeBytes, resolveCompleteCode, hw, hc, hd]
  · simp [resolveCodeBytes, resolveColdCode, hw, hc, hd]

/-- **O7, resolve step, without the authenticity premise of `complete_eq_cold`.** Wherever the
complete policy resolves code, the cold policy resolves the same bytes. -/
theorem complete_ok_coldPartial (sources : CodeSources) (pre : PrestateCode) (hash code : Bytes)
    (timely : Bool) (h : resolveCodeBytes .complete sources pre hash timely = .ok code) :
    resolveCodeBytes .coldPartial sources pre hash timely = .ok code := by
  simp only [resolveCodeBytes, resolveCompleteCode, resolveColdCode] at h ⊢
  cases hw : sources.witness hash with
  | none => rw [hw] at h; exact h
  | some c =>
    rw [hw] at h
    by_cases hs : (sha256 c == hash) = true <;> simp_all

theorem raceExclusion_isExclusion : isExclusion raceExclusion = true := by
  unfold raceExclusion; ood_tac

#print axioms complete_untimely_ood_general
#print axioms complete_ok_coldPartial
#print axioms raceExclusion_isExclusion

end NearSpecV3.Successor
