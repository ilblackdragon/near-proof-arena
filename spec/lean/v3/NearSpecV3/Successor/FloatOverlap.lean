import NearSpecV3.Successor.TierRefine

/-!
# W04 — the float extension agrees with the signed checker on its overlap

The L2 lane left "chunk-level old/new agreement on the overlap" open
(`ChallengeChunkV3Float.lean`: "`checkD3F = checkD3` on float-free chunks … is not proved").
W12 proved `relSuccessor_floats_mono : Refines (Tier.checker .signed c w) (Tier.checker .floats c w)`
(`TierRefine.lean`, via `prepare_floats`, `runCallWithLimits_floats`, `d3Hooks_floats` and
`checkD2Core_hooks_mono`). Since `Tier.checker .signed = checkD3` and `Tier.checker .floats =
checkD3F` definitionally (`tier_signed_eq_checkD3`, `tier_floats_eq_checkD3F`), that is already the
overlap statement, for every chunk and not only float-free ones:

* `checkD3F_refines_checkD3`: `checkD3F` returns exactly `checkD3`'s result wherever `checkD3` is not
  an exclusion (`out of domain …`);
* `relD3_relD3F`: every chunk the signed statement accepts, the float extension accepts;
* `checkD3F_reject_of_checkD3_reject`: every chunk the signed statement rejects (a non-exclusion
  error), the float extension rejects with the same reason;
* `checkD3F_verdict_of_decided`: the classified verdicts agree whenever the signed one is not
  out of domain.

So on the overlap — the chunks `checkD3` decides — the two checkers agree; the only chunks whose
verdict can move are ones `checkD3` excludes (the float exclusions among them). A float-free chunk is
a special case: its `checkD3` verdict is either decided (then `checkD3F` agrees) or an exclusion for
a reason other than floats. The latter can still move only if lifting floats changes the run, which
`prepare_floats` rules out at the guard level; equality there is not claimed beyond `Refines`.

**Since the UQ-010 hand-over (2026-10-29)** the statement of record `D3.checkD3` is its legacy core
`D3.checkD3Core` plus a recorder-engine decision of the core's resharding and over-bound errors
(`D3/Signed.lean`); `checkD3F` has no hand-over. The theorems below are therefore stated on the core,
which is exactly the old `checkD3` (and `Tier.checker .signed` is no longer `checkD3F`'s refinement
base: it decides claims `checkD3F` excludes). Since 2026-10-30 (W12 O4) `Tier.checker .floats` is
`checkD3F` behind the narrower legacy tiers' storage-proof precondition (`withStorageExclusion`);
the theorems below are about the adapter `checkD3F` itself, from the hook refinement directly.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3

theorem checkD3F_refines_checkD3 (c w : Bytes) : Refines (D3.checkD3Core c w) (checkD3F c w) := by
  have hh : HooksRefine (D3.d3Hooks signedCfg.wasm)
      (D3.d3Hooks ({ signedCfg with floats := true } : ProtocolCfg).wasm) := by
    rw [ProtocolCfg.wasm_floats signedCfg rfl]
    exact d3Hooks_floats _
  exact checkD2Core_hooks_mono hh _ _ _ _

theorem relD3_relD3F (c w : Bytes) (h : D3.checkD3Core c w = .ok ()) : RelD3F c w := by
  rcases checkD3F_refines_checkD3 c w with he | ⟨e, he, _⟩
  · show checkD3F c w = .ok ()
    rw [← he]; exact h
  · have : D3.checkD3Core c w = .ok () := h
    rw [this] at he; cases he

theorem checkD3F_reject_of_checkD3_reject (c w : Bytes) (e : String) (h : D3.checkD3Core c w = .error e)
    (hx : isExclusion e = false) : checkD3F c w = .error e := by
  rcases checkD3F_refines_checkD3 c w with he | ⟨e', he, hex⟩
  · rw [← he, h]
  · rw [h] at he; cases he; rw [hx] at hex; cases hex

theorem checkD3F_verdict_of_decided (c w : Bytes)
    (h : ∀ e, checkVerdict D3.checkD3Core c w ≠ .outOfDomain e) :
    checkVerdict checkD3F c w = checkVerdict D3.checkD3Core c w := by
  unfold checkVerdict at h ⊢
  rcases checkD3F_refines_checkD3 c w with he | ⟨e, he, hex⟩
  · rw [he]
  · exfalso
    apply h e
    rw [he]
    simp [Verdict.ofExcept, hex]

/-- info: 'NearSpecV3.Successor.relD3_relD3F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms relD3_relD3F

/-- info: 'NearSpecV3.Successor.checkD3F_reject_of_checkD3_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkD3F_reject_of_checkD3_reject

/-- info: 'NearSpecV3.Successor.checkD3F_verdict_of_decided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkD3F_verdict_of_decided

end NearSpecV3.Successor
