import ZkFormal.Udr.Np.Main
import ZkFormal.V2.Verifier

/-!
# ZkFormal.V2.Np.Defs — L3 for `np-udr-stark-v2`: the doomed predicate

Round-by-round soundness of `Iop.verifierP Fp Fp8 AP prm` for the language
`AirLangP AP` (`∃ tr, HoldsP AP (pubOf cb) tr`).  This mirrors v1's L3 (`ZkFormal.Udr.Np`)
and reuses its semantic reading of transcripts (`Sem.lean`), which does not depend on
the public messages.  Only the bus parts of the doomed stages change:

* `busMsgsP` = v1's `busMsgs` (trace contributions) ++ `pubBM` (public messages, multiplicity one);
* `FpDifferP` and `GpDifferP` compare the extended multisets.  Their bad-challenge bounds
  come from the same `gpAlpha` / `gpGamma`, under the v2 budgets `fpBoundP` and `multBoundP`;
* `BusFinalsFailP α γ`: `∏ send finals · Π_pub(send) ≠ ∏ recv finals · Π_pub(recv)`;
* `GlobalFailP`: v2's `globalChecksP` rejects.

The structural condition `pubFit` is a function of the claim alone.  `DoomedP` carries
`pubFit = false` as a separate disjunct, which is constant along the transcript and
contradicts `global` at the query phase.

The verifier's shape, schedule, header check and per-position checks are v1's
(`Iop.verifierP` is a structure update of `Iop.verifier`), so `Shaped`, `NextIsProver`,
`NextIsChal`, `AtQuery`, `domSize` and `trueOpenings` are v1's by `rfl`.
-/

namespace ZkFormal.V2.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2

/-- The language of v2: claims with a trace satisfying `HoldsP`. -/
def AirLangP (AP : AirP) (cb : Bytes) : Prop :=
  ∃ tr : Air.Trace Fp, HoldsP AP (pubOf Fp cb) tr

/-- Shorthand for the v2 verifier. -/
abbrev VnpP (AP : AirP) (prm : Params) : IopSpec Fp Fp8 := Iop.verifierP Fp Fp8 AP prm

/-- Side conditions of v2's L3 (decidable on the concrete AIR): v1's `NpOk` for the
underlying AIR, and v2's well-formedness (budgets with public messages). -/
def NpOkP (AP : AirP) (prm : Params) : Prop :=
  NpOk AP.toAir prm ∧ AP.wf (2 ^ prm.logBlowup) = true

section
variable (AP : AirP) (prm : Params)

/-- The public vector of a transcript. -/
abbrev pubT (τ : PTn) : List Fp := pubOf Fp τ.cb

/-- The public segments do not fit (a function of the claim only). -/
def PubBad (τ : PTn) : Prop := pubFit AP (pubT τ) = false

/-- Public messages of side `s` as fingerprint coefficient lists `m ‖ (bus+1)`,
multiplicity one. -/
def pubBM (τ : PTn) (s : Bool) : List (List Fp8 × Nat) :=
  ((pubMsgs AP (pubT τ)).filter fun x => x.2.1 == s).map fun x =>
    (x.2.2.map Fp8.ofBase ++ [((x.1 + 1 : Nat) : Fp8)], 1)

/-- Trace and public contributions of one side. -/
noncomputable def busMsgsP (τ : PTn) (s : Bool) : List (List Fp8 × Nat) :=
  busMsgs AP.toAir prm τ s ++ pubBM AP τ s

/-- The fingerprint multisets of the two sides differ (public messages included). -/
noncomputable def FpDifferP (τ : PTn) (α : Fp8) : Prop :=
  ¬ ((expand (busMsgsP AP prm τ true)).map (fpL α)).Perm ((expand (busMsgsP AP prm τ false)).map (fpL α))

/-- The grand products of the two sides differ (public messages included). -/
noncomputable def GpDifferP (τ : PTn) (α γ : Fp8) : Prop :=
  ((expand (busMsgsP AP prm τ true)).map fun m => γ - fpL α m).prod ≠
    ((expand (busMsgsP AP prm τ false)).map fun m => γ - fpL α m).prod

/-- `Π_pub(s)` as L3 sees it. -/
def pubGp (τ : PTn) (α γ : Fp8) (s : Bool) : Fp8 :=
  ((expand (pubBM AP τ s)).map fun m => γ - fpL α m).prod

/-- The finals split per table (as `globalChecks` slices them). -/
def finsSplit (τ : PTn) : List (List Fp8) :=
  ((layOf AP.toAir prm τ).foldl (fun (acc : List (List Fp8) × List Fp8) L =>
      (acc.1 ++ [acc.2.take (L.sendG + L.recvG)], acc.2.drop (L.sendG + L.recvG))) ([], finalsOf τ)).1

/-- Product of the send finals. -/
def finSends (τ : PTn) : Fp8 :=
  (((finsSplit AP prm τ).zip (layOf AP.toAir prm τ)).map fun (f, L) =>
    (f.take L.sendG).foldl (· * ·) 1).foldl (· * ·) 1

/-- Product of the receive finals. -/
def finRecvs (τ : PTn) : Fp8 :=
  (((finsSplit AP prm τ).zip (layOf AP.toAir prm τ)).map fun (f, L) =>
    (f.drop L.sendG).foldl (· * ·) 1).foldl (· * ·) 1

theorem busFinalsFail_iff (τ : PTn) :
    BusFinalsFail AP.toAir prm τ ↔ finSends AP prm τ ≠ finRecvs AP prm τ := Iff.rfl

/-- The v2 bus equation on the clear-text finals fails. -/
def BusFinalsFailP (τ : PTn) (α γ : Fp8) : Prop :=
  finSends AP prm τ * pubGp AP τ α γ true ≠ finRecvs AP prm τ * pubGp AP τ α γ false

/-- v2's clear-text checks fail on the claimed OOD values. -/
def GlobalFailP (τ : PTn) : Prop :=
  match τ.chals, τ.elems with
  | αfp :: γ :: αc :: z :: _, finals :: ood :: _ =>
    globalChecksP (F := Fp) AP prm (pubT τ) (layOf AP.toAir prm τ)
      (splitOod (layOf AP.toAir prm τ) ood).1 finals αfp γ αc z = false
  | _, _ => False

/-- **L3's doomed stages for v2** (on shaped transcripts with fitting segments). -/
noncomputable def StageP (τ : PTn) : Prop :=
  let A := AP.toAir
  let ch := fun k => τ.chals.getD k 0
  let pub := pubT τ
  match τ.entries.length with
  | 0 => ¬ AirLangP AP τ.cb
  | 1 => ¬ AllClose A prm τ 1 ∨ ¬ HoldsP AP pub (decTrace A prm τ)
  | 2 | 3 => ¬ AllClose A prm τ 1 ∨ LocalFail A prm τ ∨ FpDifferP AP prm τ (ch 0)
  | 4 => ¬ AllClose A prm τ 1 ∨ LocalFail A prm τ ∨ GpDifferP AP prm τ (ch 0) (ch 1)
  | 5 => ¬ AllClose A prm τ 2 ∨ CsFailH A prm τ (ch 0) (ch 1) ∨ BusFinalsFailP AP prm τ (ch 0) (ch 1)
  | 6 => ¬ AllClose A prm τ 2 ∨
      (∃ t, t < A.tables.length ∧ ∃ r, r < 2 ^ (tl A prm τ t).log ∧
        Ct A prm τ t (ch 0) (ch 1) (ch 2) (omg (tl A prm τ t).log ^ r) ≠ 0) ∨
      BusFinalsFailP AP prm τ (ch 0) (ch 1)
  | 7 => ¬ AllClose A prm τ 3 ∨
      (∃ t, t < A.tables.length ∧ ∃ x, Ct A prm τ t (ch 0) (ch 1) (ch 2) x ≠
        (x ^ (2 ^ (tl A prm τ t).log) - 1) * Qt A prm τ t x) ∨ BusFinalsFailP AP prm τ (ch 0) (ch 1)
  | 8 => ¬ (ch 3).IsBase ∧ (¬ AllClose A prm τ 3 ∨
      (∃ t, t < A.tables.length ∧ Ct A prm τ t (ch 0) (ch 1) (ch 2) (ch 3) ≠
        ((ch 3) ^ (2 ^ (tl A prm τ t).log) - 1) * Qt A prm τ t (ch 3)) ∨
      BusFinalsFailP AP prm τ (ch 0) (ch 1))
  | _ => GlobalFailP AP prm τ ∨
      ((∃ L ∈ layOf A prm τ, BatchFar A prm τ L.lde L.log) ∧ FriGoodSoFar A prm τ)

/-- The doomed predicate handed to L2: malformed transcripts, claims whose public
segments do not fit, and doomed stages. -/
noncomputable def DoomedP (τ : PTn) : Prop :=
  ¬ Shaped (VnpP AP prm) τ ∨ PubBad AP τ ∨ StageP AP prm τ

end

/-! ## The v2 verifier has v1's shape -/

section
variable (AP : AirP) (prm : Params)

theorem slots_eq {O : Type} (τ : PT Fp8 O) : (VnpP AP prm).slots τ = (Vnp AP.toAir prm).slots τ := by
  unfold IopSpec.slots; rfl

theorem shaped_iff (τ : PTn) : Shaped (VnpP AP prm) τ ↔ Shaped (Vnp AP.toAir prm) τ := by
  unfold Shaped; rw [slots_eq]; exact Iff.rfl

theorem nextIsProver_iff (τ : PTn) : (VnpP AP prm).NextIsProver τ ↔ (Vnp AP.toAir prm).NextIsProver τ := by
  unfold IopSpec.NextIsProver; rw [slots_eq]

theorem nextIsChal_iff (τ : PTn) : (VnpP AP prm).NextIsChal τ ↔ (Vnp AP.toAir prm).NextIsChal τ := by
  unfold IopSpec.NextIsChal; rw [slots_eq]

theorem atQuery_iff (τ : PTn) : (VnpP AP prm).AtQuery τ ↔ (Vnp AP.toAir prm).AtQuery τ := by
  unfold IopSpec.AtQuery; rw [slots_eq]

theorem domSize_eq (τ : PTn) : (VnpP AP prm).domSize τ = (Vnp AP.toAir prm).domSize τ := by
  unfold IopSpec.domSize; rfl

theorem trueOpenings_eq (τ : PTn) (x : Nat) :
    (VnpP AP prm).trueOpenings τ x = (Vnp AP.toAir prm).trueOpenings τ x := by
  unfold IopSpec.trueOpenings; rfl

theorem checksPassP_iff (τ : PTn) (x : Nat) (op : List (List (List Fp))) :
    (VnpP AP prm).ChecksPass τ x op ↔ (Vnp AP.toAir prm).ChecksPass τ x op :=
  checksPass_eq AP prm τ x op

end

/-! ## Obligations (v2 analogues of `Udr.Np.Statements`) -/

/-- A message transition at `E = k` (for claims whose segments fit). -/
def MsgAtP (k : Nat) : Prop :=
  ∀ (AP : AirP) (prm : Params), NpOkP AP prm → ∀ (τ : PTn) m, ¬ PubBad AP τ →
    Shaped (VnpP AP prm) (τ.push m) → (VnpP AP prm).NextIsProver τ → τ.entries.length = k →
    StageP AP prm τ → StageP AP prm (τ.push m)

/-- A challenge transition at `E = k` (for claims whose segments fit). -/
def ChalAtP (k : Nat) : Prop :=
  ∀ (AP : AirP) (prm : Params), NpOkP AP prm → ∀ τ : PTn, ¬ PubBad AP τ →
    Shaped (VnpP AP prm) τ → (VnpP AP prm).NextIsChal τ → τ.entries.length = k → StageP AP prm τ →
    count Fp8.all (fun c => Shaped (VnpP AP prm) (τ.pushChal c) ∧ ¬ StageP AP prm (τ.pushChal c)) ≤
      badBudget

def QueryStmtP : Prop :=
  ∀ (AP : AirP) (prm : Params), NpOkP AP prm → ∀ τ : PTn,
    StageP AP prm τ → (VnpP AP prm).AtQuery τ → Shaped (VnpP AP prm) τ →
    (VnpP AP prm).global ((VnpP AP prm).prep τ.erase) = true →
    count (List.range ((VnpP AP prm).domSize τ))
      (fun x => (VnpP AP prm).ChecksPass τ x ((VnpP AP prm).trueOpenings τ x)) ≤
      agreeUdr prm.logBlowup ((VnpP AP prm).domSize τ)

end ZkFormal.V2.Np
