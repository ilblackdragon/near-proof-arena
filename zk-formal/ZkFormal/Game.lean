import ZkFormal.Potential
import ZkFormal.BadQuery

/-!
# ZkFormal.Game — from ArenaCore's `RomSound` to a potential argument

The judge's ROM game (`ArenaCore.Security.romWins`) runs the adversary with
two oracles (`hash`, `prove`), the honest prover `P` answering `prove`
queries through the *same* lazy oracle, and then the deployed verifier `V`,
continuing the oracle state.  This file shows that for a prover and a
verifier given as **hash-query trees** (`TreeProver`, `TreeVerifier`) the
whole experiment is a single hash-query tree (`expt`), and derives

* `romSound_of_potential`: `RomSound` at the profile's budgets follows from
  1. a potential `Φ` on oracle logs with the one-step bound
     `StepBound Φ w C` (each fresh query of weight `w x ≤ 1` raises the
     expected potential by at most `C · w x`), and
  2. a **deterministic** acceptance lemma about the verifier tree alone:
     whenever `V` accepts a claim outside `L` without oracle overflow, the
     final log has potential `≥ M`.

The bound is `(Φ [] + C · (qH + qP·NPw + NVw)) / M` with tape length
`qH + qP·NPu + NVu`, so the tape never overflows.  Everything protocol-
specific (round-by-round doomed sets, Merkle extraction from the log, the
multi-symbol query phase) lives in `Φ` and in obligation 2; this file is the
generic Fiat–Shamir/BCS plumbing for the deployed non-interactive verifier
(DESIGN.md §6.1).

Tree-defined provers/verifiers are not a restriction of generality for us:
the candidate chooses `P` and the verifier model, and a native-lean verifier
written as a tree is compiled and deployed as `V.toVerifier.deployed`.
-/

namespace ZkFormal

open ArenaCore ArenaCore.Security

/-! ## Trees run against an arbitrary hash oracle -/

/-- Run a hash-query tree against any (stateful) hash oracle. -/
def runH {σ α : Type} (H : Interp.HashOracle σ) : OracleComp hashSpec α → σ → α × σ
  | .pure a, s => (a, s)
  | .query x k, s => runH H (k (H s x).1) (H s x).2

theorem runH_lazy {α : Type} (A : OracleComp hashSpec α) (s : LazyRO) :
    runH LazyRO.query A s = OracleComp.simulate hashImpl A s := by
  induction A generalizing s with
  | pure a => rfl
  | query x k ih => simp only [runH, OracleComp.simulate, hashImpl]; exact ih _ _

/-- An honest prover given as a hash-query tree. -/
structure TreeProver (S : ChallengeSpec) where
  tree : Bytes → S.Claim → S.Witness → OracleComp hashSpec Bytes

/-- A verifier given as a hash-query tree. -/
structure TreeVerifier where
  tree : Bytes → Bytes → Bytes → OracleComp hashSpec Bool

def TreeProver.toProver {S : ChallengeSpec} (P : TreeProver S) : OracleProver S :=
  ⟨fun H s pub c w => runH H (P.tree pub c w) s⟩

def TreeVerifier.toVerifier (V : TreeVerifier) : OracleVerifier :=
  ⟨fun H s pub cb pb => runH H (V.tree pub cb pb) s⟩

/-! ## Inlining the `prove` oracle -/

section
variable (S : ChallengeSpec) (P : TreeProver S) (pub : Bytes)

open Classical in
/-- Replace each `prove cb w` query by the honest prover's tree (on true
statements; `[]` otherwise, exactly as `romImpl`). -/
noncomputable def inline {α : Type} : OracleComp (romSpec S.Witness) α → OracleComp hashSpec α
  | .pure a => .pure a
  | .query (.hash x) k => .query x fun y => inline (k y)
  | .query (.prove cb w) k =>
    match S.decodeClaim cb with
    | some c => if S.Rel c w then OracleComp.bind (P.tree pub c w) fun r => inline (k r)
                else inline (k [])
    | none => inline (k [])

theorem simulate_inline {α : Type} (A : OracleComp (romSpec S.Witness) α) (s : LazyRO) :
    OracleComp.simulate (romImpl S P.toProver pub) A s =
      OracleComp.simulate hashImpl (inline S P pub A) s := by
  classical
  induction A generalizing s with
  | pure a => rfl
  | query q k ih =>
    cases q with
    | hash x =>
      simp only [OracleComp.simulate, romImpl, inline, hashImpl]
      exact ih _ _
    | prove cb w =>
      simp only [OracleComp.simulate, romImpl, inline]
      cases hd : S.decodeClaim cb with
      | none => simp only; exact ih _ _
      | some c =>
        simp only
        by_cases hr : S.Rel c w
        · simp only [hr, ite_true, simulate_bind, TreeProver.toProver, runH_lazy]
          exact ih _ _
        · simp only [hr, ite_false]
          exact ih _ _

end

/-! ## Query budgets -/

theorem QueryBound.bind {spec : OracleSpec} {α β : Type} {w : spec.Query → Nat}
    {oa : OracleComp spec α} {f : α → OracleComp spec β} {a b : Nat}
    (h : OracleComp.QueryBound w oa a) (hf : ∀ r, OracleComp.QueryBound w (f r) b) :
    OracleComp.QueryBound w (OracleComp.bind oa f) (a + b) := by
  induction h with
  | pure x a => exact (hf x).mono (Nat.le_add_left _ _)
  | query q k a hq _ ih =>
    refine .query q _ (a + b) (Nat.le_trans hq (Nat.le_add_right _ _)) fun r => ?_
    have e : a - w q + b = a + b - w q := by omega
    rw [← e]; exact ih r

theorem inline_queryBound {S : ChallengeSpec} (P : TreeProver S) (pub : Bytes)
    (w : Bytes → Nat) (hw1 : ∀ x, w x ≤ 1) (NP : Nat)
    (hP : ∀ c wit, OracleComp.QueryBound w (P.tree pub c wit) NP) {α : Type} :
    ∀ (A : OracleComp (romSpec S.Witness) α) (qH qP : Nat),
      OracleComp.QueryBound hashWeight A qH → OracleComp.QueryBound proveWeight A qP →
      OracleComp.QueryBound w (inline S P pub A) (qH + qP * NP) := by
  classical
  intro A
  induction A with
  | pure a => intro qH qP _ _; exact .pure _ _
  | query q k ih =>
    intro qH qP hH hPr
    cases hH with
    | query _ _ _ hwH hkH =>
    cases hPr with
    | query _ _ _ hwP hkP =>
    cases q with
    | hash x =>
      simp only [hashWeight, proveWeight, Nat.sub_zero] at hwH hkH hkP
      show OracleComp.QueryBound w (OracleComp.query (spec := hashSpec) x fun y => inline S P pub (k y))
        (qH + qP * NP)
      have h1 := hw1 x
      refine OracleComp.QueryBound.query (spec := hashSpec) (w := w) x _ (qH + qP * NP)
        (by omega) fun y => ?_
      exact (ih y (qH - 1) qP (hkH y) (hkP y)).mono (by omega)
    | prove cb wit =>
      simp only [hashWeight, proveWeight, Nat.sub_zero] at hwP hkH hkP
      simp only [inline]
      have hk : ∀ r, OracleComp.QueryBound w (inline S P pub (k r)) (qH + (qP - 1) * NP) :=
        fun r => ih r qH (qP - 1) (hkH r) (hkP r)
      have e : qH + qP * NP = NP + (qH + (qP - 1) * NP) := by
        obtain ⟨m, rfl⟩ : ∃ m, qP = m + 1 := ⟨qP - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.succ_mul]; omega
      cases S.decodeClaim cb with
      | none => exact (hk []).mono (by rw [e]; exact Nat.le_add_left _ _)
      | some c =>
        simp only
        split
        · rw [e]; exact QueryBound.bind (hP c wit) hk
        · exact (hk []).mono (by rw [e]; exact Nat.le_add_left _ _)

/-! ## The whole experiment as one tree -/

/-- Adversary (with inlined honest prover), then the verifier on its output. -/
noncomputable def expt {S : ChallengeSpec} (P : TreeProver S) (V : TreeVerifier) (pub : Bytes)
    (A : RomAdversary S) : OracleComp hashSpec (Bytes × Bool) :=
  OracleComp.bind (inline S P pub A) fun out =>
    OracleComp.bind (V.tree pub out.1 out.2) fun acc => .pure (out.1, acc)

theorem simulate_expt {S : ChallengeSpec} (P : TreeProver S) (V : TreeVerifier) (pub : Bytes)
    (A : RomAdversary S) (s : LazyRO) :
    let r1 := OracleComp.simulate hashImpl (inline S P pub A) s
    let r2 := OracleComp.simulate hashImpl (V.tree pub r1.1.1 r1.1.2) r1.2
    OracleComp.simulate hashImpl (expt P V pub A) s = ((r1.1.1, r2.1), r2.2) := by
  simp only [expt, simulate_bind, OracleComp.simulate]

theorem romWins_iff {S : ChallengeSpec} (L : Bytes → Prop) (P : TreeProver S) (V : TreeVerifier)
    (pub : Bytes) (A : RomAdversary S) (tape : List Nat) :
    romWins S L V.toVerifier P.toProver pub A tape ↔
      let r := OracleComp.simulate hashImpl (expt P V pub A) (LazyRO.init tape)
      r.2.overflow = true ∨ (r.1.2 = true ∧ ¬ L r.1.1) := by
  simp only [romWins, simulate_inline, simulate_expt, TreeVerifier.toVerifier, runH_lazy]

/-- **ROM soundness from a potential.**  The generic Fiat–Shamir/BCS step:
`RomSound` for the deployed (tree-defined) verifier follows from a potential
on oracle logs (`hΦ`) and a deterministic acceptance lemma (`hacc`). -/
theorem romSound_of_potential {S : ChallengeSpec} (L : Bytes → Prop)
    (P : TreeProver S) (V : TreeVerifier) (pub : Bytes)
    (qH qP NPu NVu : Nat)
    (hPu : ∀ c wit, OracleComp.QueryBound unitWeight (P.tree pub c wit) NPu)
    (hVu : ∀ cb pb, OracleComp.QueryBound unitWeight (V.tree pub cb pb) NVu)
    (w : Bytes → Nat) (hw1 : ∀ x, w x ≤ 1) (NPw NVw : Nat)
    (hPw : ∀ c wit, OracleComp.QueryBound w (P.tree pub c wit) NPw)
    (hVw : ∀ cb pb, OracleComp.QueryBound w (V.tree pub cb pb) NVw)
    (Φ : Table → Nat) (C M : Nat) (hM : 0 < M) (hΦ : StepBound Φ w C)
    (hacc : ∀ (s : LazyRO) (cb pb : Bytes),
      (OracleComp.simulate hashImpl (V.tree pub cb pb) s).2.overflow = false →
      (OracleComp.simulate hashImpl (V.tree pub cb pb) s).1 = true → ¬ L cb →
      M ≤ Φ (OracleComp.simulate hashImpl (V.tree pub cb pb) s).2.table) :
    RomSound S L V.toVerifier P.toProver pub qH qP (qH + qP * NPu + NVu)
      (Φ [] + C * (qH + qP * NPw + NVw)) M := by
  intro A hH hPr
  -- budgets of the whole experiment
  let f : Bytes × Bytes → OracleComp hashSpec (Bytes × Bool) := fun out =>
    OracleComp.bind (V.tree pub out.1 out.2) fun acc => .pure (out.1, acc)
  have hEw : OracleComp.QueryBound w (expt P V pub A) (qH + qP * NPw + NVw) := by
    have h := QueryBound.bind (f := f) (b := NVw + 0)
      (inline_queryBound P pub w hw1 NPw hPw A qH qP hH hPr)
      fun out => QueryBound.bind (hVw out.1 out.2) fun acc => .pure (out.1, acc) 0
    simpa [expt] using h
  have hEu : OracleComp.QueryBound unitWeight (expt P V pub A) (qH + qP * NPu + NVu) := by
    have h := QueryBound.bind (f := f) (b := NVu + 0)
      (inline_queryBound P pub unitWeight (fun _ => Nat.le_refl 1) NPu hPu A qH qP hH hPr)
      fun out => QueryBound.bind (hVu out.1 out.2) fun acc => .pure (out.1, acc) 0
    simpa [expt] using h
  refine prLE_of_potential hΦ hEw _ [] false _ M hM ?_
  intro t ht hwin
  rw [romWins_iff] at hwin
  -- no overflow: the tape is as long as the total query budget
  obtain ⟨k', _, hinv⟩ := LazyInv.simulate hEu (LazyInv.init t) (by omega)
  have hov := hinv.2.1
  simp only at hwin
  rcases hwin with hwin | ⟨hacc', hnl⟩
  · rw [hov] at hwin; cases hwin
  · rw [simulate_expt] at hacc' hnl hov
    simp only at hacc' hnl hov
    have := hacc _ _ _ hov hacc' hnl
    show M ≤ Φ (finalTable (expt P V pub A) (LazyRO.init t))
    unfold finalTable
    rw [simulate_expt]
    exact this

end ZkFormal
