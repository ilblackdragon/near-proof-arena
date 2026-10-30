import NearSpecV3.Successor.TierO4NS

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O4 — simulation and refinement up to the named escapes (README §14)

`Sim` (`TierO4Engine.lean`) asks the recorder to reproduce every legacy decision. Where the recorder
excludes (or, G4, rejects) for one of the named reasons `esc` (G2 fuel certificate, G3 preparation
race, G3b rolled-back-deploy code, G4 V3 empty-buffer assertion, G7 global action), that is false
for some values, so it cannot be proved for every value (§13). `SimX` and `RefinesX` allow exactly
those failures on the recorder side:

* `SimX e P φ x y`: `Sim`, or the recorder fails with an `esc` string;
* `RefinesX x y`: `Refines x y`, or `y` fails with an `esc` string.

The lockstep shell walk of §10 (`o4_lockstep`) is repeated for `RefinesX` (`o4x_lockstep`), so an
engine-level `EngineRefX` gives a shell-level `RefinesX` (`checkD2CoreGWith_legacy_ns`), and the
premise "the storage-resolution result is not an escape" turns `RefinesX` back into `Refines`.
-/

namespace NearSpecV3.Successor.O4E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged
open NearSpecV3.Successor
open NearSpecV3.Successor.StorageExecution (M Recording)

/-! ## `SimX` -/

/-- `SimAt`, or the recorder fails with a named escape. -/
def SimAtX {α β : Type} (e : Env) (P : Recording → Prop) (φ : β → α) (x : Except String α) (y : M β)
    (r : Recording) : Prop :=
  SimAt e P φ x y r ∨ ∃ s, esc s = true ∧ y.run r e = .error s

def SimX {α β : Type} (e : Env) (P : Recording → Prop) (φ : β → α) (x : Except String α) (y : M β) :
    Prop :=
  ∀ r, P r → SimAtX e P φ x y r

/-- The relation of two `Except` values up to a legacy exclusion and a recorder escape. -/
def RelE {α : Type} (x y : Except String α) : Prop :=
  x = y ∨ (∃ err, x = .error err ∧ isExclusion err = true) ∨ ∃ s, esc s = true ∧ y = .error s

namespace SimX
variable {e : Env} {P : Recording → Prop}

theorem of {α β : Type} {φ : β → α} {x : Except String α} {y : M β} (h : Sim e P φ x y) :
    SimX e P φ x y := fun r hr => Or.inl (h r hr)

theorem bind {α α' β β' : Type} {φ : β → α} {ψ : β' → α'}
    {x : Except String α} {y : M β} {f : α → Except String α'} {g : β → M β'}
    (hxy : SimX e P φ x y) (hfg : ∀ b, SimX e P ψ (f (φ b)) (g b)) :
    SimX e P ψ (x >>= f) (y >>= g) := by
  intro r hr
  rcases hxy r hr with h1 | ⟨s, hs, hy⟩
  · unfold SimAt at h1
    cases hx : x with
    | error err =>
      rw [hx] at h1
      refine Or.inl ?_
      unfold SimAt
      rcases h1 with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [Sim.run_bind, h]; rfl)
    | ok a =>
      rw [hx] at h1
      obtain ⟨b, r', hy, rfl, hr'⟩ := h1
      rcases hfg b r' hr' with h2 | ⟨s, hs, hg⟩
      · refine Or.inl ?_
        unfold SimAt at h2 ⊢
        show match f (φ b) with
          | .ok a => ∃ b r'', (y >>= g).run r e = .ok (b, r'') ∧ a = ψ b ∧ P r''
          | .error err => isExclusion err = true ∨ (y >>= g).run r e = .error err
        rw [Sim.run_bind, hy]
        exact h2
      · exact Or.inr ⟨s, hs, by rw [Sim.run_bind, hy]; exact hg⟩
  · exact Or.inr ⟨s, hs, by rw [Sim.run_bind, hy]; rfl⟩

theorem bind_id {α α' β' : Type} {ψ : β' → α'}
    {x : Except String α} {y : M α} {f : α → Except String α'} {g : α → M β'}
    (hxy : SimX e P id x y) (hfg : ∀ b, SimX e P ψ (f b) (g b)) :
    SimX e P ψ (x >>= f) (y >>= g) := bind hxy hfg

theorem ite {α β : Type} {φ : β → α} (c : Prop) [Decidable c] {x x' : Except String α} {y y' : M β}
    (h : c → SimX e P φ x y) (h' : ¬c → SimX e P φ x' y') :
    SimX e P φ (if c then x else x') (if c then y else y') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h hc
  · simp only [hc, ite_false]; exact h' hc

theorem ite_iff {α β : Type} {φ : β → α} (c c' : Prop) [Decidable c] [Decidable c'] (hc : c ↔ c')
    {x x' : Except String α} {y y' : M β}
    (h : c → SimX e P φ x y) (h' : ¬c → SimX e P φ x' y') :
    SimX e P φ (if c then x else x') (if c' then y else y') := by
  by_cases hcc : c
  · simp only [hcc, hc.mp hcc, ite_true]; exact h hcc
  · have : ¬c' := fun h => hcc (hc.mpr h)
    simp only [hcc, this, ite_false]; exact h' hcc

theorem ite_right {α β : Type} {φ : β → α} (c : Prop) [Decidable c] {x : Except String α} {y y' : M β}
    (h : c → SimX e P φ x y) (h' : ¬c → SimX e P φ x y') : SimX e P φ x (if c then y else y') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h hc
  · simp only [hc, ite_false]; exact h' hc

theorem book {α β γ : Type} {ψ : β → α} {x : Except String α} {B : M γ} {c : γ} {g : γ → M β}
    (hP : PFrame P) (hB : Book e B c) (h : SimX e P ψ x (g c)) : SimX e P ψ x (B >>= g) := by
  intro r hr
  obtain ⟨r', hrun, h1, h2⟩ := hB r
  rcases h r' (hP r r' h1 h2 hr) with h' | ⟨s, hs, hg⟩
  · refine Or.inl ?_
    unfold SimAt at h' ⊢
    rw [Sim.run_bind, hrun]
    exact h'
  · exact Or.inr ⟨s, hs, by rw [Sim.run_bind, hrun]; exact hg⟩

theorem get_all {α β : Type} {ψ : β → α} {x : Except String α} {g : Recording → M β}
    (h : ∀ r0, SimX e P ψ x (g r0)) : SimX e P ψ x (MonadState.get >>= g) := fun r hr => h r r hr

theorem foldlM {γ α β : Type} {φ : β → α} {f : α → γ → Except String α} {g : β → γ → M β}
    (hfg : ∀ b c, SimX e P φ (f (φ b) c) (g b c)) :
    ∀ (l : List γ) (b : β), SimX e P φ (l.foldlM f (φ b)) (l.foldlM g b)
  | [], b => of (Sim.pure rfl)
  | c :: l, b => by
    simp only [List.foldlM_cons]
    exact bind (hfg b c) fun b' => foldlM hfg l b'

theorem foldlM' {γ α β : Type} {φ : β → α} {f : α → γ → Except String α} {g : β → γ → M β}
    (hfg : ∀ b c, SimX e P φ (f (φ b) c) (g b c)) (l : List γ) {a : α} {b : β} (hab : a = φ b) :
    SimX e P φ (l.foldlM f a) (l.foldlM g b) := hab ▸ foldlM hfg l b

theorem congr_left {α β : Type} {φ : β → α} {x x' : Except String α} {y : M β} (h : x = x')
    (h' : SimX e P φ x' y) : SimX e P φ x y := h ▸ h'

theorem logged_ok_bind {α β γ : Type} {ψ : β → α} {x : Except String α} {n : LM γ} {c : γ} {g : γ → M β}
    (hev : LM.ev e.store e.preRoot n = .ok c)
    (hP : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder })
    (h : SimX e P ψ x (g c)) : SimX e P ψ x (StorageExecution.logged n >>= g) := by
  intro r hr
  rcases h _ (hP r (Logged.SM.reads (hGet e.store) (n e.preRoot)) hr) with h' | ⟨s, hs, hg⟩
  · refine Or.inl ?_
    unfold SimAt at h' ⊢
    rw [Sim.run_bind, logged_run, hev]
    exact h'
  · exact Or.inr ⟨s, hs, by rw [Sim.run_bind, logged_run, hev]; exact hg⟩

theorem bind_book {α β : Type} {φ : β → α} {x : Except String α} {y : M β} {g : β → M β}
    (hP : PFrame P) (hxy : SimX e P φ x y) (hg : ∀ b, Book e (g b) b) : SimX e P φ x (y >>= g) := by
  have := bind (f := fun a => (Pure.pure a : Except String α)) (ψ := φ) hxy fun b =>
    fun r hr => Or.inl (Sim.pure_book hP (hg b) rfl r hr)
  simpa only [bind_pure] using this

/-- A named recorder escape is simulated against anything. -/
theorem escape {α β : Type} {φ : β → α} {x : Except String α} (s : String) (hs : esc s = true) :
    SimX e P φ x (MonadExcept.throw s : M β) := fun _ _ => Or.inr ⟨s, hs, rfl⟩

/-- A recorder `liftE` of an `Except` value related to the legacy one by `RelE`. -/
theorem liftE_rel {α : Type} {x y : Except String α} (h : RelE x y) :
    SimX e P id x (StorageExecution.liftE y) := by
  intro r hr
  rcases h with rfl | ⟨err, rfl, he⟩ | ⟨s, hs, rfl⟩
  · exact Or.inl (Sim.liftE x r hr)
  · exact Or.inl (Or.inl he)
  · exact Or.inr ⟨s, hs, rfl⟩

end SimX

/-! ## The engine relation up to the escapes -/

/-- `EngineRef`, or the recorder fails with a named escape. -/
def EngineRefX (base : Nat) (x y : Except String MainOutD2) : Prop :=
  (∀ e, x = .error e → isExclusion e = false → base ≤ legacyStorageBound →
      y = .error e ∨ ∃ s, esc s = true ∧ y = .error s) ∧
    (∀ out, x = .ok out → legacySizeOk base out.cdRemovals = true →
      y = .ok out ∨ ∃ s, esc s = true ∧ y = .error s)

/-- `EngineAgree` for the `NS` engine, up to the escapes. -/
def EngineAgreeX (cfg : Wasm.NearCfg) : Prop :=
  ∀ (merged : List Bytes) (p : Prims) (e : Env) (vu : Option ValidatorUpdateFacts)
    (ps : List (Bytes × Nat)) (rs : List Rcpt) (txs : List (TxD2 × Bool)) (cg : Congestion),
    e.store = mkHStore merged →
    EngineRefX (mergedBytes merged)
      ((applyNewChunkD2 (D3.d3Hooks cfg) p e (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg).map obsClear)
      ((StorageExecutionNS.run cfg p e (revealAll e.store revealFuel e.preRoot) vu ps rs txs cg).map obsClear)

/-- **Bridge.** A `SimX` of the main transition from the initial recorder state gives `EngineAgreeX`. -/
theorem engineAgreeX_of_simX (cfg : Wasm.NearCfg) (P : Recording → Prop)
    (hinit : P { observe := cfg.observeDetail })
    (h : ∀ (merged : List Bytes) (p : Prims) (e : Env) (vu : Option ValidatorUpdateFacts)
      (ps : List (Bytes × Nat)) (rs : List Rcpt) (txs : List (TxD2 × Bool)) (cg : Congestion),
      e.store = mkHStore merged →
      SimX e P obsClear (D2.applyNewChunkD2 (D3.d3Hooks cfg) p e (T e) vu ps rs txs cg)
        (StorageExecutionNS.applyNewChunkD2 cfg p e (T e) vu ps rs txs cg)) :
    EngineAgreeX cfg := by
  intro merged p e vu ps rs txs cg he
  have h0 := h merged p e vu ps rs txs cg he _ hinit
  refine ⟨fun err hx hne _ => ?_, fun out hx _ => ?_⟩
  · cases hl : D2.applyNewChunkD2 (D3.d3Hooks cfg) p e (T e) vu ps rs txs cg with
    | ok a => rw [hl] at hx; cases hx
    | error err' =>
      rw [hl] at hx
      cases hx
      rcases h0 with h0 | ⟨s, hs, hy⟩
      · unfold SimAt at h0
        rw [hl] at h0
        rcases h0 with h0 | h0
        · rw [hne] at h0; cases h0
        · left; unfold StorageExecutionNS.run; rw [h0]; rfl
      · right; exact ⟨s, hs, by unfold StorageExecutionNS.run; rw [hy]; rfl⟩
  · cases hl : D2.applyNewChunkD2 (D3.d3Hooks cfg) p e (T e) vu ps rs txs cg with
    | error err' => rw [hl] at hx; cases hx
    | ok a =>
      rw [hl] at hx
      cases hx
      rcases h0 with h0 | ⟨s, hs, hy⟩
      · unfold SimAt at h0
        rw [hl] at h0
        obtain ⟨b, r', hy, rfl, _⟩ := h0
        left; unfold StorageExecutionNS.run; rw [hy]; rfl
      · right; exact ⟨s, hs, by unfold StorageExecutionNS.run; rw [hy]; rfl⟩

/-! ## `RefinesX` and the shell walk -/

/-- `Refines`, or the right side fails with a named escape. -/
def RefinesX {α : Type} (x y : Except String α) : Prop :=
  Refines x y ∨ ∃ s, esc s = true ∧ y = .error s

namespace RefinesX

theorem of {α : Type} {x y : Except String α} (h : Refines x y) : RefinesX x y := Or.inl h

theorem refl {α : Type} (x : Except String α) : RefinesX x x := of (Refines.refl x)

theorem bind {α β : Type} {x y : Except String α} {f g : α → Except String β}
    (hxy : RefinesX x y) (hfg : ∀ a, RefinesX (f a) (g a)) : RefinesX (x >>= f) (y >>= g) := by
  rcases hxy with (rfl | ⟨e, rfl, he⟩) | ⟨s, hs, rfl⟩
  · cases x with
    | error e => exact refl _
    | ok a => exact hfg a
  · exact of (Or.inr ⟨e, rfl, he⟩)
  · exact Or.inr ⟨s, hs, rfl⟩

theorem bind' {α β : Type} {x y : Except String α} {f g : α → Except String β}
    (hxy : x = y) (hfg : ∀ a, RefinesX (f a) (g a)) : RefinesX (x >>= f) (y >>= g) := by
  subst hxy; exact bind (refl _) hfg

theorem bind_ok {α β : Type} {x : Except String α} {f g : α → Except String β}
    (hfg : ∀ a, x = .ok a → RefinesX (f a) (g a)) : RefinesX (x >>= f) (x >>= g) := by
  cases hx : x with
  | error e => exact refl _
  | ok a => exact hfg a hx

theorem throw_bind {α β : Type} (e : String) (f g : α → Except String β) :
    RefinesX ((Except.error e : Except String α) >>= f) ((Except.error e : Except String α) >>= g) :=
  refl _

theorem throw_bind'' {α β : Type} (e : String) (f g : α → Except String β) :
    RefinesX ((throw e : Except String α) >>= f) ((throw e : Except String α) >>= g) := refl _

theorem map {α β : Type} {x y : Except String α} (f : α → β) (h : RefinesX x y) :
    RefinesX (x.map f) (y.map f) := by
  rcases h with h | ⟨s, hs, rfl⟩
  · exact of (Refines.map f h)
  · exact Or.inr ⟨s, hs, rfl⟩

theorem ite_congr {β : Type} (c : Prop) [Decidable c] {t t' e e' : Except String β}
    (ht : c → RefinesX t t') (he : ¬c → RefinesX e e') :
    RefinesX (if c then t else e) (if c then t' else e') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact ht hc
  · simp only [hc, ite_false]; exact he hc

theorem ite_bind_join {β : Type} (c : Prop) [Decidable c] (x₁ x₂ : Except String Unit)
    {K K' : Unit → Except String β} (hK : ∀ u, RefinesX (K u) (K' u)) :
    RefinesX (if c then x₁ >>= K else x₂ >>= K) (if c then x₁ >>= K' else x₂ >>= K') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact bind (refl _) hK
  · simp only [hc, ite_false]; exact bind (refl _) hK

theorem ite_bind_skip {β : Type} (c : Prop) [Decidable c] (x : Except String Unit)
    {K K' : Except String β} (hK : RefinesX K K') :
    RefinesX (if c then x >>= (fun _ => K) else K) (if c then x >>= (fun _ => K') else K') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact bind (refl _) fun _ => hK
  · simp only [hc, ite_false]; exact hK

theorem check_bind_left {β : Type} (b : Bool) (m : String) (hm : isExclusion m = true)
    {f : Unit → Except String β} {g : Except String β} (hfg : ∀ u, RefinesX (f u) g) :
    RefinesX (check b m >>= f) g := by
  unfold check; cases b
  · exact of (Or.inr ⟨m, rfl, hm⟩)
  · exact hfg ()

theorem check_bind_right {β : Type} {x : Except String β} (b : Bool) (m : String) (hb : b = true)
    {g : Unit → Except String β} (h : RefinesX x (g ())) : RefinesX x (check b m >>= g) := by
  subst hb; exact h

theorem check_pure (b : Bool) (m : String) (hm : isExclusion m = true) :
    RefinesX (check b m) (pure ()) := of (Refines.check_pure b m hm)

theorem forIn_congr {α σ : Type} (l : List α) (b : σ)
    {f g : α → σ → Except String (ForInStep σ)} (h : ∀ a s, RefinesX (f a s) (g a s)) :
    RefinesX (forIn l b f) (forIn l b g) := by
  induction l generalizing b with
  | nil => exact refl _
  | cons a t ih =>
    simp only [List.forIn_cons]
    refine bind (h a b) fun r => ?_
    cases r with
    | done s => exact refl _
    | yield s => exact ih s

/-- The main-transition step up to the escapes. -/
theorem engine_bind {β : Type} {base : Nat} {x y : Except String MainOutD2}
    (h : EngineRefX base x y) (hb : base ≤ legacyStorageBound) (m m' : String) (hm : isExclusion m = true)
    {K K' : MainOutD2 → Except String β} (hK : ∀ out, RefinesX (K out) (K' out)) :
    RefinesX (x >>= fun out => check (legacySizeOk base out.cdRemovals) m >>= fun _ => K out)
      (y >>= fun out => check true m' >>= fun _ => K' out) := by
  cases hx : x with
  | error e =>
    cases he : isExclusion e
    · rcases h.1 e hx he hb with hy | ⟨s, hs, hy⟩
      · rw [hy]; exact refl _
      · rw [hy]; exact Or.inr ⟨s, hs, rfl⟩
    · exact of (Or.inr ⟨e, rfl, he⟩)
  | ok out =>
    cases hs : legacySizeOk base out.cdRemovals
    · exact of (Or.inr ⟨m, by simp [check, hs], hm⟩)
    · rcases h.2 out hx hs with hy | ⟨s, hs', hy⟩
      · rw [hy]
        change RefinesX (check (legacySizeOk base out.cdRemovals) m >>= fun _ => K out)
          (check true m' >>= fun _ => K' out)
        rw [hs]; exact hK out
      · rw [hy]; exact Or.inr ⟨s, hs', rfl⟩

end RefinesX

/-- `o4_lockstep` for `RefinesX`. -/
macro "o4x_lockstep" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact RefinesX.refl _)
    | (exact RefinesX.throw_bind _ _ _)
    | (exact RefinesX.throw_bind'' _ _ _)
    | (with_reducible assumption)
    | (refine RefinesX.engine_bind (‹EngineAgreeX _› _ _ _ _ _ _ _ _ rfl) ‹_› _ _ (by ood_tac) fun _ => ?_)
    | ((refine RefinesX.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine RefinesX.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine RefinesX.ite_bind_join _ _ _ fun _ => ?_)
    | (refine RefinesX.ite_bind_skip _ _ ?_)
    | (refine RefinesX.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine RefinesX.bind (by with_reducible assumption) fun _ => ?_); try dsimp only)
    | (refine RefinesX.check_bind_left _ _ (by ood_tac) fun _ => ?_)
    | (refine RefinesX.check_bind_right _ _ rfl ?_)
    | ((refine RefinesX.bind (RefinesX.check_pure _ _ (by ood_tac)) fun _ => ?_); try dsimp only)
    | ((refine RefinesX.bind (RefinesX.forIn_congr _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine RefinesX.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine RefinesX.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

set_option maxHeartbeats 16000000 in
theorem checkD2CoreWithObs_legacy_ns (cfg : Wasm.NearCfg) (hE : EngineAgreeX cfg)
    (c w : Bytes) (hw : O4Witness w) (hB : legacyMergedBytes w ≤ legacyStorageBound) (g : Option Nat) :
    RefinesX (checkD2CoreWithObs legacyDriver.clearObs (D3.d3Hooks cfg) true c w g)
      (checkD2CoreWithObs (recorderDriverNS cfg).clearObs (D3.d3Hooks cfg) true c w g) := by
  unfold checkD2CoreWithObs
  simp only [ExecutionDriver.clearObs, legacyDriver, recorderDriverNS, recorderDriver, Bool.false_eq_true,
    ↓reduceIte, Bool.not_true, decodeWitnessFileV_of_not_c w hw.1]
  refine RefinesX.bind' rfl fun cl => ?_
  refine RefinesX.bind_ok fun ⟨sw, codes⟩ hd => ?_
  refine RefinesX.check_bind_right _ _ (decide_eq_true (hw.2 sw codes hd)) ?_
  simp only [Bool.not_false, ↓reduceIte]
  refine RefinesX.bind' rfl fun _ => ?_
  refine RefinesX.bind_ok fun sw' hdw => ?_
  have hb : mergedBytes (sw'.main.values ++ codes) ≤ legacyStorageBound := by
    rw [← legacyMergedBytes_of_decode hd hdw]; exact hB
  o4x_lockstep

theorem checkD2CoreWith_legacy_ns (cfg : Wasm.NearCfg) (hE : EngineAgreeX cfg)
    (c w : Bytes) (hw : O4Witness w) (hB : legacyMergedBytes w ≤ legacyStorageBound) (g : Option Nat) :
    RefinesX (checkD2CoreWith legacyDriver (D3.d3Hooks cfg) true c w g)
      (checkD2CoreWith (recorderDriverNS cfg) (D3.d3Hooks cfg) true c w g) := by
  rw [← checkD2CoreWith_clearObs legacyDriver, ← checkD2CoreWith_clearObs (recorderDriverNS cfg)]
  exact RefinesX.map _ (checkD2CoreWithObs_legacy_ns cfg hE c w hw hB g)

set_option maxHeartbeats 16000000 in
/-- **Shell level, up to the escapes.** -/
theorem checkD2CoreGWith_legacy_ns (cfg : Wasm.NearCfg) (hE : EngineAgreeX cfg)
    (c w : Bytes) (hw : O4Witness w) (hB : legacyMergedBytes w ≤ legacyStorageBound) (g : Option Nat) :
    RefinesX (checkD2CoreG (D3.d3Hooks cfg) true c w g)
      (checkD2CoreGWith (recorderDriverNS cfg) (D3.d3Hooks cfg) true c w g) := by
  have hW : RefinesX (checkD2CoreWith legacyDriver.clearObs (D3.d3Hooks cfg) true c w g)
      (checkD2CoreWith (recorderDriverNS cfg).clearObs (D3.d3Hooks cfg) true c w g) := by
    rw [checkD2CoreWith_clearObs, checkD2CoreWith_clearObs]
    exact checkD2CoreWith_legacy_ns cfg hE c w hw hB g
  rw [← legacy_genesis_eq, ← checkD2CoreGWith_clearObs legacyDriver,
    ← checkD2CoreGWith_clearObs (recorderDriverNS cfg)]
  unfold checkD2CoreGWith
  simp only [ExecutionDriver.clearObs, legacyDriver, recorderDriverNS, recorderDriver, Bool.false_eq_true,
    ↓reduceIte, Bool.not_true, decodeWitnessFileV_of_not_c w hw.1]
  simp only [ExecutionDriver.clearObs, legacyDriver, recorderDriverNS, recorderDriver, Bool.false_eq_true,
    ↓reduceIte] at hW
  refine RefinesX.bind' rfl fun cl => ?_
  refine RefinesX.bind_ok fun ⟨sw, codes⟩ hd => ?_
  refine RefinesX.check_bind_right _ _ (decide_eq_true (hw.2 sw codes hd)) ?_
  simp only [Bool.not_false, ↓reduceIte]
  refine RefinesX.bind' rfl fun _ => ?_
  refine RefinesX.bind_ok fun sw' hdw => ?_
  have hb : mergedBytes (sw'.main.values ++ codes) ≤ legacyStorageBound := by
    rw [← legacyMergedBytes_of_decode hd hdw]; exact hB
  o4x_lockstep

/-- **Tier level, up to the escapes**: `.runtimeLimits` against the `NS` reference shell. -/
theorem runtimeLimits_ns_of (hE : EngineAgreeX (Tier.cfg .storageResolution).wasm) (c w : Bytes)
    (hw : O4Witness w) : RefinesX (Tier.checker .runtimeLimits c w) (checkNS c w) := by
  rw [tier_runtimeLimits_eq]
  by_cases hB : legacyMergedBytes w ≤ legacyStorageBound
  · rw [withStorageExclusion_small _ hB]
    exact checkD2CoreGWith_legacy_ns _ hE c w hw hB _
  · obtain ⟨e, he, hx⟩ := withStorageExclusion_big (checkD2CoreG_noacc _ c w _ (Nat.lt_of_not_le hB))
      (Nat.lt_of_not_le hB)
    exact RefinesX.of (Or.inr ⟨e, he, hx⟩)

/-- From `RefinesX` against `NS` to `Refines` against the storage-resolution tier, under the two
per-witness premises. -/
theorem refines_of_x {x y z : Except String Unit} (h : RefinesX x z) (hNS : y = z)
    (hX : ∀ s, y = .error s → esc s = false) : Refines x y := by
  subst hNS
  rcases h with h | ⟨s, hs, hz⟩
  · exact h
  · rw [hX s hz] at hs; cases hs

#print axioms SimX.bind
#print axioms engineAgreeX_of_simX
#print axioms checkD2CoreGWith_legacy_ns
#print axioms runtimeLimits_ns_of

end NearSpecV3.Successor.O4E
