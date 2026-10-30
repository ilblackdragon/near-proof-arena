import NearSpecV3.Successor.TierO4

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O4 — the engine simulation against the original legacy engine

`TierO4.lean` reduces O4 to `EngineAgree`: the recorder engine (`StorageExecution.applyNewChunkD2`,
monad `M = StateT Recording (ReaderT Env (Except String))`) refines the legacy engine
(`D2.applyNewChunkD2 (D3.d3Hooks cfg)`, `Except String`) on the shell's inputs.

## The relation `Sim`

`Sim e P φ x y`: from every recorder state satisfying `P`, if the original `x` returns `a`, the
recorder `y` returns some `b` with `a = φ b` (in a state satisfying `P`); if `x` rejects with a
non-exclusion, `y` rejects with the same string. `φ` puts the revealed pre-state trie back into the
recorder's states (`·.wt T`).

**Why the original and not the logged mirror.** The recorder runs each logged mirror `fL` on its
own states, whose overlays carry the revealed trie `T`; the mirror lemma `R_f`
(`Logged/*`) says `f (b.wt T) = (LM.ev (fL b)).map (·.wt T)` for *every* `b`. Relating the recorder
to the original with `a = b.wt T` therefore needs no trie-independence lemma per mirror (the
recorder's overlays may carry any trie): `Sim.logged` turns every `R`-lemma into a simulation step.

## The recorder invariant

`P` depends on the recorder state only through `recorder` and `softLimit` (`PFrame`), so the
observation and pipeline bookkeeping (`detail`, `vmErr`, `curFail`, `pipe`, `receiptStart`) keeps it.
-/

namespace NearSpecV3.Successor.O4E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged
open NearSpecV3.Successor
open NearSpecV3.Successor.StorageExecution (M Recording)

/-- The revealed pre-state trie of an environment (the shell's `tMain`). -/
abbrev T (e : Env) : PTrie := preT e.store e.preRoot

/-- The simulation from one recorder state. -/
def SimAt {α β : Type} (e : Env) (P : Recording → Prop) (φ : β → α) (x : Except String α) (y : M β)
    (r : Recording) : Prop :=
  match x with
  | .ok a => ∃ b r', y.run r e = .ok (b, r') ∧ a = φ b ∧ P r'
  | .error err => isExclusion err = true ∨ y.run r e = .error err

/-- The engine simulation: original `x`, recorder `y`, value map `φ` (recorder → original). -/
def Sim {α β : Type} (e : Env) (P : Recording → Prop) (φ : β → α) (x : Except String α) (y : M β) :
    Prop :=
  ∀ r, P r → SimAt e P φ x y r

/-- `P` reads only the recorder and the soft limit. -/
def PFrame (P : Recording → Prop) : Prop :=
  ∀ r r', r'.recorder = r.recorder → r'.softLimit = r.softLimit → P r → P r'

/-- `y` only does bookkeeping: it returns `b` and keeps the recorder and the soft limit. -/
def Book {β : Type} (e : Env) (y : M β) (b : β) : Prop :=
  ∀ r, ∃ r', y.run r e = .ok (b, r') ∧ r'.recorder = r.recorder ∧ r'.softLimit = r.softLimit

namespace Sim

variable {e : Env} {P : Recording → Prop}

theorem run_bind {β γ : Type} (y : M β) (g : β → M γ) (r : Recording) :
    (y >>= g).run r e = (y.run r e) >>= fun p => (g p.1).run p.2 e := rfl

theorem pure {α β : Type} {φ : β → α} {a : α} {b : β} (h : a = φ b) :
    Sim e P φ (Pure.pure a) (Pure.pure b : M β) := fun r hr => ⟨b, r, rfl, h, hr⟩

theorem ok {α β : Type} {φ : β → α} {a : α} {b : β} (h : a = φ b) :
    Sim e P φ (Except.ok a) (Pure.pure b : M β) := fun r hr => ⟨b, r, rfl, h, hr⟩

theorem throw {α β : Type} {φ : β → α} (err : String) :
    Sim e P φ (MonadExcept.throw err : Except String α) (MonadExcept.throw err : M β) :=
  fun _ _ => Or.inr rfl

theorem error {α β : Type} {φ : β → α} (err : String) :
    Sim e P φ (Except.error err : Except String α) (MonadExcept.throw err : M β) :=
  fun _ _ => Or.inr rfl

theorem bind {α α' β β' : Type} {φ : β → α} {ψ : β' → α'}
    {x : Except String α} {y : M β} {f : α → Except String α'} {g : β → M β'}
    (hxy : Sim e P φ x y) (hfg : ∀ b, Sim e P ψ (f (φ b)) (g b)) :
    Sim e P ψ (x >>= f) (y >>= g) := by
  intro r hr
  have h1 := hxy r hr
  unfold SimAt at h1 ⊢
  rw [run_bind]
  cases hx : x with
  | error err =>
    rw [hx] at h1
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; rfl)
  | ok a =>
    rw [hx] at h1
    obtain ⟨b, r', hy, rfl, hr'⟩ := h1
    have h2 := hfg b r' hr'
    unfold SimAt at h2
    rw [hy]
    exact h2

/-- `bind` at the identity value map (no `id` left in the continuation). -/
theorem bind_id {α α' β' : Type} {ψ : β' → α'}
    {x : Except String α} {y : M α} {f : α → Except String α'} {g : α → M β'}
    (hxy : Sim e P id x y) (hfg : ∀ b, Sim e P ψ (f b) (g b)) :
    Sim e P ψ (x >>= f) (y >>= g) := bind hxy hfg

/-- A logged read: every mirror lemma `R_f` is a simulation step. -/
theorem logged {α β : Type} {φ : β → α} {n : LM β} {x : Except String α}
    (hR : R e.store e.preRoot n x φ)
    (hP : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder }) :
    Sim e P φ x (StorageExecution.logged n) := by
  intro r hr
  unfold SimAt
  unfold R at hR
  rw [logged_run, hR]
  cases LM.ev e.store e.preRoot n with
  | error err => exact Or.inr rfl
  | ok b => exact ⟨b, _, rfl, rfl, hP r _ hr⟩

theorem liftE {α : Type} (x : Except String α) : Sim e P id x (StorageExecution.liftE x) := by
  intro r hr
  unfold SimAt
  cases x with
  | error err => exact Or.inr rfl
  | ok a => exact ⟨a, r, rfl, rfl, hr⟩

theorem okR {α : Type} (o : Option α) (m : String) : Sim e P id (ok? o m) (StorageExecution.okR o m) := by
  unfold StorageExecution.okR
  exact liftE _

/-- Recorder-only bookkeeping before the continuation. -/
theorem book {α β γ : Type} {ψ : β → α} {x : Except String α} {B : M γ} {c : γ} {g : γ → M β}
    (hP : PFrame P) (hB : Book e B c) (h : Sim e P ψ x (g c)) : Sim e P ψ x (B >>= g) := by
  intro r hr
  obtain ⟨r', hrun, h1, h2⟩ := hB r
  have h' := h r' (hP r r' h1 h2 hr)
  unfold SimAt at h' ⊢
  rw [run_bind, hrun]
  exact h'

/-- An original value against recorder bookkeeping that returns the related value. -/
theorem pure_book {α β : Type} {φ : β → α} {a : α} {y : M β} {b : β} (hP : PFrame P) (hB : Book e y b)
    (h : a = φ b) : Sim e P φ (Pure.pure a) y := by
  intro r hr
  obtain ⟨r', hrun, h1, h2⟩ := hB r
  exact ⟨b, r', hrun, h, hP r r' h1 h2 hr⟩

theorem ite {α β : Type} {φ : β → α} (c : Prop) [Decidable c] {x x' : Except String α} {y y' : M β}
    (h : c → Sim e P φ x y) (h' : ¬c → Sim e P φ x' y') :
    Sim e P φ (if c then x else x') (if c then y else y') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h hc
  · simp only [hc, ite_false]; exact h' hc

theorem foldlM {γ α β : Type} {φ : β → α} {f : α → γ → Except String α} {g : β → γ → M β}
    (hfg : ∀ b c, Sim e P φ (f (φ b) c) (g b c)) :
    ∀ (l : List γ) (b : β), Sim e P φ (l.foldlM f (φ b)) (l.foldlM g b)
  | [], b => Sim.pure rfl
  | c :: l, b => by
    simp only [List.foldlM_cons]
    exact Sim.bind (hfg b c) fun b' => foldlM hfg l b'

theorem foldlM' {γ α β : Type} {φ : β → α} {f : α → γ → Except String α} {g : β → γ → M β}
    (hfg : ∀ b c, Sim e P φ (f (φ b) c) (g b c)) (l : List γ) {a : α} {b : β} (hab : a = φ b) :
    Sim e P φ (l.foldlM f a) (l.foldlM g b) := hab ▸ foldlM hfg l b

theorem congr_left {α β : Type} {φ : β → α} {x x' : Except String α} {y : M β} (h : x = x')
    (h' : Sim e P φ x' y) : Sim e P φ x y := h ▸ h'

end Sim

namespace Sim
variable {e : Env} {P : Recording → Prop}

/-- A recorder bind whose head is a logged read with a known value. -/
theorem logged_ok_bind {α β γ : Type} {ψ : β → α} {x : Except String α} {n : LM γ} {c : γ} {g : γ → M β}
    (hev : LM.ev e.store e.preRoot n = .ok c)
    (hP : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder })
    (h : Sim e P ψ x (g c)) : Sim e P ψ x (StorageExecution.logged n >>= g) := by
  intro r hr
  have h' := h _ (hP r (Logged.SM.reads (hGet e.store) (n e.preRoot)) hr)
  unfold SimAt at h' ⊢
  rw [run_bind, logged_run, hev]
  exact h'

/-- The recorder state read by `get`. -/
theorem get {α β : Type} {ψ : β → α} {x : Except String α} {g : Recording → M β}
    (h : ∀ r, P r → SimAt e P ψ x (g r) r) : Sim e P ψ x (MonadState.get >>= g) := by
  intro r hr
  exact h r hr

/-- A simulation step followed by recorder bookkeeping that returns its value. -/
theorem bind_book {α β : Type} {φ : β → α} {x : Except String α} {y : M β} {g : β → M β}
    (hP : PFrame P) (hxy : Sim e P φ x y) (hg : ∀ b, Book e (g b) b) : Sim e P φ x (y >>= g) := by
  intro r hr
  have h1 := hxy r hr
  unfold SimAt at h1 ⊢
  rw [run_bind]
  cases hx : x with
  | error err =>
    rw [hx] at h1
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; rfl)
  | ok a =>
    rw [hx] at h1
    obtain ⟨b, r', hy, hab, hr'⟩ := h1
    obtain ⟨r'', hrun, h1, h2⟩ := hg b r'
    rw [hy]
    exact ⟨b, r'', hrun, hab, hP r' r'' h1 h2 hr'⟩

end Sim

namespace Book
variable {e : Env}

theorem pure {β : Type} (b : β) : Book e (Pure.pure b : M β) b := fun r => ⟨r, rfl, rfl, rfl⟩

theorem bind {β γ : Type} {y : M γ} {c : γ} {g : γ → M β} {b : β} (hy : Book e y c) (hg : Book e (g c) b) :
    Book e (y >>= g) b := by
  intro r
  obtain ⟨r1, h1, a1, b1⟩ := hy r
  obtain ⟨r2, h2, a2, b2⟩ := hg r1
  refine ⟨r2, ?_, a2.trans a1, b2.trans b1⟩
  rw [Sim.run_bind, h1]; exact h2

theorem modifyDetail (f : ObsDetail → ObsDetail) :
    Book e (StorageExecution.modifyDetail f) () := by
  intro r
  unfold StorageExecution.modifyDetail
  by_cases h : r.observe = true
  · exact ⟨{ r with detail := f r.detail }, by simp [h]; rfl, rfl, rfl⟩
  · exact ⟨r, by simp [h]; rfl, rfl, rfl⟩

theorem get_bind {β : Type} {g : Recording → M β} {b : β} (h : ∀ r0, Book e (g r0) b) :
    Book e (MonadState.get >>= g) b := fun r => h r r

theorem ite {β : Type} (c : Prop) [Decidable c] {y y' : M β} {b : β} (h : c → Book e y b)
    (h' : ¬c → Book e y' b) : Book e (if c then y else y') b := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h hc
  · simp only [hc, ite_false]; exact h' hc

theorem pushAttrib (ids : List Bytes) (d : List (Bytes × Option Bytes) × List (Bytes × Option Bytes)) :
    Book e (StorageExecution.pushAttrib ids d) () := modifyDetail _

end Book

theorem throw_bind {e : Env} {P : Recording → Prop} {α α' β β' : Type} {ψ : β' → α'} (err : String) {f : α → Except String α'}
    {g : β → M β'} :
    Sim e P ψ ((MonadExcept.throw err : Except String α) >>= f) ((MonadExcept.throw err : M β) >>= g) :=
  fun _ _ => Or.inr rfl

theorem err_bind {e : Env} {P : Recording → Prop} {α α' β β' : Type} {ψ : β' → α'} {err : String}
    {x : Except String α} {y : M β} {f : α → Except String α'} {g : β → M β'}
    (hx : x = .error err) (hy : ∀ r, y.run r e = .error err) : Sim e P ψ (x >>= f) (y >>= g) := by
  intro r _
  unfold SimAt
  rw [hx]
  exact Or.inr (by rw [Sim.run_bind, hy]; rfl)

theorem ovl_wt_trie (o : Ovl) (t : PTrie) : (o.wt t).trie = t := rfl

section steps
variable {e : Env} {P : Recording → Prop}

theorem sim_processTxR (hP : PFrame P)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder })
    (rs : RS × List Bytes) (tf : TxD2 × Bool) :
    Sim e P (fun p => (p.1.wt (T e), p.2)) (processTxD2 e (rs.1.wt (T e), rs.2) tf)
      (StorageExecution.processTxR e rs tf) := by
  unfold StorageExecution.processTxR
  refine Sim.bind_book hP (Sim.logged (R_processTxD2' e rfl rs rfl tf) hRec) fun out => ?_
  obtain ⟨t, flag⟩ := tf
  refine Book.get_bind fun r0 => ?_
  simp only []
  exact Book.ite _ (fun _ => Book.bind (Book.modifyDetail _) (Book.bind (Book.pushAttrib _ _) (Book.pure _)))
    (fun _ => Book.pure _)

/-- The recorder's bandwidth-request dispatch is the logged dispatch. -/
theorem bandwidthRequestsR_eq (env : Env) (rs : RS) :
    StorageExecution.bandwidthRequestsR env rs = StorageExecution.logged (bandwidthRequestsL env rs) := by
  unfold StorageExecution.bandwidthRequestsR bandwidthRequestsL
  split <;> rfl

set_option hygiene false in
/-- Walk the main transition (`sim_applyNewChunkD2`); the hypotheses are named as there. -/
macro "main_walk" : tactic => `(tactic|
  repeat (first
    | (exact Sim.pure rfl)
    | (exact Sim.ok rfl)
    | (exact Sim.throw _)
    | (exact Sim.error _)
    | (exact throw_bind _)
    | (refine err_bind rfl fun _ => ?_; rfl)
    | (refine Sim.get fun r0 hr0 => ⟨_, r0, rfl, rfl, hr0⟩)
    | (refine Sim.bind (Sim.pure (φ := fun o : Ovl => o.wt (T _)) rfl) fun _ => ?_)
    | (refine Sim.bind_id (Sim.logged (R_getIndices' _ (by rfl) _ _) hRec) fun _ => ?_)
    | (refine Sim.bind (Sim.logged (R_schedOvl _ _ _ (by rfl)) hRec) fun _ => ?_)
    | (refine Sim.bind_id (Sim.logged (R_bandwidthRequests' _ (by rfl) _ (by rfl)) hRec) fun _ => ?_)
    | (refine Sim.bind_id (Sim.logged (R_finalize' hs _ (by rfl)) hRec) fun _ => ?_)
    | (refine Sim.bind (hFwd _ _ (by rfl)) fun _ => ?_)
    | (refine Sim.bind (hLoc _ _ _ (by rfl)) fun _ => ?_)
    | (refine Sim.bind (hDel _ _ _ (by rfl)) fun _ => ?_)
    | (refine Sim.bind (hInc _ _ _ (by rfl)) fun _ => ?_)
    | (refine Sim.bind (hYld _ _ _ _ (by rfl)) fun _ => ?_)
    | (refine Sim.bind (Sim.foldlM' (fun b c => sim_processTxR hP hRec b c) _ rfl) fun _ => ?_)
    | (refine Sim.bind_id (Sim.foldlM' (φ := id) (fun b c => ?_) _ rfl) fun _ => ?_)
    | (refine Sim.logged_ok_bind (ev_trieFindL _) hRec ?_; try simp only [ovl_wt_trie, T])
    | (refine Sim.bind_id (Sim.liftE _) fun _ => ?_)
    | (refine Sim.bind_id (Sim.okR _ _) fun _ => ?_)
    | (refine Sim.ite _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

/-- The main transition's recorder flags (`StorageExecution.run`'s defaults). -/
abbrev fl0 : StorageExecution.Flags := { globalActions := false, codePolicy := .coldPartial }

/-- **Main transition, phases 1–5 and 7.** The recorder's `applyNewChunkD2` simulates the legacy
engine, given the simulations of the forwarding step and of the receipt phases (local, delayed,
incoming receipts and yield timeouts). The output relation is `obsClear` (finding G0). -/
theorem sim_applyNewChunkD2 (cfg : Wasm.NearCfg) (hP : PFrame P)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder })
    (hs : HInv e.store) (prims : Prims) (vu : Option ValidatorUpdateFacts) (ps : List (Bytes × Nat))
    (inc : List Rcpt) (txs : List (TxD2 × Bool)) (cg : Congestion)
    (hFwd : ∀ rs rsO, rsO = rs.wt (T e) → Sim e P (·.wt (T e)) (forwardFromBuffer e rsO)
      (StorageExecution.forwardFromBufferR false e rs))
    (hLoc : ∀ rs rsO l, rsO = rs.wt (T e) → Sim e P (·.wt (T e)) (D2.processLocals (D3.d3Hooks cfg) e rsO l)
      (StorageExecution.processLocals fl0 cfg e rs l))
    (hDel : ∀ fuel rs rsO, rsO = rs.wt (T e) → Sim e P (·.wt (T e))
      (D2.processDelayed (D3.d3Hooks cfg) e fuel rsO) (StorageExecution.processDelayed fl0 cfg e fuel rs))
    (hInc : ∀ rs rsO l, rsO = rs.wt (T e) → Sim e P (·.wt (T e))
      (D2.processIncoming (D3.d3Hooks cfg) e rsO l) (StorageExecution.processIncoming fl0 cfg e rs l))
    (hYld : ∀ next fuel (acc accO : RS × Nat × Nat), accO = (acc.1.wt (T e), acc.2) →
      Sim e P (fun p => (p.1.wt (T e), p.2))
      (D2.yieldLoop e next fuel accO) (StorageExecution.yieldLoop false e next fuel acc)) :
    Sim e P obsClear (D2.applyNewChunkD2 (D3.d3Hooks cfg) prims e (T e) vu ps inc txs cg)
      (StorageExecution.applyNewChunkD2 fl0 cfg prims e (T e) vu ps inc txs cg) := by
  unfold D2.applyNewChunkD2 StorageExecution.applyNewChunkD2
  simp only [StorageExecution.validatorUpdateR, StorageExecution.getIndicesR, StorageExecution.schedOvlR,
    StorageExecution.trieFindR, StorageExecution.finalizeR, bandwidthRequestsR_eq]
  cases vu with
  | none =>
    dsimp only
    main_walk
    all_goals done
  | some f =>
    dsimp only
    refine Sim.bind (Sim.logged (R_validatorUpdate' _ _ _ (by rfl) _ _) hRec) fun _ => ?_
    main_walk
    all_goals done

end steps

#print axioms Sim.bind
#print axioms Sim.logged
#print axioms Sim.foldlM

end NearSpecV3.Successor.O4E
