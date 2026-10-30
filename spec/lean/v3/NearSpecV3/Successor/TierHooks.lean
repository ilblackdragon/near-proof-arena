import NearSpecV3.Successor.TierMono
import NearSpecV3.Successor.TierFloats

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 — the legacy pipeline is monotone in its `FunctionCall` hook

`HooksRefine h h'`: wherever `h.functionCall` decides, `h'.functionCall` returns the same result.
The legacy D2 pipeline (`checkD2Core`, `checkD2CoreG`) only *binds* the hook's result and never
catches an error, so it inherits the refinement (`checkD2Core_hooks_mono`,
`checkD2CoreG_hooks_mono`). This is the chunk-level propagation step that the per-call lemmas of
O1 (floats) and O5 (loading limits) need on the legacy engine.

Every proof walks the two elaborated bodies in lockstep (`hooks_lockstep`, the `refines_lockstep`
walk extended by the lemmas of this file, registered through `hk_close`).
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

theorem Refines.foldlM {α β : Type} (l : List β) (init : α)
    {f g : α → β → Except String α} (h : ∀ a b, Refines (f a b) (g a b)) :
    Refines (l.foldlM f init) (l.foldlM g init) := by
  induction l generalizing init with
  | nil => exact Refines.refl _
  | cons x t ih =>
    simp only [List.foldlM_cons]
    exact Refines.bind (h init x) fun a => ih a

/-- Closers for one call of a function the walk has already proved monotone. Extended below by
`macro_rules`; every rule is tried. -/
syntax "hk_close" : tactic
macro_rules | `(tactic| hk_close) => `(tactic| exact (‹HooksRefine _ _› _ _ _ _))

/-- `refines_lockstep` plus the lemmas registered with `hk_close`, and `foldlM`. -/
macro "hooks_lockstep" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact Refines.refl _)
    | hk_close
    | (exact Refines.throw_bind _ _ _)
    | ((refine Refines.bind (by hk_close) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind (by hk_close) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind (Refines.foldlM _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine Refines.foldlM _ _ fun _ _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Refines.ite_bind_join _ _ _ fun _ => ?_)
    | (refine Refines.ite_bind_skip _ _ ?_)
    | (refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine Refines.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

theorem applyAction_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (c : ActCtx) (st : ActSt)
    (act : Act) : Refines (applyAction h c st act) (applyAction h' c st act) := by
  unfold applyAction
  hooks_lockstep
  all_goals exact Refines.refl _

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact applyAction_hooks_mono ‹_› _ _ _)

theorem actionLoop_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (env : Env) (r : Rcpt)
    (a : ActionR) (inputs : List (Option Bytes)) (deployed attempted : List Bytes) (i : Nat)
    (acts : List Act) (acc : ActSt × AR) :
    Refines (actionLoop h env r a inputs deployed attempted i acts acc)
      (actionLoop h' env r a inputs deployed attempted i acts acc) := by
  induction acts generalizing i acc with
  | nil => exact Refines.refl _
  | cons act rest ih =>
    obtain ⟨st, res⟩ := acc
    unfold actionLoop
    hooks_lockstep
    all_goals first | exact ih _ _ | exact Refines.refl _

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact actionLoop_hooks_mono ‹_› _ _ _ _ _ _ _ _ _)

theorem applyActionReceipt_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (env : Env)
    (rs : RS) (r : Rcpt) (a : ActionR) :
    Refines (applyActionReceipt h env rs r a) (applyActionReceipt h' env rs r a) := by
  unfold applyActionReceipt
  hooks_lockstep
  all_goals exact Refines.refl _

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact applyActionReceipt_hooks_mono ‹_› _ _ _ _)

theorem processReceipt_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (env : Env)
    (rs : RS) (r : Rcpt) :
    Refines (processReceipt h env rs r) (processReceipt h' env rs r) := by
  unfold processReceipt
  hooks_lockstep
  all_goals exact Refines.refl _

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact processReceipt_hooks_mono ‹_› _ _ _)

theorem processWithTotals_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (env : Env)
    (rs : RS) (r : Rcpt) :
    Refines (processWithTotals h env rs r) (processWithTotals h' env rs r) := by
  unfold processWithTotals
  hooks_lockstep
  all_goals exact Refines.refl _

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact processWithTotals_hooks_mono ‹_› _ _ _)

theorem processWithInstant_drain_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (env : Env)
    (fuel : Nat) (rs : RS) :
    Refines (processWithInstant.drain h env fuel rs) (processWithInstant.drain h' env fuel rs) := by
  induction fuel generalizing rs with
  | zero => exact Refines.refl _
  | succ n ih =>
    unfold processWithInstant.drain
    hooks_lockstep
    all_goals first | exact ih _ | exact Refines.refl _

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact processWithInstant_drain_hooks_mono ‹_› _ _ _)

theorem processWithInstant_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (env : Env)
    (rs : RS) (r : Rcpt) :
    Refines (processWithInstant h env rs r) (processWithInstant h' env rs r) := by
  unfold processWithInstant
  hooks_lockstep
  all_goals exact Refines.refl _

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact processWithInstant_hooks_mono ‹_› _ _ _)

theorem processLocals_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (env : Env)
    (rs : RS) (l : List Rcpt) :
    Refines (processLocals h env rs l) (processLocals h' env rs l) := by
  unfold processLocals
  hooks_lockstep
  all_goals exact Refines.refl _

theorem processDelayed_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (env : Env)
    (fuel : Nat) (rs : RS) :
    Refines (processDelayed h env fuel rs) (processDelayed h' env fuel rs) := by
  induction fuel generalizing rs with
  | zero => exact Refines.refl _
  | succ n ih =>
    unfold processDelayed
    hooks_lockstep
    all_goals first | exact ih _ | exact Refines.refl _

theorem processIncoming_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (env : Env)
    (rs : RS) (l : List Rcpt) :
    Refines (processIncoming h env rs l) (processIncoming h' env rs l) := by
  unfold processIncoming
  hooks_lockstep
  all_goals exact Refines.refl _

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact processLocals_hooks_mono ‹_› _ _ _)
macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact processDelayed_hooks_mono ‹_› _ _ _)
macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact processIncoming_hooks_mono ‹_› _ _ _)

theorem applyNewChunkD2_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (prims : Prims)
    (env : Env) (t : PTrie) (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    Refines (applyNewChunkD2 h prims env t vu lastProps incoming txs ownCong)
      (applyNewChunkD2 h' prims env t vu lastProps incoming txs ownCong) := by
  unfold applyNewChunkD2
  hooks_lockstep
  all_goals exact Refines.refl _

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact applyNewChunkD2_hooks_mono ‹_› _ _ _ _ _ _ _ _)

theorem checkD2CoreObs_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreObs h a c w g) (checkD2CoreObs h' a c w g) := by
  unfold checkD2CoreObs
  hooks_lockstep
  all_goals exact Refines.refl _

theorem checkD2Core_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2Core h a c w g) (checkD2Core h' a c w g) :=
  Refines.map _ (checkD2CoreObs_hooks_mono hh a c w g)

macro_rules | `(tactic| hk_close) => `(tactic| with_reducible exact checkD2Core_hooks_mono ‹_› _ _ _ _)

theorem checkD2CoreG_hooks_mono {h h' : ActionHooks} (hh : HooksRefine h h') (a : Bool)
    (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreG h a c w g) (checkD2CoreG h' a c w g) := by
  unfold checkD2CoreG
  hooks_lockstep
  all_goals exact Refines.refl _

end NearSpecV3.Successor
