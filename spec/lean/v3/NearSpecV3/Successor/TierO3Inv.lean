import NearSpecV3.Successor.TierO3Engine

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 step 5d — the lower run never carries a distribution receipt

`ND l`: no receipt of `l` is a distribution receipt. The lower run (`globalActions` off) keeps
`ND rs.outgoing` through every store program it runs, and every receipt it creates is a
non-distribution one. This file proves the single-run facts on the read-logging store programs:

* `SOk Q x` / `LOk Q x`: every successful result of the store program satisfies `Q` (no claim on
  errors). Rules: `pure`, `throw`, `bind`, `ite`, and `LOk.tru` (no fact).
* `SRelQ.of_SRel`, `LRQ.of_LR`: a refinement of store programs (`SRel`/`LR`) whose lower program
  satisfies `Q` is an `SRelQ Q`/`LRQ Q` refinement; `LRQ.refl_of` for a program with itself.
* `MRX.loggedQ`: `logged` of an `LRQ Q` pair is an engine pair whose values satisfy `Q`.
* The queue programs keep `ND rs.outgoing`: `bufferReceiptL_nd`, `forwardOrBufferL_nd` (on a
  non-distribution receipt), `fwdLoopL_nd`, `forwardFromBufferL_nd`, `forwardFromBufferV3L_nd`,
  `delayPushL_nd`, `delayPopL_nd`, `processTxD2L_nd`. The buffer and delayed queues need no
  invariant of their own: their receipts are read back through `decodeStored`, which never yields a
  distribution receipt (`decodeStored_not_distribution`).
* The action programs create none: `applyActionL_nd` (`d2HooksL`, the new receipts of every
  non-call action), `refunds_nd`.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged

/-- No distribution receipt in the list. -/
def ND (l : List Rcpt) : Prop := ∀ r ∈ l, rcptIsDistribution r = false

theorem ND.nil : ND [] := fun _ h => by cases h

theorem ND.append {a b : List Rcpt} (ha : ND a) (hb : ND b) : ND (a ++ b) := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact ha r h
  · exact hb r h

theorem ND.cons {r : Rcpt} {l : List Rcpt} (hr : rcptIsDistribution r = false) (hl : ND l) : ND (r :: l) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | h
  · exact hr
  · exact hl x h

theorem ND.single {r : Rcpt} (hr : rcptIsDistribution r = false) : ND [r] := ND.cons hr ND.nil

theorem ND.left {a b : List Rcpt} (h : ND (a ++ b)) : ND a := fun r hr => h r (List.mem_append_left _ hr)
theorem ND.right {a b : List Rcpt} (h : ND (a ++ b)) : ND b := fun r hr => h r (List.mem_append_right _ hr)

theorem ND.ite {c : Prop} [Decidable c] {a b : List Rcpt} (ha : ND a) (hb : ND b) : ND (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

theorem ND.sub {a b : List Rcpt} (h : ND b) (hs : ∀ r ∈ a, r ∈ b) : ND a := fun r hr => h r (hs r hr)

theorem nd_action (pred recv rid : Bytes) (y : Bool) (a : ActionR) :
    rcptIsDistribution ⟨pred, recv, rid, .action y a⟩ = false := rfl
theorem nd_data (pred recv rid : Bytes) (y : Bool) (d : Bytes) (x : Option Bytes) :
    rcptIsDistribution ⟨pred, recv, rid, .data y d x⟩ = false := rfl

/-! ## Single-run facts on store programs -/

/-- Every successful result of the store program satisfies `Q`. -/
inductive SOk {K α : Type} (Q : α → Prop) : SM K α → Prop where
  | ok (a : α) (h : Q a) : SOk Q (.ok a)
  | err (e : String) : SOk Q (.err e)
  | get (k : K) (c : Option Bytes → SM K α) (h : ∀ v, SOk Q (c v)) : SOk Q (.get k c)

theorem SOk.tru {K α : Type} (x : SM K α) : SOk (fun _ => True) x := by
  induction x with
  | ok a => exact SOk.ok a trivial
  | err e => exact SOk.err e
  | get k c ih => exact SOk.get k c ih

theorem SOk.bind {K α β : Type} {Q : α → Prop} {Q' : β → Prop} {x : SM K α} {f : α → SM K β}
    (hx : SOk Q x) (hf : ∀ a, Q a → SOk Q' (f a)) : SOk Q' (x.bind f) := by
  induction hx with
  | ok a h => exact hf a h
  | err e => exact SOk.err e
  | get k c _ ih => exact SOk.get k _ ih

theorem SOk.weaken {K α : Type} {Q Q' : α → Prop} (hq : ∀ a, Q a → Q' a) {x : SM K α} (h : SOk Q x) :
    SOk Q' x := by
  induction h with
  | ok a h => exact SOk.ok a (hq a h)
  | err e => exact SOk.err e
  | get k c _ ih => exact SOk.get k c ih

/-- `LM` form. -/
def LOk {α : Type} (Q : α → Prop) (x : LM α) : Prop := ∀ root, SOk Q (x root)

namespace LOk

theorem tru {α : Type} (x : LM α) : LOk (fun _ => True) x := fun _ => SOk.tru _

theorem pure {α : Type} {Q : α → Prop} (a : α) (h : Q a) : LOk Q (Pure.pure a) := fun _ => SOk.ok a h

theorem throw {α : Type} {Q : α → Prop} (e : String) : LOk Q (MonadExcept.throw e : LM α) :=
  fun _ => SOk.err e

theorem throwThe {α : Type} {Q : α → Prop} (e : String) : LOk Q (throwThe String e : LM α) :=
  fun _ => SOk.err e

theorem bind {α β : Type} {Q : α → Prop} {Q' : β → Prop} {x : LM α} {f : α → LM β}
    (hx : LOk Q x) (hf : ∀ a, Q a → LOk Q' (f a)) : LOk Q' (x >>= f) :=
  fun root => SOk.bind (hx root) fun a h => hf a h root

theorem weaken {α : Type} {Q Q' : α → Prop} (hq : ∀ a, Q a → Q' a) {x : LM α} (h : LOk Q x) : LOk Q' x :=
  fun root => (h root).weaken hq

theorem ite {α : Type} {Q : α → Prop} (c : Prop) [Decidable c] {a b : LM α} (ha : c → LOk Q a)
    (hb : ¬ c → LOk Q b) : LOk Q (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem okL {α : Type} {Q : β → Prop} (o : Option α) (e : String) {f : α → LM β} (hf : ∀ a, LOk Q (f a)) :
    LOk Q (LM.okL o e >>= f) := by
  cases o with
  | none => exact fun _ => SOk.err e
  | some a => exact hf a

theorem foldlM {α β : Type} {Q : α → Prop} (l : List β) (init : α) (hi : Q init) {f : α → β → LM α}
    (h : ∀ a b, Q a → LOk Q (f a b)) : LOk Q (l.foldlM f init) := by
  induction l generalizing init with
  | nil => exact pure _ hi
  | cons x t ih =>
    simp only [List.foldlM_cons]
    exact bind (h init x hi) fun a ha => ih a ha

end LOk

/-! ## From single-run facts to two-run facts -/

theorem SRelQ.of_SOk {K α : Type} {Q : α → Prop} {x : SM K α} (h : SOk Q x) : SRelQ Q x x := by
  induction h with
  | ok a h => exact SRelQ.ok a h
  | err e => exact SRelQ.err e
  | get k c _ ih => exact SRelQ.get k c c ih

theorem SRelQ.of_SRel {K α : Type} {Q : α → Prop} {x y : SM K α} (h : SRel x y) (hq : SOk Q x) :
    SRelQ Q x y := by
  induction h with
  | refl x => exact SRelQ.of_SOk hq
  | ex e he y => exact SRelQ.ex e he y
  | get k c c' _ ih =>
    cases hq with
    | get _ _ h => exact SRelQ.get k c c' fun v => ih v (h v)

theorem LRQ.of_LR {α : Type} {Q : α → Prop} {x y : LM α} (h : LR x y) (hq : LOk Q x) : LRQ Q x y :=
  fun root => SRelQ.of_SRel (h root) (hq root)

theorem LRQ.refl_of {α : Type} {Q : α → Prop} {x : LM α} (hq : LOk Q x) : LRQ Q x x :=
  LRQ.of_LR (LR.refl x) hq

theorem SRelQ.runAcc {K α : Type} {Q : α → Prop} {x y : SM K α} (h : SRelQ Q x y) (s : K → Option Bytes)
    (acc : List K) :
    (∃ e acc', SM.runAcc s x acc = (.error e, acc') ∧ isExclusion e = true) ∨
      (SM.runAcc s x acc = SM.runAcc s y acc ∧ ∀ a, (SM.runAcc s x acc).1 = .ok a → Q a) := by
  induction h generalizing acc with
  | ok a hq => exact Or.inr ⟨rfl, fun b hb => by cases hb; exact hq⟩
  | err e => exact Or.inr ⟨rfl, fun b hb => by cases hb⟩
  | ex e he y => exact Or.inl ⟨e, acc, rfl, he⟩
  | get k c c' _ ih => exact ih (s k) (k :: acc)

theorem SRelQ.runR {K α : Type} {Q : α → Prop} {x y : SM K α} (h : SRelQ Q x y) (s : K → Option Bytes) :
    (∃ e ks, SM.runR s x = (.error e, ks) ∧ isExclusion e = true) ∨
      (SM.runR s x = SM.runR s y ∧ ∀ a, (SM.runR s x).1 = .ok a → Q a) := by
  unfold SM.runR
  rcases h.runAcc s [] with ⟨e, acc', h1, he⟩ | ⟨h1, h2⟩
  · left; exact ⟨e, acc'.reverse, by rw [h1], he⟩
  · right
    refine ⟨by rw [h1], fun a ha => h2 a ?_⟩
    revert ha
    generalize SM.runAcc s x [] = p
    obtain ⟨o, ks⟩ := p
    exact id

open StorageExecution in
/-- `logged` of an `LRQ Q` pair: the engine values satisfy `Q`. -/
theorem MRX.loggedQ {X : String → Prop} (hX : ∀ e, isExclusion e = true → X e) {E : Env → Prop} {α : Type}
    {Q : α → Prop} {x y : LM α} (h : LRQ Q x y) :
    MRX X E Q (StorageExecution.logged x) (StorageExecution.logged y) := by
  intro rL rU env ⟨h1, h2⟩ _
  rw [logged_run_rr, logged_run_rr]
  rcases (h env.preRoot).runR (hGet env.store) with ⟨e, ks, he, hx⟩ | ⟨he, hq⟩
  · left; refine ⟨e, ?_, hX e hx⟩; rw [he]; rfl
  · rw [← he]
    revert hq
    generalize SM.runR (hGet env.store) (x env.preRoot) = p
    obtain ⟨out, keys⟩ := p
    intro hq
    cases out with
    | error e => right; left; exact ⟨e, rfl, rfl⟩
    | ok a =>
      right; right
      refine ⟨a, _, _, rfl, rfl, ⟨?_, ?_⟩, hq a rfl⟩
      · generalize rL.pipe = q at h1 h2
        subst h1; rfl
      · exact h2

/-! ## The walk tactic for single-run facts -/

/-- Close a store-program obligation by a proved fact (extended below, function by function). -/
syntax "lok_close" : tactic

/-- Close a leaf fact: `ND` of a list built from known lists and constructed receipts. -/
macro "nd_close" : tactic => `(tactic| first
  | assumption
  | exact ND.single (by assumption)
  | exact Codec.decodeStored_not_distribution _ _ (by assumption)
  | (simp only [AR.fail]; first | assumption | exact ND.nil)
  | (repeat' (first | assumption | exact ND.nil | exact ND.single rfl | exact ND.single (by assumption) | refine ND.append ?_ ?_ | refine ND.cons rfl ?_)))

macro "lok" : tactic => `(tactic|
  repeat' (first
    | (refine LOk.pure _ ?_; focus ((try dsimp only [RS.setMeta, RS.writeDelayedIdx]); nd_close; done))
    | (exact LOk.throw _)
    | (exact LOk.throwThe _)
    | (exact fun _ => SOk.err _)
    | (simp only [pure_bind])
    | lok_close
    | ((refine LOk.bind (by lok_close) fun _ _ => ?_); try dsimp only)
    | ((refine LOk.bind (LOk.tru _) fun _ _ => ?_); try dsimp only)
    | (refine LOk.ite _ (fun _ => ?_) (fun _ => ?_))
    | (dsimp only)
    | (split <;> (try dsimp only))))

/-! ## Queue programs keep `ND rs.outgoing` -/

theorem groupsPopBackL_nd (rs : RS) (s : Nat) (m : Meta) (h : ND rs.outgoing) :
    LOk (fun x : RS × Meta × Option (Nat × Nat) => ND x.1.outgoing) (groupsPopBackL rs s m) := by
  unfold groupsPopBackL; lok

macro_rules | `(tactic| lok_close) => `(tactic| exact groupsPopBackL_nd _ _ _ (by assumption))

theorem groupsPushBackL_nd (rs : RS) (s : Nat) (m : Meta) (size gas : Nat) (h : ND rs.outgoing) :
    LOk (fun x : RS × Meta => ND x.1.outgoing) (groupsPushBackL rs s m size gas) := by
  unfold groupsPushBackL; lok

macro_rules | `(tactic| lok_close) => `(tactic| exact groupsPushBackL_nd _ _ _ _ _ (by assumption))

theorem metaPushedL_nd (rs : RS) (s size gas : Nat) (h : ND rs.outgoing) :
    LOk (fun x : RS => ND x.outgoing) (metaPushedL rs s size gas) := by
  unfold metaPushedL; lok

theorem metaPoppedL_nd (rs : RS) (s size gas : Nat) (h : ND rs.outgoing) :
    LOk (fun x : RS => ND x.outgoing) (metaPoppedL rs s size gas) := by
  unfold metaPoppedL; lok

macro_rules | `(tactic| lok_close) => `(tactic| exact metaPushedL_nd _ _ _ _ (by assumption))
macro_rules | `(tactic| lok_close) => `(tactic| exact metaPoppedL_nd _ _ _ _ (by assumption))

theorem bufferReceiptL_nd (rs : RS) (r : Rcpt) (size gas shard : Nat) (h : ND rs.outgoing) :
    LOk (fun x : RS => ND x.outgoing) (bufferReceiptL rs r size gas shard) := by
  unfold bufferReceiptL; lok

macro_rules | `(tactic| lok_close) => `(tactic| exact bufferReceiptL_nd _ _ _ _ _ (by assumption))

theorem forwardOrBufferL_nd (env : Env) (rs : RS) (r : Rcpt) (h : ND rs.outgoing)
    (hr : rcptIsDistribution r = false) :
    LOk (fun x : RS => ND x.outgoing) (forwardOrBufferL env rs r) := by
  unfold forwardOrBufferL; lok

theorem readBufferedFromTrieL_nd (s i : Nat) :
    LOk (fun st : Stored => rcptIsDistribution st.r = false) (readBufferedFromTrieL s i) := by
  unfold readBufferedFromTrieL
  lok
  all_goals exact Codec.decodeStored_not_distribution _ _ ‹_›

macro_rules | `(tactic| lok_close) => `(tactic| exact readBufferedFromTrieL_nd _ _)

theorem fwdLoopL_nd (env : Env) (s : Nat) : ∀ fuel i (acc : RS × Nat × List (Nat × Nat)), ND acc.1.outgoing →
    LOk (fun x : RS × Nat × List (Nat × Nat) => ND x.1.outgoing) (fwdLoopL env s fuel i acc)
  | 0, _, _, h => LOk.pure _ h
  | fuel + 1, i, (rs, k, pops), h => by
    unfold fwdLoopL
    dsimp only at h
    lok
    all_goals exact fwdLoopL_nd env s fuel _ _ (by dsimp only; exact ND.append ‹_› (ND.single ‹_›))

macro_rules | `(tactic| lok_close) => `(tactic| exact fwdLoopL_nd _ _ _ _ _ (by assumption))

theorem foldl_outgoing {β : Type} (l : List β) (g : RS → β → Ovl) :
    ∀ rs : RS, (l.foldl (fun rs j => { rs with o := g rs j }) rs).outgoing = rs.outgoing := by
  induction l with
  | nil => intro rs; rfl
  | cons b t ih => intro rs; simp only [List.foldl_cons]; rw [ih]

theorem forwardFromBufferToShardL_nd (env : Env) (rs : RS) (s : Nat) (h : ND rs.outgoing) :
    LOk (fun x : RS => ND x.outgoing) (forwardFromBufferToShardL env rs s) := by
  unfold forwardFromBufferToShardL
  refine LOk.bind (fwdLoopL_nd env s _ _ _ h) fun ⟨rs', k, pops⟩ h' => ?_
  dsimp only at h' ⊢
  refine LOk.foldlM _ _ ?_ fun a _ ha => metaPoppedL_nd _ _ _ _ ha
  split
  · dsimp only; rw [foldl_outgoing]; exact h'
  · rw [foldl_outgoing]; exact h'

macro_rules | `(tactic| lok_close) => `(tactic| exact forwardFromBufferToShardL_nd _ _ _ (by assumption))

theorem forwardFromBufferL_nd (env : Env) (rs : RS) (h : ND rs.outgoing) :
    LOk (fun x : RS => ND x.outgoing) (forwardFromBufferL env rs) := by
  unfold forwardFromBufferL
  refine LOk.ite _ (fun _ => LOk.throw _) fun _ => ?_
  exact LOk.foldlM (Q := fun x : RS => ND x.outgoing) _ _ h fun a _ ha => forwardFromBufferToShardL_nd _ _ _ ha

theorem forwardFromBufferV3L_nd (env : Env) (rs : RS) (h : ND rs.outgoing) :
    LOk (fun x : RS => ND x.outgoing) (StorageExecution.forwardFromBufferV3L false env rs) := by
  unfold StorageExecution.forwardFromBufferV3L
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine LOk.bind (LOk.foldlM (Q := fun x : RS => ND x.outgoing) _ _ h fun a _ ha => forwardFromBufferToShardL_nd _ _ _ ha) fun a ha => ?_
  lok

theorem delayPushL_nd (rs : RS) (r : Rcpt) (h : ND rs.outgoing) :
    LOk (fun x : RS => ND x.outgoing) (delayPushL rs r) := by
  unfold delayPushL; lok

theorem delayPopL_nd (env : Env) : ∀ fuel (rs : RS), ND rs.outgoing →
    LOk (fun x : RS × Option Rcpt => ND x.1.outgoing) (delayPopL env fuel rs)
  | 0, _, h => LOk.pure _ h
  | fuel + 1, rs, h => by
    unfold delayPopL
    lok
    all_goals exact delayPopL_nd env fuel _ (by exact h)

macro_rules | `(tactic| lok_close) => `(tactic| exact forwardOrBufferL_nd _ _ _ (by assumption) (by first | rfl | assumption))

theorem ite_fob_nd (c : Prop) [Decidable c] (env : Env) (rs x : RS) (r : Rcpt) (hx : ND x.outgoing)
    (h : ND rs.outgoing) (hr : rcptIsDistribution r = false) :
    LOk (fun y : RS => ND y.outgoing) (if c then pure x else forwardOrBufferL env rs r) :=
  LOk.ite _ (fun _ => LOk.pure _ hx) fun _ => forwardOrBufferL_nd env rs r h hr

macro_rules | `(tactic| lok_close) => `(tactic| exact ite_fob_nd _ _ _ _ _ (by first | assumption | (dsimp only; assumption)) (by assumption) rfl)

theorem processTxD2L_nd (env : Env) (rs : RS × List Bytes) (tf : TxD2 × Bool) (h : ND rs.1.outgoing) :
    LOk (fun x : RS × List Bytes => ND x.1.outgoing) (processTxD2L env rs tf) := by
  obtain ⟨rs, seen⟩ := rs
  dsimp only at h
  unfold processTxD2L
  lok

/-! ## Action programs create no distribution receipt -/

section acts
variable (c : ActCtx) (st : ActSt) (res : AR) (h : ND res.newReceipts)
include h

theorem actCreateAccountL_nd : LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actCreateAccountL c st res) := by
  unfold actCreateAccountL; lok
theorem actDeployL_nd (code : Bytes) : LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actDeployL c st res code) := by
  unfold actDeployL; lok
theorem actTransferL_nd (d : Nat) : LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actTransferL c st res d) := by
  unfold actTransferL; lok
theorem actStakeL_nd (s : Nat) (pk : PublicKey) :
    LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actStakeL c st res s pk) := by
  unfold actStakeL; lok
theorem actAddKeyL_nd (pk : PublicKey) (ak : AK) :
    LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actAddKeyL c st res pk ak) := by
  unfold actAddKeyL; lok
theorem actDeleteKeyL_nd (pk : PublicKey) :
    LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actDeleteKeyL c st res pk) := by
  unfold actDeleteKeyL; lok
theorem actDeleteAccountL_nd (ben : Bytes) :
    LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actDeleteAccountL c st res ben) := by
  unfold actDeleteAccountL; lok
theorem actToGasKeyL_nd (pk : PublicKey) (d : Nat) :
    LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actToGasKeyL c st res pk d) := by
  unfold actToGasKeyL; lok
theorem actFromGasKeyL_nd (pk : PublicKey) (a : Nat) :
    LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actFromGasKeyL c st res pk a) := by
  unfold actFromGasKeyL; lok
theorem actDelegateL_nd (d : Delegate) :
    LOk (fun p : ActSt × AR => ND p.2.newReceipts) (actDelegateL c st res d) := by
  unfold actDelegateL; lok

end acts

macro_rules | `(tactic| lok_close) => `(tactic| first
  | exact actCreateAccountL_nd _ _ _ (by first | assumption | exact ND.nil)
  | exact actDeployL_nd _ _ _ (by first | assumption | exact ND.nil) _
  | exact actTransferL_nd _ _ _ (by first | assumption | exact ND.nil) _
  | exact actStakeL_nd _ _ _ (by first | assumption | exact ND.nil) _ _
  | exact actAddKeyL_nd _ _ _ (by first | assumption | exact ND.nil) _ _
  | exact actDeleteKeyL_nd _ _ _ (by first | assumption | exact ND.nil) _
  | exact actDeleteAccountL_nd _ _ _ (by first | assumption | exact ND.nil) _
  | exact actToGasKeyL_nd _ _ _ (by first | assumption | exact ND.nil) _ _
  | exact actFromGasKeyL_nd _ _ _ (by first | assumption | exact ND.nil) _ _
  | exact actDelegateL_nd _ _ _ (by first | assumption | exact ND.nil) _)

/-- **The non-call actions create no distribution receipt** (`ordinaryAction`'s store program). -/
theorem applyActionL_nd (c : ActCtx) (st : ActSt) (a : Act) :
    LOk (fun p : ActSt × AR => ND p.2.newReceipts) (applyActionL d2HooksL c st a) := by
  unfold applyActionL; lok

/-- Single-run facts on `Except` programs: every successful result satisfies `P`. -/
def EOk {β : Type} (P : β → Prop) (x : Except String β) : Prop := ∀ v, x = .ok v → P v

theorem EOk.bind {α β : Type} {P : β → Prop} {x : Except String α} {f : α → Except String β}
    (hf : ∀ a, EOk P (f a)) : EOk P (x >>= f) := by
  intro v h
  cases x with
  | error e => cases h
  | ok a => exact hf a v h

theorem EOk.pure {β : Type} {P : β → Prop} {b : β} (hb : P b) : EOk P (Pure.pure b : Except String β) := by
  intro v h; cases h; exact hb

theorem EOk.throw {β : Type} {P : β → Prop} (e : String) : EOk P (MonadExcept.throw e : Except String β) := by
  intro v h; cases h

theorem EOk.ite {β : Type} {P : β → Prop} (c : Prop) [Decidable c] {a b : Except String β} (ha : c → EOk P a)
    (hb : ¬ c → EOk P b) : EOk P (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

/-- **Refund receipts are action receipts.** -/
theorem refunds_nd (r : Rcpt) (a : ActionR) (res : AR) (purchase burn : Nat) (created : Bool) :
    EOk (fun x : List Rcpt × Nat => ND x.1) (refunds r a res purchase burn created) := by
  unfold refunds
  repeat' (first
    | (refine EOk.bind fun _ => ?_)
    | (refine EOk.ite _ (fun _ => ?_) (fun _ => ?_))
    | (exact EOk.throw _)
    | (dsimp only)
    | (refine EOk.pure ?_; dsimp only
       exact ND.append (ND.ite (ND.single (nd_action _ _ _ _ _)) ND.nil)
         (ND.ite (ND.single (nd_action _ _ _ _ _)) ND.nil)))

#print axioms forwardOrBufferL_nd
#print axioms forwardFromBufferL_nd
#print axioms forwardFromBufferV3L_nd
#print axioms delayPopL_nd
#print axioms delayPushL_nd
#print axioms processTxD2L_nd
#print axioms applyActionL_nd
#print axioms refunds_nd
#print axioms MRX.loggedQ

end NearSpecV3.Successor
