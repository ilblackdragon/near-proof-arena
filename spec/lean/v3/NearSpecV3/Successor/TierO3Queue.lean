import NearSpecV3.Successor.TierO3Pipe

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 step 5b — the queue operations with the D2 and the global policy

On a well-formed layout (`Layout.WF`: `shardIds.length = boundaries.length + 1`, the integrator's
hypothesis, README §9) every account's shard is in the layout, so on a non-distribution receipt the
global queue target is the D2 shard (`globalTarget_of_not_distribution`). Receipts the D2 stored
decoder produces are never distribution receipts (`decodeStored_not_distribution`).

`SRel x y` relates two read-logging store programs: identical, or `x` stops with an exclusion,
node by node (so the reads up to that point are the same). `LR` is its `LM` form.

* `forwardOrBuffer_eq`: on a non-distribution receipt, `forwardOrBufferLWith globalQueuePolicy` is
  `forwardOrBufferL`.
* The D2 queue operations are the `QueuePolicy` operations at `d2Policy` (`delayPopL_eq`, …), and
  operations at two policies related by `PolRel` refine (`delayPopWith_rel`, `fwdLoopWith_rel`, …).
  Hence `delayPop_rel`, `forwardFromBuffer_rel`, `forwardFromBufferV3_rel`: the D2 queue operations
  refine the global ones (`LR`) on a well-formed layout.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged

/-! ## Layouts -/

/-- The integrator-decided hypothesis on every layout of a claim (nearcore's `ShardLayout`
constructors assert it, `shard_layout/v2.rs:63,207`, `v3.rs:100,211`). -/
def _root_.NearSpecV3.Layout.WF (l : Layout) : Prop := l.shardIds.length = l.boundaries.length + 1

theorem partitionPoint_le (acct : Bytes) : ∀ bs : List Bytes, partitionPoint acct bs ≤ bs.length
  | [] => Nat.le_refl _
  | b :: bs => by
    unfold partitionPoint
    split
    · have := partitionPoint_le acct bs; simp only [List.length_cons]; omega
    · exact Nat.zero_le _

theorem _root_.NearSpecV3.Layout.shardOf_mem {l : Layout} (h : l.WF) (a : Bytes) : l.shardIds.contains (l.shardOf a) = true := by
  unfold Layout.shardOf
  have hl : partitionPoint a l.boundaries < l.shardIds.length := by
    have := partitionPoint_le a l.boundaries; unfold Layout.WF at h; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact List.contains_iff_mem.mpr (List.getElem_mem hl)

theorem globalTarget_wf {l : Layout} (h : l.WF) (r : Rcpt) (hr : rcptIsDistribution r = false) :
    StorageExecution.globalTarget l r = .ok (l.shardOf r.recv) :=
  globalTarget_of_not_distribution l r hr (Layout.shardOf_mem h _)

/-! ## `SRel`: refinement of store programs -/

inductive SRel {K α : Type} : SM K α → SM K α → Prop where
  | refl (x : SM K α) : SRel x x
  | ex (e : String) (he : isExclusion e = true) (y : SM K α) : SRel (.err e) y
  | get (k : K) (c c' : Option Bytes → SM K α) (h : ∀ v, SRel (c v) (c' v)) : SRel (.get k c) (.get k c')

theorem SRel.bind_same {K α β : Type} (x : SM K α) {f g : α → SM K β} (h : ∀ a, SRel (f a) (g a)) :
    SRel (x.bind f) (x.bind g) := by
  induction x with
  | ok a => exact h a
  | err e => exact SRel.refl _
  | get k c ih => exact SRel.get k _ _ ih

theorem SRel.bind {K α β : Type} {x y : SM K α} {f g : α → SM K β} (hx : SRel x y)
    (h : ∀ a, SRel (f a) (g a)) : SRel (x.bind f) (y.bind g) := by
  induction hx with
  | refl x => exact SRel.bind_same x h
  | ex e he y => exact SRel.ex e he _
  | get k c c' _ ih => exact SRel.get k _ _ ih

theorem SRel.runAcc {K α : Type} {x y : SM K α} (h : SRel x y) (s : K → Option Bytes) (acc : List K) :
    (∃ e acc', SM.runAcc s x acc = (.error e, acc') ∧ isExclusion e = true) ∨
      SM.runAcc s x acc = SM.runAcc s y acc := by
  induction h generalizing acc with
  | refl x => exact Or.inr rfl
  | ex e he y => exact Or.inl ⟨e, acc, rfl, he⟩
  | get k c c' _ ih => exact ih (s k) (k :: acc)

theorem SRel.runR {K α : Type} {x y : SM K α} (h : SRel x y) (s : K → Option Bytes) :
    (∃ e ks, SM.runR s x = (.error e, ks) ∧ isExclusion e = true) ∨ SM.runR s x = SM.runR s y := by
  unfold SM.runR
  rcases h.runAcc s [] with ⟨e, acc', h1, he⟩ | h1
  · left; exact ⟨e, acc'.reverse, by rw [h1], he⟩
  · right; rw [h1]

/-- `LM` form. -/
def LR {α : Type} (x y : LM α) : Prop := ∀ root, SRel (x root) (y root)

theorem LR.refl {α : Type} (x : LM α) : LR x x := fun _ => SRel.refl _

theorem LR.bind {α β : Type} {x y : LM α} {f g : α → LM β} (hx : LR x y) (h : ∀ a, LR (f a) (g a)) :
    LR (x >>= f) (y >>= g) := fun root => SRel.bind (hx root) fun a => h a root

theorem LR.ex {α : Type} (e : String) (he : isExclusion e = true) (y : LM α) : LR (throw e) y :=
  fun _ => SRel.ex e he _

theorem LR.throw_bind {α β : Type} (e : String) (he : isExclusion e = true) (f : α → LM β) (y : LM β) :
    LR (throw e >>= f) y := fun _ => SRel.ex e he _

theorem LR.throw_bind_same {α β : Type} (e : String) (f g : α → LM β) :
    LR (throw e >>= f) (throw e >>= g) := fun _ => SRel.refl _

theorem LR.ite {α : Type} (c : Prop) [Decidable c] {a b a' b' : LM α} (ha : c → LR a a') (hb : ¬ c → LR b b') :
    LR (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha h
  · rw [if_neg h, if_neg h]; exact hb h

theorem LR.foldlM {α β : Type} (l : List β) (init : α) {f g : α → β → LM α} (h : ∀ a b, LR (f a b) (g a b)) :
    LR (l.foldlM f init) (l.foldlM g init) := by
  induction l generalizing init with
  | nil => exact LR.refl _
  | cons x t ih =>
    simp only [List.foldlM_cons]
    exact LR.bind (h init x) fun a => ih a

/-! ## Queue operations -/

theorem forwardOrBuffer_eq (env : Env) (hwf : env.ctx.layout.WF) (rs : RS) (r : Rcpt)
    (hr : rcptIsDistribution r = false) :
    forwardOrBufferLWith StorageExecution.globalQueuePolicy env rs r = forwardOrBufferL env rs r := by
  unfold forwardOrBufferLWith forwardOrBufferL
  simp only [StorageExecution.globalQueuePolicy]
  rw [globalTarget_wf hwf r hr]
  rfl

/-! ## The D2 queue operations as policy instances -/

/-- The D2 queue policy: the D2 stored decoder and account routing. -/
def d2Policy : QueuePolicy := ⟨decodeStored, fun l r => .ok (l.shardOf r.recv)⟩

theorem delayPopL_eq (env : Env) : ∀ fuel rs, delayPopL env fuel rs = delayPopLWith d2Policy env fuel rs
  | 0, _ => rfl
  | fuel + 1, rs => by
    unfold delayPopL delayPopLWith
    simp only [delayPopL_eq env fuel]
    rfl

/-- Two queue policies agree where the first decodes, up to its `w.shape` exclusions. -/
def PolRel (l : Layout) (P1 P2 : QueuePolicy) : Prop :=
  (∀ b, Codec.XR Codec.Shape (P1.decodeStored b) (P2.decodeStored b)) ∧
  ∀ b st, P1.decodeStored b = .ok st → P1.target l st.r = P2.target l st.r

theorem polRel_global (l : Layout) (hwf : l.WF) : PolRel l d2Policy StorageExecution.globalQueuePolicy := by
  refine ⟨fun b => Codec.decodeStored_ref b, fun b st h => ?_⟩
  show Except.ok (l.shardOf st.r.recv) = StorageExecution.globalTarget l st.r
  rw [globalTarget_wf hwf _ (Codec.decodeStored_not_distribution b st h)]

macro "lr_same" : tactic => `(tactic| repeat (first
  | (with_reducible exact LR.refl _)
  | (exact LR.throw_bind_same _ _ _)
  | ((refine LR.bind (LR.refl _) fun ⟨_, _⟩ => ?_); try dsimp only)
  | ((refine LR.bind (LR.refl _) fun _ => ?_); try dsimp only)
  | (refine LR.ite _ (fun _ => ?_) (fun _ => ?_))))

/-- Case on a stored decode under `PolRel`: rewrite the upper decode to the lower one where they
agree, else the lower run stops with a `w.shape` exclusion. -/
theorem LR.decPol {β : Type} {l : Layout} {P1 P2 : QueuePolicy} (h : PolRel l P1 P2) (b : Bytes) (w : String)
    {f g : Stored → LM β}
    (hfg : ∀ st, P1.decodeStored b = .ok st → LR (f st) (g st)) :
    LR ((match P1.decodeStored b with
          | .ok st => pure st
          | .error e => if isShapeOOD e then throw e else throw (inconsistent w)) >>= f)
      ((match P2.decodeStored b with
          | .ok st => pure st
          | .error e => if isShapeOOD e then throw e else throw (inconsistent w)) >>= g) := by
  rcases h.1 b with h1 | ⟨e, h1, hX⟩
  · rw [← h1]
    cases hd : P1.decodeStored b with
    | ok st => exact hfg st hd
    | error e => dsimp only; split <;> exact LR.throw_bind_same _ _ _
  · rw [h1]
    dsimp only
    rw [if_pos (show isShapeOOD e = true from hX)]
    exact LR.throw_bind _ (Codec.shape_excl e hX) _ _

theorem delayPopWith_rel (env : Env) (P1 P2 : QueuePolicy) (h : PolRel env.ctx.layout P1 P2) :
    ∀ fuel rs, LR (delayPopLWith P1 env fuel rs) (delayPopLWith P2 env fuel rs)
  | 0, _ => LR.refl _
  | fuel + 1, rs => by
    unfold delayPopLWith
    lr_same
    split
    · lr_same
    · rename_i b
      rcases h.1 b with h1 | ⟨e, h1, hX⟩
      · rw [← h1]
        split
        · rename_i st hd
          simp only [pure_bind]
          rw [h.2 b st hd]
          lr_same
          all_goals exact delayPopWith_rel env P1 P2 h fuel _
        · split <;> lr_same
      · rw [h1]
        dsimp only
        rw [if_pos (show isShapeOOD e = true from hX)]
        exact LR.throw_bind _ (Codec.shape_excl e hX) _ _

theorem fwdLoopL_eq (env : Env) (s : Nat) :
    ∀ fuel i acc, fwdLoopL env s fuel i acc = fwdLoopLWith d2Policy env s fuel i acc
  | 0, _, _ => rfl
  | fuel + 1, i, acc => by
    unfold fwdLoopL fwdLoopLWith readBufferedFromTrieL readBufferedFromTrieLWith
    simp only [fwdLoopL_eq env s fuel]
    rfl

/-- `SRel` whose common successful results satisfy `Q`. -/
inductive SRelQ {K α : Type} (Q : α → Prop) : SM K α → SM K α → Prop where
  | ok (a : α) (h : Q a) : SRelQ Q (.ok a) (.ok a)
  | err (e : String) : SRelQ Q (.err e) (.err e)
  | ex (e : String) (he : isExclusion e = true) (y : SM K α) : SRelQ Q (.err e) y
  | get (k : K) (c c' : Option Bytes → SM K α) (h : ∀ v, SRelQ Q (c v) (c' v)) : SRelQ Q (.get k c) (.get k c')

theorem SRelQ.bind {K α β : Type} {Q : α → Prop} {x y : SM K α} {f g : α → SM K β} (hx : SRelQ Q x y)
    (h : ∀ a, Q a → SRel (f a) (g a)) : SRel (x.bind f) (y.bind g) := by
  induction hx with
  | ok a hq => exact h a hq
  | err e => exact SRel.refl _
  | ex e he y => exact SRel.ex e he _
  | get k c c' _ ih => exact SRel.get k _ _ ih

theorem SRelQ.bind_same {K α β : Type} {Q : β → Prop} (x : SM K α) {f g : α → SM K β}
    (h : ∀ a, SRelQ Q (f a) (g a)) : SRelQ Q (x.bind f) (x.bind g) := by
  induction x with
  | ok a => exact h a
  | err e => exact SRelQ.err e
  | get k c ih => exact SRelQ.get k _ _ ih

def LRQ {α : Type} (Q : α → Prop) (x y : LM α) : Prop := ∀ root, SRelQ Q (x root) (y root)

theorem LR.bindQ {α β : Type} {Q : α → Prop} {x y : LM α} {f g : α → LM β} (hx : LRQ Q x y)
    (h : ∀ a, Q a → LR (f a) (g a)) : LR (x >>= f) (y >>= g) :=
  fun root => SRelQ.bind (hx root) fun a hq => h a hq root

theorem readBufferedWith_rel (l : Layout) (P1 P2 : QueuePolicy) (h : PolRel l P1 P2) (s i : Nat) :
    LRQ (fun st => P1.target l st.r = P2.target l st.r)
      (readBufferedFromTrieLWith P1 s i) (readBufferedFromTrieLWith P2 s i) := by
  intro root
  unfold readBufferedFromTrieLWith
  refine SRelQ.bind_same _ fun v => ?_
  dsimp only
  split
  · rename_i raw
    cases raw with
    | none => exact SRelQ.err _
    | some b =>
      simp only [pure_bind]
      rcases h.1 b with h1 | ⟨e, h1, hX⟩
      · rw [← h1]
        cases hd : P1.decodeStored b with
        | ok st => exact SRelQ.ok st (h.2 b st hd)
        | error e => dsimp only; split <;> exact SRelQ.err _
      · rw [h1]
        dsimp only
        rw [if_pos (show isShapeOOD e = true from hX)]
        exact SRelQ.ex _ (Codec.shape_excl e hX) _
  · exact SRelQ.err _

theorem fwdLoopWith_rel (env : Env) (P1 P2 : QueuePolicy) (h : PolRel env.ctx.layout P1 P2) (s : Nat) :
    ∀ fuel i acc, LR (fwdLoopLWith P1 env s fuel i acc) (fwdLoopLWith P2 env s fuel i acc)
  | 0, _, _ => LR.refl _
  | fuel + 1, i, acc => by
    obtain ⟨rs, k, pops⟩ := acc
    unfold fwdLoopLWith
    lr_same
    refine LR.bindQ (readBufferedWith_rel _ P1 P2 h s i) fun st hst => ?_
    dsimp only
    rw [hst]
    lr_same
    all_goals (try split) <;> lr_same
    all_goals exact fwdLoopWith_rel env P1 P2 h s fuel _ _

theorem forwardFromBufferToShardL_eq (env : Env) (rs : RS) (s : Nat) :
    forwardFromBufferToShardL env rs s = forwardFromBufferToShardLWith d2Policy env rs s := by
  unfold forwardFromBufferToShardL forwardFromBufferToShardLWith
  simp only [fwdLoopL_eq]

theorem forwardFromBufferToShardWith_rel (env : Env) (P1 P2 : QueuePolicy) (h : PolRel env.ctx.layout P1 P2)
    (rs : RS) (s : Nat) :
    LR (forwardFromBufferToShardLWith P1 env rs s) (forwardFromBufferToShardLWith P2 env rs s) := by
  unfold forwardFromBufferToShardLWith
  exact LR.bind (fwdLoopWith_rel env P1 P2 h s _ _ _) fun _ => LR.refl _

theorem forwardFromBufferL_eq (env : Env) (rs : RS) :
    forwardFromBufferL env rs = forwardFromBufferLWith d2Policy env rs := by
  unfold forwardFromBufferL forwardFromBufferLWith
  have : forwardFromBufferToShardL env = forwardFromBufferToShardLWith d2Policy env :=
    funext fun rs => funext fun s => forwardFromBufferToShardL_eq env rs s
  rw [this]

theorem forwardFromBufferWith_rel (env : Env) (P1 P2 : QueuePolicy) (h : PolRel env.ctx.layout P1 P2) (rs : RS) :
    LR (forwardFromBufferLWith P1 env rs) (forwardFromBufferLWith P2 env rs) := by
  unfold forwardFromBufferLWith
  refine LR.ite _ (fun _ => LR.refl _) fun _ => ?_
  exact LR.foldlM _ _ fun a b => forwardFromBufferToShardWith_rel env P1 P2 h a b

/-! ## The four queue operations of the engine, D2 against global -/

theorem delayPop_rel (env : Env) (hwf : env.ctx.layout.WF) (fuel : Nat) (rs : RS) :
    LR (delayPopL env fuel rs) (delayPopLWith StorageExecution.globalQueuePolicy env fuel rs) := by
  rw [delayPopL_eq]; exact delayPopWith_rel env _ _ (polRel_global _ hwf) fuel rs

theorem forwardFromBuffer_rel (env : Env) (hwf : env.ctx.layout.WF) (rs : RS) :
    LR (forwardFromBufferL env rs) (forwardFromBufferLWith StorageExecution.globalQueuePolicy env rs) := by
  rw [forwardFromBufferL_eq]; exact forwardFromBufferWith_rel env _ _ (polRel_global _ hwf) rs

theorem forwardFromBufferV3_rel (env : Env) (hwf : env.ctx.layout.WF) (rs : RS) :
    LR (StorageExecution.forwardFromBufferV3L false env rs) (StorageExecution.forwardFromBufferV3L true env rs) := by
  unfold StorageExecution.forwardFromBufferV3L
  have : forwardFromBufferToShardL env = forwardFromBufferToShardLWith d2Policy env :=
    funext fun rs => funext fun s => forwardFromBufferToShardL_eq env rs s
  simp only [Bool.false_eq_true, ↓reduceIte, this]
  refine LR.bind (LR.foldlM _ _ fun a b => forwardFromBufferToShardWith_rel env _ _ (polRel_global _ hwf) a b)
    fun _ => LR.refl _

#print axioms forwardOrBuffer_eq
#print axioms delayPop_rel
#print axioms forwardFromBuffer_rel
#print axioms forwardFromBufferV3_rel

end NearSpecV3.Successor
