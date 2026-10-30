import NearSpecV3.D2SubD3.GasFree

/-!
# D2 ⊂ D3, step 2: under a gas-free hook the chunk's `wasmGas` stays 0

`RS.wasmGas` is written only by `applyActionReceipt` (`wasmGas := rs.wasmGas + res.gasFC`); every
other runtime function copies it through `{ rs with … }`. With a gas-free hook `res.gasFC = 0`
(`applyAction_gasFC`), so every function of the D2 runtime preserves `wasmGas`, and
`applyNewChunkD2` (which starts from `wasmGas = 0`) returns `wasmGas = 0`.
-/

namespace NearSpecV3.D2
open NearSpec NearSpecV3

namespace PostE

theorem foldlM {α β : Type} (l : List β) (init : α) {f : α → β → Except String α}
    (I : α → Prop) (h0 : I init) (hf : ∀ a b, I a → PostE (f a b) I) : PostE (l.foldlM f init) I := by
  induction l generalizing init with
  | nil => exact pure' h0
  | cons x t ih =>
    simp only [List.foldlM_cons]
    exact bind (hf init x h0) fun a ha => ih a ha

theorem ok' {α : Type} {P : α → Prop} {a : α} (h : P a) : PostE (Except.ok a : Except String α) P :=
  fun _ e => by cases e; exact h

end PostE

/-- Registry of callee lemmas (extended below). -/
syntax "wg_close" : tactic
macro_rules | `(tactic| wg_close) => `(tactic| fail "wg_close")

/-- Finish a `pure` exit: projections of record literals, then linear arithmetic on the
hypotheses collected along the way. -/
macro "wg_fin" : tactic => `(tactic| first
  | rfl
  | exact rfl
  | (simp only [RS.setMeta, RS.writeDelayedIdx]; done)
  | (dsimp only [RS.setMeta, RS.writeDelayedIdx] at *; omega)
  | (simp_all [RS.setMeta, RS.writeDelayedIdx, AR.fail]; done)
  | (simp_all [RS.setMeta, RS.writeDelayedIdx, AR.fail]; omega))

macro "wg_walk" : tactic => `(tactic|
  repeat' (first
    | (exact PostE.throw' _)
    | wg_close
    | (with_reducible apply PostE.pure'; wg_fin)
    | (with_reducible apply PostE.ok'; wg_fin)
    | (with_reducible apply PostE.ite' _ ?_ ?_)
    | (simp only [pure_bind])
    | (with_reducible apply PostE.bind_any; intro)
    | (dsimp only)
    | (split)))


/-! ## Queues -/

theorem setMeta_wg (rs : RS) (s : Nat) (m : Meta) : (rs.setMeta s m).wasmGas = rs.wasmGas := rfl
theorem writeDelayedIdx_wg (rs : RS) : rs.writeDelayedIdx.wasmGas = rs.wasmGas := rfl

theorem groupsPopBack_wg (rs : RS) (s : Nat) (m : Meta) :
    PostE (groupsPopBack rs s m) fun p => p.1.wasmGas = rs.wasmGas := by
  unfold groupsPopBack; wg_walk

theorem groupsPushBack_wg (rs : RS) (s : Nat) (m : Meta) (size gas : Nat) :
    PostE (groupsPushBack rs s m size gas) fun p => p.1.wasmGas = rs.wasmGas := by
  unfold groupsPushBack; wg_walk

macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (groupsPopBack_wg _ _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (groupsPushBack_wg _ _ _ _ _) fun _ _ => ?_))

theorem metaPushed_wg (rs : RS) (s size gas : Nat) :
    PostE (metaPushed rs s size gas) fun r => r.wasmGas = rs.wasmGas := by
  unfold metaPushed; wg_walk

theorem metaPopped_wg (rs : RS) (s size gas : Nat) :
    PostE (metaPopped rs s size gas) fun r => r.wasmGas = rs.wasmGas := by
  unfold metaPopped; wg_walk


macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (metaPushed_wg _ _ _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (metaPopped_wg _ _ _ _) fun _ _ => ?_))

theorem bufferReceipt_wg (rs : RS) (r : Rcpt) (size gas shard : Nat) :
    PostE (bufferReceipt rs r size gas shard) fun x => x.wasmGas = rs.wasmGas := by
  unfold bufferReceipt; wg_walk

macro_rules | `(tactic| wg_close) => `(tactic| (refine PostE.mono (bufferReceipt_wg _ _ _ _ _) fun _ h => ?_; exact h))

theorem forwardOrBuffer_wg (env : Env) (rs : RS) (r : Rcpt) :
    PostE (forwardOrBuffer env rs r) fun x => x.wasmGas = rs.wasmGas := by
  unfold forwardOrBuffer; wg_walk

macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (forwardOrBuffer_wg _ _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (refine PostE.mono (forwardOrBuffer_wg _ _ _) fun _ h => ?_; exact h))

theorem fwdLoop_wg (env : Env) (s : Nat) : ∀ (fuel i : Nat) (acc : RS × Nat × List (Nat × Nat)),
    PostE (fwdLoop env s fuel i acc) fun p => p.1.wasmGas = acc.1.wasmGas
  | 0, i, acc => PostE.ok' rfl
  | fuel + 1, i, (rs, k, pops) => by
    unfold fwdLoop
    wg_walk
    all_goals (refine PostE.mono (fwdLoop_wg env s fuel _ _) fun _ h => ?_; exact h)

theorem foldl_o_wg (l : List Nat) (rs : RS) (g : RS → Nat → Ovl) :
    (l.foldl (fun rs j => { rs with o := g rs j }) rs).wasmGas = rs.wasmGas := by
  induction l generalizing rs with
  | nil => rfl
  | cons x t ih => exact ih _

theorem forwardFromBufferToShard_wg (env : Env) (rs : RS) (s : Nat) :
    PostE (forwardFromBufferToShard env rs s) fun x => x.wasmGas = rs.wasmGas := by
  unfold forwardFromBufferToShard
  refine PostE.bind (fwdLoop_wg env s _ _ _) fun p hp => ?_
  obtain ⟨rs1, k, pops⟩ := p
  dsimp only at hp ⊢
  refine PostE.mono (PostE.foldlM pops _ (fun x => x.wasmGas = rs.wasmGas) ?_ fun a b ha =>
    PostE.mono (metaPopped_wg a _ _ _) fun _ h => h.trans ha) fun _ h => h
  split
  · dsimp only; rw [foldl_o_wg]; exact hp
  · rw [foldl_o_wg]; exact hp

theorem forwardFromBuffer_wg (env : Env) (rs : RS) :
    PostE (forwardFromBuffer env rs) fun x => x.wasmGas = rs.wasmGas := by
  unfold forwardFromBuffer
  dsimp only
  split
  · exact PostE.bind (Q := fun _ => False) (PostE.throw' _) fun _ h => h.elim
  · exact PostE.foldlM _ _ _ rfl fun a b ha =>
      PostE.mono (forwardFromBufferToShard_wg env a b) fun _ h => h.trans ha

theorem delayPush_wg (rs : RS) (r : Rcpt) :
    PostE (delayPush rs r) fun x => x.wasmGas = rs.wasmGas := by
  unfold delayPush; wg_walk

theorem delayPop_wg (env : Env) : ∀ (fuel : Nat) (rs : RS),
    PostE (delayPop env fuel rs) fun p => p.1.wasmGas = rs.wasmGas
  | 0, rs => PostE.ok' rfl
  | fuel + 1, rs => by
    unfold delayPop
    wg_walk
    all_goals (refine PostE.mono (delayPop_wg env fuel _) fun _ h => ?_; exact h)


/-! ## Receipts -/

theorem ok_add64 (a b : Nat) (e : String) : PostE (ok? (add64 a b) e) fun r => r = a + b := by
  unfold ok? add64; split <;> rename_i h <;> split at h <;> cases h
  · exact PostE.ok' rfl
  · exact PostE.throw' _

macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (ok_add64 _ _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (applyAction_gasFC _ ‹GasFree _› _ _ _) fun _ _ => ?_))

theorem actionLoop_gasFC (h : ActionHooks) (hg : GasFree h) (env : Env) (r : Rcpt) (a : ActionR)
    (inputs : List (Option Bytes)) (deployed attempted : List Bytes) : ∀ (i : Nat) (acts : List Act)
    (acc : ActSt × AR),
    PostE (actionLoop h env r a inputs deployed attempted i acts acc) fun p => p.2.gasFC = acc.2.gasFC
  | _, [], acc => PostE.ok' rfl
  | i, act :: rest, (st, res) => by
    unfold actionLoop
    wg_walk
    all_goals (refine PostE.mono (actionLoop_gasFC h hg env r a inputs deployed attempted _ rest _) fun _ h => ?_)
    all_goals first | (simp_all [AR.fail]; done) | (simp_all [AR.fail]; omega)

theorem emitReceipts_wg (env : Env) (parent : Bytes) : ∀ (rs : RS) (k : Nat) (l : List Rcpt),
    PostE (emitReceipts env parent rs k l) fun p => p.1.wasmGas = rs.wasmGas
  | rs, _, [] => PostE.ok' rfl
  | rs, k, nr :: rest => by
    unfold emitReceipts
    dsimp only
    split
    · refine PostE.bind (PostE.pure' (P := fun (x : RS) => x.wasmGas = rs.wasmGas) rfl) fun rs1 h1 => ?_
      exact PostE.bind (emitReceipts_wg env parent rs1 _ rest) fun p hp => PostE.pure' (hp.trans h1)
    · refine PostE.bind (forwardOrBuffer_wg _ _ _) fun rs1 h1 => ?_
      exact PostE.bind (emitReceipts_wg env parent rs1 _ rest) fun p hp => PostE.pure' (hp.trans h1)


macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (actionLoop_gasFC _ ‹GasFree _› _ _ _ _ _ _ _ _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (emitReceipts_wg _ _ _ _ _) fun _ _ => ?_))

set_option maxHeartbeats 4000000 in
theorem applyActionReceipt_wg (h : ActionHooks) (hg : GasFree h) (env : Env) (rs : RS) (r : Rcpt)
    (a : ActionR) : PostE (applyActionReceipt h env rs r a) fun p => p.1.wasmGas = rs.wasmGas := by
  unfold applyActionReceipt
  wg_walk


macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (applyActionReceipt_wg _ ‹GasFree _› _ _ _ _) fun _ _ => ?_))

set_option maxHeartbeats 4000000 in
theorem processReceipt_wg (h : ActionHooks) (hg : GasFree h) (env : Env) (rs : RS) (r : Rcpt) :
    PostE (processReceipt h env rs r) fun p => p.1.wasmGas = rs.wasmGas := by
  unfold processReceipt
  wg_walk

macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (processReceipt_wg _ ‹GasFree _› _ _ _) fun _ _ => ?_))

theorem processWithTotals_wg (h : ActionHooks) (hg : GasFree h) (env : Env) (rs : RS) (r : Rcpt) :
    PostE (processWithTotals h env rs r) fun x => x.wasmGas = rs.wasmGas := by
  unfold processWithTotals
  wg_walk


macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (processWithTotals_wg _ ‹GasFree _› _ _ _) fun _ _ => ?_))

theorem drain_wg (h : ActionHooks) (hg : GasFree h) (env : Env) : ∀ (fuel : Nat) (rs : RS),
    PostE (processWithInstant.drain h env fuel rs) fun x => x.wasmGas = rs.wasmGas
  | 0, rs => PostE.throw' _
  | fuel + 1, rs => by
    unfold processWithInstant.drain
    split
    · exact PostE.ok' rfl
    · exact PostE.bind (processWithTotals_wg h hg env _ _) fun x hx =>
        PostE.mono (drain_wg h hg env fuel x) fun _ h2 => h2.trans hx

theorem processWithInstant_wg (h : ActionHooks) (hg : GasFree h) (env : Env) (rs : RS) (r : Rcpt) :
    PostE (processWithInstant h env rs r) fun x => x.wasmGas = rs.wasmGas := by
  unfold processWithInstant
  exact PostE.bind (processWithTotals_wg h hg env _ _) fun x hx =>
    PostE.mono (drain_wg h hg env _ x) fun _ h2 => h2.trans hx

theorem processLocals_wg (h : ActionHooks) (hg : GasFree h) (env : Env) (rs : RS) (l : List Rcpt) :
    PostE (processLocals h env rs l) fun x => x.wasmGas = rs.wasmGas := by
  unfold processLocals
  refine PostE.foldlM _ _ _ rfl fun a b ha => ?_
  split
  · exact PostE.mono (delayPush_wg _ _) fun _ h2 => h2.trans ha
  · exact PostE.mono (processWithInstant_wg h hg env _ _) fun _ h2 => h2.trans ha

theorem processDelayed_wg (h : ActionHooks) (hg : GasFree h) (env : Env) : ∀ (fuel : Nat) (rs : RS),
    PostE (processDelayed h env fuel rs) fun x => x.wasmGas = rs.wasmGas
  | 0, rs => PostE.ok' rfl
  | fuel + 1, rs => by
    unfold processDelayed
    dsimp only
    split
    · exact PostE.pure' rfl
    · refine PostE.bind (delayPop_wg env _ _) fun p hp => ?_
      obtain ⟨rs1, ro⟩ := p
      dsimp only at hp ⊢
      split
      · exact PostE.pure' hp
      · split
        · exact PostE.bind (Q := fun _ => False) (PostE.throw' _) fun _ h => h.elim
        · exact PostE.bind (processWithInstant_wg h hg env _ _) fun x hx =>
            PostE.mono (processDelayed_wg h hg env fuel x) fun _ h2 => (h2.trans hx).trans hp

theorem processIncoming_wg (h : ActionHooks) (hg : GasFree h) (env : Env) (rs : RS) (l : List Rcpt) :
    PostE (processIncoming h env rs l) fun x => x.wasmGas = rs.wasmGas := by
  unfold processIncoming
  refine PostE.foldlM _ _ _ rfl fun a b ha => ?_
  dsimp only
  split
  · exact PostE.bind (Q := fun _ => False) (PostE.throw' _) fun _ h => h.elim
  · split
    · exact PostE.mono (delayPush_wg _ _) fun _ h2 => h2.trans ha
    · exact PostE.mono (processWithInstant_wg h hg env _ _) fun _ h2 => h2.trans ha

theorem fob_ite_wg (env : Env) (rs : RS) (c : Prop) [Decidable c] (x : RS) (r : Rcpt)
    (hx : x.wasmGas = rs.wasmGas) :
    PostE (if c then pure x else forwardOrBuffer env rs r) fun y => y.wasmGas = rs.wasmGas := by
  split
  · exact PostE.pure' hx
  · exact forwardOrBuffer_wg _ _ _

macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (fob_ite_wg _ _ _ _ _ (by exact rfl)) fun _ _ => ?_))

set_option maxHeartbeats 4000000 in
theorem processTxD2_wg (env : Env) (p : RS × List Bytes) (tf : TxD2 × Bool) :
    PostE (processTxD2 env p tf) fun q => q.1.wasmGas = p.1.wasmGas := by
  unfold processTxD2
  wg_walk

theorem yieldLoop_wg (env : Env) (next : Nat) : ∀ (fuel : Nat) (acc : RS × Nat × Nat),
    PostE (yieldLoop env next fuel acc) fun q => q.1.wasmGas = acc.1.wasmGas
  | 0, acc => by unfold yieldLoop; wg_walk
  | fuel + 1, (rs, i, k) => by
    unfold yieldLoop
    wg_walk
    all_goals (refine PostE.mono (yieldLoop_wg env next fuel _) fun _ h => ?_; first | exact h | (simp_all; done) | (simp_all; omega))


theorem txs_foldlM_wg (env : Env) (l : List (TxD2 × Bool)) (p : RS × List Bytes) :
    PostE (l.foldlM (processTxD2 env) p) fun q => q.1.wasmGas = p.1.wasmGas :=
  PostE.foldlM _ _ (fun q => q.1.wasmGas = p.1.wasmGas) rfl fun a b ha =>
    PostE.mono (processTxD2_wg env a b) fun _ h => h.trans ha

macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (forwardFromBuffer_wg _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (txs_foldlM_wg _ _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (processLocals_wg _ ‹GasFree _› _ _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (processDelayed_wg _ ‹GasFree _› _ _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (processIncoming_wg _ ‹GasFree _› _ _ _) fun _ _ => ?_))
macro_rules | `(tactic| wg_close) => `(tactic| (with_reducible refine PostE.bind (yieldLoop_wg _ _ _ _) fun _ _ => ?_))

set_option maxHeartbeats 8000000 in
/-- **Under a gas-free hook, the D2 runtime reports no function-call gas.** -/
theorem applyNewChunkD2_wasmGas (h : ActionHooks) (hg : GasFree h) (prims : Prims) (env : Env)
    (t : PTrie) (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    PostE (applyNewChunkD2 h prims env t vu lastProps incoming txs ownCong) fun out => out.wasmGas = 0 := by
  unfold applyNewChunkD2
  wg_walk

end NearSpecV3.D2
