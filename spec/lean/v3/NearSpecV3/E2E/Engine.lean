import NearSpecV3.Successor.StorageExecution

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# E2E-M11, obligation 3 (part 1): the whole-state engine as a small-step machine

`StorageExecution.applyNewChunkD2 … >>= raceCheck`, the computation the recorder engine `run`
executes, is cut into the steps of the E2E plan §3.1 item 2: one prelude step (validator update,
delayed-queue load, bandwidth scheduler, buffered forwarding), one step per transaction, per local
receipt, per delayed receipt, per incoming receipt and per yield timeout, phase-change steps, and
one finalize step (congestion, bandwidth requests, `finalize`, totals, race check).

Nothing is reimplemented. Each step body is a verbatim slice of the engine (`prelude`,
`localsBody`, `incomingBody`, `delayedK`, `yieldK`, `finalizeStep`), and the equations
`applyNewChunkD2_split`, `processLocals_eq`, `processIncoming_eq`, `processDelayedLoop_succ` and
`yieldLoop_succ` state that the engine **is** the composition of the slices. A configuration
(`EConf`) is the engine's own state at a step boundary: the position (phase tag, remaining work)
with the receipt state `RS` (trie overlay = the working set as a map, delayed and buffered queue
indices, gas/compute/burnt totals, outcomes, outgoing receipts, proposals, congestion, limits) and
the `Recording` (recorder, pipeline schedule).

Granularity: a step is one whole receipt including its instant receipts and its Wasm calls. A
mid-call cut (plan §3.2, `inCall`) refines one receipt step through `Wasm.run_foldSegments`; that
refinement is not done here (plan §3.5, status).

Results: `den_step` (every position's denotation is one step followed by the successor's
denotation), `den_ok_iff` and `engine_run_ok_iff` (`StorageExecution.run … = .ok out` iff the
machine reaches `done out`).
-/

namespace NearSpecV3.E2E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution

/-- The static inputs of one main transition: the arguments of `StorageExecution.run`. -/
structure Prog where
  fl : Flags
  hooks : NearCfg
  prims : Prims
  env : Env
  t : PTrie
  vu : Option ValidatorUpdateFacts
  props : List (Bytes × Nat)
  incoming : List Rcpt
  txs : List (TxD2 × Bool)
  cong : Congestion

/-- A position of the engine machine: phase tag and remaining work, with the receipt state. -/
inductive EPos where
  | start
  | txs (rest : List (TxD2 × Bool)) (acc : List Bytes) (rs : RS)
  | locals (rest : List Rcpt) (rs : RS)
  | delayed (fuel : Nat) (rs : RS)
  | incoming (rest : List Rcpt) (rs : RS)
  | yields (yf yn fuel i k : Nat) (rs : RS)
  | done (out : MainOutD2)

/-! ## The verbatim slices -/

/-- Steps 1–4 of `applyNewChunkD2`, verbatim, followed by a continuation. -/
def preludeK {β : Type} (fl : Flags) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat)) (ownCong : Congestion)
    (k : RS → M β) : M β := do
  let ctx := env.ctx
  let o := Ovl.ofTrie t
  -- 1. validator accounts update
  let o ← match vu with
    | some f => validatorUpdateR ctx.layout ctx.own o f lastProps
    | none => pure o
  -- 2. delayed queue load
  let (df, dn) ← getIndicesR o kDelayedIdx "DelayedReceiptIndices"
  -- 3. bandwidth scheduler
  let (o, so) ← schedOvlR prims ctx o
  -- 4. receipt sink (indices and metadata read from the trie)
  let bufIdx ← match ← trieFindR kBufIdx with
    | none => throw (missing "BufferedReceiptIndices")
    | some none => pure []
    | some (some b) => okR (decodeBufIdx b) (inconsistent "BufferedReceiptIndices")
  let metas ← bufIdx.foldlM (fun ms (s, _, _) => do
      match ← trieFindR (kGroupsData s) with
      | none => throw (missing "BufferedReceiptGroupsQueueData")
      | some none => pure ms
      | some (some b) => match decodeMeta b with
        | some m => pure (ms ++ [(s, m)])
        | none => throw (inconsistent "BufferedReceiptGroupsQueueData")) []
  let limits : List Limit := ctx.statuses.map fun (s, ci, missed) =>
    ⟨s, (if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own), so.grant ctx.own s⟩
  let rs : RS := { o, limits, outgoing := [], bufIdx, metas, cong := ownCong, dq := ⟨df, dn, 0, 0, 0, 0⟩,
                   outcomes := [], gas := 0, compute := 0, txBurnt := 0, otherBurnt := 0,
                   proposals := [], instant := [], locals := [] }
  let rs ← forwardFromBufferR fl.globalActions env rs
  k rs

/-- The stored-receipt decoder `pipeDecode` returns. -/
def decodeOf (ga : Bool) : Bytes → Except String Rcpt :=
  if ga then fun b => GlobalCodecs.decodeStoredRcptGlobal b "stored receipt"
  else fun b => decodeStoredRcpt b "stored receipt"

theorem pipeDecode_eq (ga : Bool) : pipeDecode ga = pure (decodeOf ga) := by
  cases ga <;> rfl

/-- The per-receipt body of `StorageExecution.processLocals`' fold, verbatim. -/
def localsBody (fl : Flags) (hooks : NearCfg) (env : Env) (decode : Bytes → Except String Rcpt)
    (rs : RS) (r : Rcpt) : M RS := do
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then logged (delayPushL rs r)
    else
      modifyPipe (Pipeline.stepList decode rs.o)
      processWithInstant fl hooks env rs r

/-- The per-receipt body of `StorageExecution.processIncoming`' fold, verbatim. -/
def incomingBody (fl : Flags) (hooks : NearCfg) (env : Env) (decode : Bytes → Except String Rcpt)
    (rs : RS) (r : Rcpt) : M RS := do
    if !validReceipt false r then throw (panicked "ReceiptValidationError on an incoming receipt")
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then logged (delayPushL rs r)
    else
      modifyPipe (Pipeline.stepList decode rs.o)
      processWithInstant fl hooks env rs r

/-- One iteration of `StorageExecution.processDelayedLoop`, its two exits as continuations. -/
def delayedK {β : Type} (fl : Flags) (hooks : NearCfg) (env : Env) (stop cont : RS → M β)
    (rs : RS) : M β := do
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then return ← stop rs
    let (rs, r) ← delayPopR fl.globalActions env (rs.dq.next - rs.dq.first + 1) rs
    match r with
    | none => stop rs
    | some r =>
      match (← get).pipe.next with
      | some n =>
        if n - 1 == 0 then scheduleDelayed fl.globalActions env rs
        else modifyPipe fun p => { p with next := some (n - 1) }
      | none => pure ()
      if !validReceipt false r then throw (inconsistent "Delayed receipt in the state is invalid")
      let rs ← processWithInstant fl hooks env rs r
      cont rs

/-- One iteration of `StorageExecution.yieldLoop`, its two exits as continuations. -/
def yieldK {β : Type} (ga : Bool) (env : Env) (next : Nat) (stop : RS × Nat → M β)
    (cont : RS × Nat × Nat → M β) (rs : RS) (i k : Nat) : M β := do
    if i ≥ next then return ← stop (rs, i)
    if rs.compute ≥ env.ctx.gasLimit || (← softExceeded) then return ← stop (rs, i)
    let (acct, d, exp) ← match ← getR rs.o (kYieldTimeout i) "promise yield timeout" with
      | none => throw (inconsistent "PromiseYield timeout queue entry should be in the state")
      | some b => okR (decodeYieldTimeout b) (inconsistent "promise yield timeout")
    if exp > env.ctx.height then return ← stop (rs, i)
    let (rs, k) ← if ← containsR rs.o (kYieldReceipt acct d) "promise yield receipt" then do
        let rid := receiptIdFrom d env.ctx.height k
        let rs ← forwardOrBufferR ga env rs ⟨acct, acct, rid, .data true d none⟩
        pure (rs, k + 1)
      else pure (rs, k)
    let rs := { rs with o := rs.o.remove (kYieldTimeout i) }
    cont (rs, i + 1, k)

/-- Step 7 of `applyNewChunkD2` (validate_apply_state_update), verbatim. -/
def finalizeStep (env : Env) (yf yn : Nat) (p : RS × Nat) : M MainOutD2 :=
  let ctx := env.ctx
  match p with
  | (rs, yf') => do
      -- 7. validate_apply_state_update
      let rs := if yf' != yf then { rs with o := rs.o.set kYieldIdx (encIndices yf' yn) } else rs
      let cong ← liftE (applyDelayedCongestion rs.dq rs.cong)
      let allowed := ctx.layout.shardIds.getD ((ctx.height + (ctx.layout.index ctx.own).getD 0) % ctx.layout.numShards) ctx.own
      let cong := { cong with allowedShard := allowed }
      let bw ← bandwidthRequestsR env rs
      let o := rs.o.commit
      let root ← finalizeR o
      let gasUsed ← okR (sumNat64 (rs.outcomes.map (·.o.gasBurnt))) (panicked "total gas burnt overflow")
      let burnt ← okR (add128 rs.txBurnt rs.otherBurnt) (panicked "burnt balance overflow")
      -- E9: balance_burnt = tx + other (+ slashed = 0) − subsidized (rt/mod.rs:386-403); negative ⇒ Error
      if rs.subsidized > burnt then throw "invalid: balance_burnt underflow (subsidized exceeds burnt)"
      let burnt := burnt - rs.subsidized
      let recd ← get
      pure { root, outcomes := rs.outcomes, outgoing := rs.outgoing, gasUsed, balanceBurnt := burnt,
             congestion := cong, bwRequests := bw, proposals := dedupProposals rs.proposals,
             cdRemovals := o.cdRemovals, wasmGas := rs.wasmGas,
             committed := some (sortKV o.committed), compute := some rs.compute,
             detail := if recd.observe then some recd.detail else none }

/-! ## The engine's continuations (verbatim tails of `applyNewChunkD2`) -/

def afterIncoming (fl : Flags) (env : Env) (rs : RS) : M MainOutD2 := do
  let (yf, yn) ← getIndicesR rs.o kYieldIdx "PromiseYieldIndices"
  StorageExecution.yieldLoop fl.globalActions env yn (yn - yf + 1) (rs, yf, 0) >>= finalizeStep env yf yn

def afterDelayed (fl : Flags) (hooks : NearCfg) (env : Env) (incoming : List Rcpt) (rs : RS) :
    M MainOutD2 :=
  StorageExecution.processIncoming fl hooks env rs incoming >>= afterIncoming fl env

def afterLocals (fl : Flags) (hooks : NearCfg) (env : Env) (incoming : List Rcpt) (rs : RS) :
    M MainOutD2 :=
  StorageExecution.processDelayed fl hooks env (rs.dq.next - rs.dq.first + 1) rs >>= afterDelayed fl hooks env incoming

def afterTxs (fl : Flags) (hooks : NearCfg) (env : Env) (incoming : List Rcpt) (p : RS × List Bytes) :
    M MainOutD2 :=
  match p with
  | (rs, _) =>
    let locals := rs.locals
    StorageExecution.processLocals fl hooks env { rs with locals := [] } locals >>= afterLocals fl hooks env incoming

/-! ## The engine is the composition of the slices -/

theorem applyNewChunkD2_split (fl : Flags) (hooks : NearCfg) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    StorageExecution.applyNewChunkD2 fl hooks prims env t vu lastProps incoming txs ownCong =
      preludeK fl prims env t vu lastProps ownCong fun rs =>
        txs.foldlM (processTxR env) (rs, []) >>= afterTxs fl hooks env incoming := by
  rfl

theorem processLocals_eq (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (locals : List Rcpt) :
    StorageExecution.processLocals fl hooks env rs locals =
      modifyPipe (Pipeline.startList (decodeOf fl.globalActions) rs.o · locals) >>= fun _ =>
        locals.foldlM (localsBody fl hooks env (decodeOf fl.globalActions)) rs := by
  simp only [StorageExecution.processLocals, pipeDecode_eq, pure_bind]
  rfl

theorem processIncoming_eq (fl : Flags) (hooks : NearCfg) (env : Env) (rs : RS) (incoming : List Rcpt) :
    StorageExecution.processIncoming fl hooks env rs incoming =
      modifyPipe (Pipeline.startList (decodeOf fl.globalActions) rs.o · incoming) >>= fun _ =>
        incoming.foldlM (incomingBody fl hooks env (decodeOf fl.globalActions)) rs := by
  simp only [StorageExecution.processIncoming, pipeDecode_eq, pure_bind]
  rfl

theorem processDelayedLoop_succ (fl : Flags) (hooks : NearCfg) (env : Env) (f : Nat) (rs : RS) :
    StorageExecution.processDelayedLoop fl hooks env (f + 1) rs =
      delayedK fl hooks env pure (StorageExecution.processDelayedLoop fl hooks env f) rs := by
  rw [StorageExecution.processDelayedLoop]
  rfl

theorem yieldLoop_succ (ga : Bool) (env : Env) (next f : Nat) (rs : RS) (i k : Nat) :
    StorageExecution.yieldLoop ga env next (f + 1) (rs, i, k) =
      yieldK ga env next pure (StorageExecution.yieldLoop ga env next f) rs i k := by
  rw [StorageExecution.yieldLoop]
  rfl

/-! ## Naturality of the slices in their continuations -/

/-- Walk two `do` blocks that differ only by a trailing `>>= g`: reassociate, descend under binds,
split `if`/`match` together. -/
syntax "nat_walk" : tactic
macro_rules
  | `(tactic| nat_walk) => `(tactic| (
      try simp only [bind_assoc]
      first
        | (with_reducible rfl)
        | (refine congrArg (_ >>= ·) (funext fun _ => ?_); nat_walk)
        | (split <;> nat_walk)
        | (simp only [pure_bind]; nat_walk)
        | skip))

theorem preludeK_nat {β γ : Type} (fl : Flags) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat)) (ownCong : Congestion)
    (k : RS → M β) (g : β → M γ) :
    preludeK fl prims env t vu lastProps ownCong k >>= g =
      preludeK fl prims env t vu lastProps ownCong (fun rs => k rs >>= g) := by
  unfold preludeK
  nat_walk

theorem delayedK_nat {β γ : Type} (fl : Flags) (hooks : NearCfg) (env : Env)
    (stop cont : RS → M β) (g : β → M γ) (rs : RS) :
    delayedK fl hooks env stop cont rs >>= g =
      delayedK fl hooks env (fun x => stop x >>= g) (fun x => cont x >>= g) rs := by
  unfold delayedK
  nat_walk

theorem yieldK_nat {β γ : Type} (ga : Bool) (env : Env) (next : Nat)
    (stop : RS × Nat → M β) (cont : RS × Nat × Nat → M β) (g : β → M γ) (rs : RS) (i k : Nat) :
    yieldK ga env next stop cont rs i k >>= g =
      yieldK ga env next (fun x => stop x >>= g) (fun x => cont x >>= g) rs i k := by
  unfold yieldK
  nat_walk

/-! ## The machine -/

/-- The engine's denotation of a position: what the engine computes from there to its result.
Every clause is the original engine's own remainder (no step function appears here). -/
def den (P : Prog) : EPos → M MainOutD2
  | .start =>
    StorageExecution.applyNewChunkD2 P.fl P.hooks P.prims P.env P.t P.vu P.props P.incoming P.txs P.cong
      >>= raceCheck
  | .txs rest acc rs =>
    (rest.foldlM (processTxR P.env) (rs, acc) >>= afterTxs P.fl P.hooks P.env P.incoming) >>= raceCheck
  | .locals rest rs =>
    (rest.foldlM (localsBody P.fl P.hooks P.env (decodeOf P.fl.globalActions)) rs
      >>= afterLocals P.fl P.hooks P.env P.incoming) >>= raceCheck
  | .delayed fuel rs =>
    (StorageExecution.processDelayedLoop P.fl P.hooks P.env fuel rs
      >>= afterDelayed P.fl P.hooks P.env P.incoming) >>= raceCheck
  | .incoming rest rs =>
    (rest.foldlM (incomingBody P.fl P.hooks P.env (decodeOf P.fl.globalActions)) rs
      >>= afterIncoming P.fl P.env) >>= raceCheck
  | .yields yf yn fuel i k rs =>
    (StorageExecution.yieldLoop P.fl.globalActions P.env yn fuel (rs, i, k) >>= finalizeStep P.env yf yn)
      >>= raceCheck
  | .done out => pure out

/-- **One step of the engine machine.** Each clause runs one verbatim slice and returns the next
position. -/
def stepM (P : Prog) : EPos → M EPos
  | .start => preludeK P.fl P.prims P.env P.t P.vu P.props P.cong fun rs => pure (.txs P.txs [] rs)
  | .txs (x :: rest) acc rs => processTxR P.env (rs, acc) x >>= fun p => pure (.txs rest p.2 p.1)
  | .txs [] _ rs =>
    modifyPipe (Pipeline.startList (decodeOf P.fl.globalActions) { rs with locals := [] }.o · rs.locals)
      >>= fun _ => pure (.locals rs.locals { rs with locals := [] })
  | .locals (r :: rest) rs =>
    localsBody P.fl P.hooks P.env (decodeOf P.fl.globalActions) rs r >>= fun rs => pure (.locals rest rs)
  | .locals [] rs =>
    scheduleDelayed P.fl.globalActions P.env rs >>= fun _ =>
      pure (.delayed (rs.dq.next - rs.dq.first + 1) rs)
  | .delayed 0 rs =>
    modifyPipe (Pipeline.startList (decodeOf P.fl.globalActions) rs.o · P.incoming) >>= fun _ =>
      pure (.incoming P.incoming rs)
  | .delayed (f + 1) rs =>
    delayedK P.fl P.hooks P.env (fun rs => pure (.delayed 0 rs)) (fun rs => pure (.delayed f rs)) rs
  | .incoming (r :: rest) rs =>
    incomingBody P.fl P.hooks P.env (decodeOf P.fl.globalActions) rs r >>= fun rs =>
      pure (.incoming rest rs)
  | .incoming [] rs =>
    getIndicesR rs.o kYieldIdx "PromiseYieldIndices" >>= fun p =>
      pure (.yields p.1 p.2 (p.2 - p.1 + 1) p.1 0 rs)
  | .yields yf yn 0 i _ rs =>
    finalizeStep P.env yf yn (rs, i) >>= raceCheck >>= fun out => pure (.done out)
  | .yields yf yn (f + 1) i k rs =>
    yieldK P.fl.globalActions P.env yn (fun p => pure (.yields yf yn 0 p.2 0 p.1))
      (fun p => pure (.yields yf yn f p.2.1 p.2.2 p.1)) rs i k
  | .done out => pure (.done out)

/-- **The step lemma.** At every position the denotation is one step followed by the denotation of
the next position. -/
theorem den_step (P : Prog) (p : EPos) : den P p = stepM P p >>= den P := by
  cases p with
  | start =>
    simp only [den, stepM, applyNewChunkD2_split, preludeK_nat, pure_bind, bind_assoc]
  | txs rest acc rs =>
    cases rest with
    | nil =>
      simp only [den, stepM, List.foldlM_nil, pure_bind, bind_assoc, afterTxs, processLocals_eq]
    | cons x rest =>
      simp only [den, stepM, List.foldlM_cons, pure_bind, bind_assoc]
  | locals rest rs =>
    cases rest with
    | nil =>
      simp only [den, stepM, List.foldlM_nil, pure_bind, bind_assoc, afterLocals,
        StorageExecution.processDelayed]
    | cons r rest => simp only [den, stepM, List.foldlM_cons, pure_bind, bind_assoc]
  | delayed fuel rs =>
    cases fuel with
    | zero =>
      simp only [den, stepM, StorageExecution.processDelayedLoop, pure_bind, bind_assoc, afterDelayed,
        processIncoming_eq]
    | succ f =>
      simp only [den, stepM, processDelayedLoop_succ, delayedK_nat, bind_assoc]
      simp only [den, StorageExecution.processDelayedLoop.eq_1, pure_bind, bind_assoc]
  | incoming rest rs =>
    cases rest with
    | nil => simp only [den, stepM, List.foldlM_nil, pure_bind, bind_assoc, afterIncoming]
    | cons r rest => simp only [den, stepM, List.foldlM_cons, pure_bind, bind_assoc]
  | yields yf yn fuel i k rs =>
    cases fuel with
    | zero => simp only [den, stepM, StorageExecution.yieldLoop, pure_bind, bind_assoc, bind_pure]
    | succ f =>
      simp only [den, stepM, yieldLoop_succ, yieldK_nat, bind_assoc]
      simp only [den, StorageExecution.yieldLoop.eq_1, pure_bind, bind_assoc, Prod.eta]
  | done out => simp only [den, stepM, pure_bind]

/-! ## Runs -/

/-- A configuration of the engine machine: position and recorder state. -/
structure EConf where
  pos : EPos
  st : Recording

/-- One machine step from a configuration. -/
def estep (P : Prog) (c : EConf) : Except String EConf :=
  match stepM P c.pos c.st P.env with
  | .ok (p, r) => .ok ⟨p, r⟩
  | .error e => .error e

/-- The reflexive-transitive closure of `estep`. -/
inductive ESteps (P : Prog) : EConf → EConf → Prop
  | refl (c : EConf) : ESteps P c c
  | step {a b c : EConf} : estep P a = .ok b → ESteps P b c → ESteps P a c

theorem ESteps.trans {P : Prog} {a b c : EConf} (h1 : ESteps P a b) (h2 : ESteps P b c) :
    ESteps P a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

/-- Sequencing of two results of an `M` computation. -/
def bindRes {α β : Type} (x : Except String (α × Recording)) (f : α → Recording → Except String β) :
    Except String β :=
  match x with
  | .ok (a, r') => f a r'
  | .error err => .error err

theorem M.bind_run {α β : Type} (x : M α) (f : α → M β) (r : Recording) (e : Env) :
    (x >>= f) r e = bindRes (x r e) (fun a r' => f a r' e) := by
  show (x r e >>= fun p => f p.1 p.2 e) = _
  rcases x r e with err | ⟨a, r'⟩ <;> rfl

theorem den_run (P : Prog) (p : EPos) (r : Recording) :
    den P p r P.env = bindRes (stepM P p r P.env) (fun p' r' => den P p' r' P.env) := by
  rw [den_step, M.bind_run]

/-- Running a configuration that the machine drives to `done out` gives `out`. -/
theorem den_of_steps (P : Prog) {a b : EConf} (h : ESteps P a b) (out : MainOutD2)
    (hb : b.pos = .done out) : den P a.pos a.st P.env = .ok (out, b.st) := by
  induction h with
  | refl c =>
    obtain ⟨pos, rec⟩ := c
    simp only at hb
    subst hb
    rfl
  | @step a b c hs _ ih =>
    rw [den_run]
    obtain ⟨pa, ra⟩ := a
    unfold estep at hs
    simp only at hs ⊢
    split at hs
    · rename_i p' r' heq
      rw [heq]
      cases hs
      exact ih hb
    · cases hs

/-! ### Postconditions of steps -/

/-- Every successful result of `x` satisfies `Q`. -/
def Post {α : Type} (x : M α) (Q : α → Prop) : Prop :=
  ∀ r e a r', x r e = .ok (a, r') → Q a

theorem post_bind_pure {α β : Type} (x : M α) (f : α → β) (Q : β → Prop) (h : ∀ a, Q (f a)) :
    Post (x >>= fun a => pure (f a)) Q := by
  intro r e b r' hx
  rw [M.bind_run] at hx
  unfold bindRes at hx
  split at hx
  · cases hx; exact h _
  · cases hx

theorem post_pure {α : Type} (a : α) (Q : α → Prop) (h : Q a) : Post (pure a : M α) Q := by
  intro r e b r' hx
  cases hx; exact h

/-- A computation that is unchanged by every continuation which is the identity on `Q` returns only
values satisfying `Q`. -/
theorem post_of_nat {α : Type} (x : M α) (Q : α → Prop)
    (h : ∀ g : α → M α, (∀ a, Q a → g a = pure a) → x >>= g = x) : Post x Q := by
  classical
  intro r e a r' hx
  let g : α → M α := fun a => if Q a then pure a else throw ""
  have hg := h g (fun a ha => by simp only [g, ha, ite_true])
  have h2 := congrArg (fun y => y r e) hg
  simp only [M.bind_run, hx, bindRes] at h2
  by_cases hq : Q a
  · exact hq
  · simp only [g, hq, ite_false] at h2
    cases h2

theorem post_delayedK {β : Type} (fl : Flags) (hooks : NearCfg) (env : Env) (s c : RS → β)
    (rs : RS) (Q : β → Prop) (hs : ∀ x, Q (s x)) (hc : ∀ x, Q (c x)) :
    Post (delayedK fl hooks env (fun x => pure (s x)) (fun x => pure (c x)) rs) Q := by
  apply post_of_nat
  intro g hg
  rw [delayedK_nat]
  simp only [pure_bind, hg _ (hs _), hg _ (hc _)]

theorem post_yieldK {β : Type} (ga : Bool) (env : Env) (next : Nat) (s : RS × Nat → β)
    (c : RS × Nat × Nat → β) (rs : RS) (i k : Nat) (Q : β → Prop) (hs : ∀ x, Q (s x))
    (hc : ∀ x, Q (c x)) :
    Post (yieldK ga env next (fun x => pure (s x)) (fun x => pure (c x)) rs i k) Q := by
  apply post_of_nat
  intro g hg
  rw [yieldK_nat]
  simp only [pure_bind, hg _ (hs _), hg _ (hc _)]

theorem post_preludeK {β : Type} (fl : Flags) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat)) (ownCong : Congestion)
    (s : RS → β) (Q : β → Prop) (hs : ∀ x, Q (s x)) :
    Post (preludeK fl prims env t vu lastProps ownCong (fun x => pure (s x))) Q := by
  apply post_of_nat
  intro g hg
  rw [preludeK_nat]
  simp only [pure_bind, hg _ (hs _)]

/-! ### The machine always progresses -/

/-- Phase rank (`start` highest, `done` lowest). -/
def EPos.phase : EPos → Nat
  | .start => 6 | .txs .. => 5 | .locals .. => 4 | .delayed .. => 3 | .incoming .. => 2
  | .yields .. => 1 | .done _ => 0

/-- Remaining work inside the phase. -/
def EPos.work : EPos → Nat
  | .txs rest _ _ => rest.length | .locals rest _ => rest.length | .delayed f _ => f
  | .incoming rest _ => rest.length | .yields _ _ f _ _ _ => f | _ => 0

/-- `p'` is strictly below `p` in the lexicographic (phase, work) order. -/
def EPos.Below (p' p : EPos) : Prop :=
  p'.phase < p.phase ∨ (p'.phase = p.phase ∧ p'.work < p.work)

theorem step_below (P : Prog) (p : EPos) (hp : ∀ out, p ≠ .done out) :
    Post (stepM P p) (fun p' => EPos.Below p' p) := by
  have lt : ∀ a b : Nat, a < b → ∀ (p' q : EPos), p'.phase = a → q.phase = b → EPos.Below p' q :=
    fun a b h p' q ha hb => Or.inl (by rw [ha, hb]; exact h)
  cases p with
  | start =>
    simp only [stepM]
    exact post_preludeK _ _ _ _ _ _ _ _ _ (fun _ => lt 5 6 (by decide) _ _ rfl rfl)
  | txs rest acc rs =>
    cases rest with
    | nil =>
      simp only [stepM]
      exact post_bind_pure _ _ _ (fun _ => lt 4 5 (by decide) _ _ rfl rfl)
    | cons x rest =>
      simp only [stepM]
      exact post_bind_pure _ _ _ (fun _ => Or.inr ⟨rfl, by simp only [EPos.work, List.length_cons]; omega⟩)
  | locals rest rs =>
    cases rest with
    | nil =>
      simp only [stepM]
      exact post_bind_pure _ _ _ (fun _ => lt 3 4 (by decide) _ _ rfl rfl)
    | cons x rest =>
      simp only [stepM]
      exact post_bind_pure _ _ _ (fun _ => Or.inr ⟨rfl, by simp only [EPos.work, List.length_cons]; omega⟩)
  | delayed f rs =>
    cases f with
    | zero =>
      simp only [stepM]
      exact post_bind_pure _ _ _ (fun _ => lt 2 3 (by decide) _ _ rfl rfl)
    | succ f =>
      simp only [stepM]
      exact post_delayedK _ _ _ _ _ _ _ (fun _ => Or.inr ⟨rfl, by simp only [EPos.work]; omega⟩)
        (fun _ => Or.inr ⟨rfl, by simp only [EPos.work]; omega⟩)
  | incoming rest rs =>
    cases rest with
    | nil =>
      simp only [stepM]
      exact post_bind_pure _ _ _ (fun _ => lt 1 2 (by decide) _ _ rfl rfl)
    | cons x rest =>
      simp only [stepM]
      exact post_bind_pure _ _ _ (fun _ => Or.inr ⟨rfl, by simp only [EPos.work, List.length_cons]; omega⟩)
  | yields yf yn f i k rs =>
    cases f with
    | zero =>
      simp only [stepM]
      exact post_bind_pure _ _ _ (fun _ => lt 0 1 (by decide) _ _ rfl rfl)
    | succ f =>
      simp only [stepM]
      exact post_yieldK _ _ _ _ _ _ _ _ _ (fun _ => Or.inr ⟨rfl, by simp only [EPos.work]; omega⟩)
        (fun _ => Or.inr ⟨rfl, by simp only [EPos.work]; omega⟩)
  | done out => exact absurd rfl (hp out)

/-- A successful denotation is a run of the machine to `done`. -/
theorem steps_of_den (P : Prog) (p : EPos) (r r' : Recording) (out : MainOutD2)
    (h : den P p r P.env = .ok (out, r')) : ESteps P ⟨p, r⟩ ⟨.done out, r'⟩ := by
  by_cases hd : ∃ o, p = .done o
  · obtain ⟨o, rfl⟩ := hd
    simp only [den] at h
    cases h
    exact .refl _
  · have hp : ∀ o, p ≠ .done o := fun o he => hd ⟨o, he⟩
    rw [den_run] at h
    unfold bindRes at h
    split at h
    · rename_i p' r1 hs
      have hb := step_below P p hp r P.env p' r1 hs
      have ih := steps_of_den P p' r1 r' out h
      exact .step (by unfold estep; rw [hs]) ih
    · cases h
termination_by (p.phase, p.work)
decreasing_by
  rcases hb with h1 | ⟨h1, h2⟩
  · exact Prod.Lex.left _ _ h1
  · rw [h1]; exact Prod.Lex.right _ h2

/-- **The engine machine is the engine.** -/
theorem den_ok_iff (P : Prog) (p : EPos) (r r' : Recording) (out : MainOutD2) :
    den P p r P.env = .ok (out, r') ↔ ESteps P ⟨p, r⟩ ⟨.done out, r'⟩ :=
  ⟨steps_of_den P p r r' out, fun h => den_of_steps P h out rfl⟩

/-- The program of a `StorageExecution.run` call. -/
def Prog.ofRun (cfg : NearCfg) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (congestion : Congestion) (globalActions : Bool)
    (codePolicy : CodeWitnessPolicy) : Prog :=
  { fl := { globalActions, codePolicy }, hooks := cfg, prims, env, t, vu, props, incoming, txs,
    cong := congestion }

/-- The recorder state `StorageExecution.run` starts from. -/
def initRec (cfg : NearCfg) (env : Env) : Recording :=
  { observe := cfg.observeDetail, pipe := { chain := env.chainId } }

/-- **`StorageExecution.run` accepts with `out` iff the engine machine, started at `start` from
the run's initial recorder state, reaches `done out`.** -/
theorem engine_run_ok_iff (cfg : NearCfg) (prims : Prims) (env : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (congestion : Congestion) (ga : Bool) (cp : CodeWitnessPolicy)
    (out : MainOutD2) :
    StorageExecution.run cfg prims env t vu props incoming txs congestion ga cp = .ok out ↔
      ∃ r', ESteps (Prog.ofRun cfg prims env t vu props incoming txs congestion ga cp)
        ⟨.start, initRec cfg env⟩ ⟨.done out, r'⟩ := by
  have hden : ∀ r', (den (Prog.ofRun cfg prims env t vu props incoming txs congestion ga cp) .start
      (initRec cfg env) env = .ok (out, r')) ↔
      ESteps (Prog.ofRun cfg prims env t vu props incoming txs congestion ga cp)
        ⟨.start, initRec cfg env⟩ ⟨.done out, r'⟩ :=
    fun r' => den_ok_iff _ _ _ _ _
  unfold StorageExecution.run
  simp only [← hden]
  show ((den (Prog.ofRun cfg prims env t vu props incoming txs congestion ga cp) .start
      (initRec cfg env) env).map Prod.fst = .ok out) ↔ _
  rcases den (Prog.ofRun cfg prims env t vu props incoming txs congestion ga cp) .start
      (initRec cfg env) env with e | ⟨o, r⟩
  · simp [Except.map]
  · simp only [Except.map, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h; exact ⟨r, h, rfl⟩
    · rintro ⟨r', h, -⟩; exact h

#print axioms den_step
#print axioms engine_run_ok_iff
end NearSpecV3.E2E
