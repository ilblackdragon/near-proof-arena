import NearSpecV3.ChunkValidationD2

/-!
# The D2 runtime reads `Env.store` only through the `FunctionCall` hook

`Env.store` (the merged recorded storage `w.main.values ++ codes`, E2) is consulted only by
`Env.codeOf`, which only the `FunctionCall` hook calls. So for any hooks `H` that give equal
results for two stores `s1`, `s2` (`HookCong H s1 s2`), `applyNewChunkD2 H` gives equal results
(`applyNewChunkD2_store`). `StoreCongD3.lean` proves `HookCong` for `d3Hooks` whenever the two
stores answer every lookup alike (`hGet s1 = hGet s2`).
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

/-- The hooks give equal results under the two stores. -/
def HookCong (H : ActionHooks) (E : Env) (s1 s2 : HStore) : Prop :=
  ∀ (r : Rcpt) (a : ActionR) (i n : Nat) (inputs : List (Option Bytes)) (deployed attempted : List Bytes)
    (st : ActSt) (ar : AR) (b : Base),
    H.functionCall ⟨{ E with store := s1 }, r, a, i, n, inputs, deployed, attempted⟩ st ar b =
    H.functionCall ⟨{ E with store := s2 }, r, a, i, n, inputs, deployed, attempted⟩ st ar b

variable (H : ActionHooks) (E : Env) (s1 s2 : HStore) (hH : HookCong H E s1 s2)
include hH

theorem applyAction_store (r : Rcpt) (a : ActionR) (i n : Nat) (inputs : List (Option Bytes))
    (deployed attempted : List Bytes) (st : ActSt) (act : Act) :
    applyAction H ⟨{ E with store := s1 }, r, a, i, n, inputs, deployed, attempted⟩ st act =
    applyAction H ⟨{ E with store := s2 }, r, a, i, n, inputs, deployed, attempted⟩ st act := by
  unfold applyAction
  cases act with
  | delegate _ d => rfl
  | base x =>
    obtain ⟨_, b⟩ := x
    cases b <;> first | rfl | (unfold HookCong at hH; simp only [hH])

theorem actionLoop_store (r : Rcpt) (a : ActionR) (inputs : List (Option Bytes))
    (deployed attempted : List Bytes) :
    ∀ (i : Nat) (acts : List Act) (acc : ActSt × AR),
    actionLoop H { E with store := s1 } r a inputs deployed attempted i acts acc =
    actionLoop H { E with store := s2 } r a inputs deployed attempted i acts acc
  | _, [], _ => rfl
  | i, act :: rest, (st, res) => by
    rw [actionLoop, actionLoop]
    simp only [applyAction_store H E s1 s2 hH, actionLoop_store r a inputs deployed attempted (i + 1) rest]

theorem forwardOrBuffer_store (rs : RS) (r : Rcpt) :
    forwardOrBuffer { E with store := s1 } rs r = forwardOrBuffer { E with store := s2 } rs r := rfl

theorem emitReceipts_store (p : Bytes) : ∀ rs k l,
    emitReceipts { E with store := s1 } p rs k l = emitReceipts { E with store := s2 } p rs k l
  | _, _, [] => rfl
  | rs, k, nr :: rest => by
    rw [emitReceipts, emitReceipts]
    simp only [emitReceipts_store p _ _ rest, forwardOrBuffer_store H E s1 s2 hH]

theorem applyActionReceipt_store (rs : RS) (r : Rcpt) (a : ActionR) :
    applyActionReceipt H { E with store := s1 } rs r a =
    applyActionReceipt H { E with store := s2 } rs r a := by
  unfold applyActionReceipt
  simp only [actionLoop_store H E s1 s2 hH, emitReceipts_store H E s1 s2 hH]

theorem processReceipt_store (rs : RS) (r : Rcpt) :
    processReceipt H { E with store := s1 } rs r = processReceipt H { E with store := s2 } rs r := by
  unfold processReceipt
  simp only [applyActionReceipt_store H E s1 s2 hH]

theorem processWithTotals_store (rs : RS) (r : Rcpt) :
    processWithTotals H { E with store := s1 } rs r =
    processWithTotals H { E with store := s2 } rs r := by
  unfold processWithTotals
  simp only [processReceipt_store H E s1 s2 hH]

theorem drain_store : ∀ (fuel : Nat) (rs : RS),
    processWithInstant.drain H { E with store := s1 } fuel rs =
    processWithInstant.drain H { E with store := s2 } fuel rs
  | 0, _ => rfl
  | fuel + 1, rs => by
    rw [processWithInstant.drain, processWithInstant.drain]
    simp only [processWithTotals_store H E s1 s2 hH, drain_store fuel]

theorem processWithInstant_store (rs : RS) (r : Rcpt) :
    processWithInstant H { E with store := s1 } rs r =
    processWithInstant H { E with store := s2 } rs r := by
  unfold processWithInstant
  simp only [processWithTotals_store H E s1 s2 hH, drain_store H E s1 s2 hH]

theorem fwdLoop_store (s : Nat) : ∀ f i x,
    fwdLoop { E with store := s1 } s f i x = fwdLoop { E with store := s2 } s f i x
  | 0, _, _ => rfl
  | f + 1, i, (rs, k, pops) => by
    rw [fwdLoop, fwdLoop]
    simp only [fwdLoop_store s f]

theorem forwardFromBuffer_store (rs : RS) :
    forwardFromBuffer { E with store := s1 } rs = forwardFromBuffer { E with store := s2 } rs := by
  unfold forwardFromBuffer forwardFromBufferToShard
  simp only [fwdLoop_store H E s1 s2 hH]

theorem processTxD2_store (x : RS × List Bytes) (tf : TxD2 × Bool) :
    processTxD2 { E with store := s1 } x tf = processTxD2 { E with store := s2 } x tf := by
  unfold processTxD2
  simp only [forwardOrBuffer_store H E s1 s2 hH]

theorem processTxD2_store' :
    processTxD2 { E with store := s1 } = processTxD2 { E with store := s2 } := by
  funext x tf; exact processTxD2_store H E s1 s2 hH x tf

theorem processLocals_store (rs : RS) (l : List Rcpt) :
    processLocals H { E with store := s1 } rs l = processLocals H { E with store := s2 } rs l := by
  unfold processLocals
  simp only [processWithInstant_store H E s1 s2 hH]

theorem delayPop_store : ∀ (f : Nat) (rs : RS),
    delayPop { E with store := s1 } f rs = delayPop { E with store := s2 } f rs
  | 0, _ => rfl
  | f + 1, rs => by
    rw [delayPop, delayPop]
    simp only [delayPop_store f]

theorem processDelayed_store : ∀ (f : Nat) (rs : RS),
    processDelayed H { E with store := s1 } f rs = processDelayed H { E with store := s2 } f rs
  | 0, _ => rfl
  | f + 1, rs => by
    rw [processDelayed, processDelayed]
    simp only [delayPop_store H E s1 s2 hH, processWithInstant_store H E s1 s2 hH, processDelayed_store f]

theorem processIncoming_store (rs : RS) (l : List Rcpt) :
    processIncoming H { E with store := s1 } rs l =
    processIncoming H { E with store := s2 } rs l := by
  unfold processIncoming
  simp only [processWithInstant_store H E s1 s2 hH]

theorem yieldLoop_store (next : Nat) : ∀ (f : Nat) (x : RS × Nat × Nat),
    yieldLoop { E with store := s1 } next f x = yieldLoop { E with store := s2 } next f x
  | 0, (_, _, _) => rfl
  | f + 1, (rs, i, k) => by
    rw [yieldLoop, yieldLoop]
    simp only [forwardOrBuffer_store H E s1 s2 hH, yieldLoop_store next f]

theorem bandwidthRequests_store (rs : RS) :
    bandwidthRequests { E with store := s1 } rs = bandwidthRequests { E with store := s2 } rs := rfl

/-- **The D2 main transition does not depend on `Env.store`.** -/
theorem applyNewChunkD2_store (prims : Prims) (t : PTrie) (vu : Option ValidatorUpdateFacts)
    (lastProps : List (Bytes × Nat)) (incoming : List Rcpt) (txs : List (TxD2 × Bool))
    (ownCong : Congestion) :
    applyNewChunkD2 H prims { E with store := s1 } t vu lastProps incoming txs ownCong =
    applyNewChunkD2 H prims { E with store := s2 } t vu lastProps incoming txs ownCong := by
  unfold applyNewChunkD2
  simp only [forwardFromBuffer_store H E s1 s2 hH, processTxD2_store' H E s1 s2 hH, processLocals_store H E s1 s2 hH,
    processDelayed_store H E s1 s2 hH, processIncoming_store H E s1 s2 hH, yieldLoop_store H E s1 s2 hH,
    bandwidthRequests_store H E s1 s2 hH]

end ReexecV3D3
