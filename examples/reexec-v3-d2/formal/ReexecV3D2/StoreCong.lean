import NearSpecV3.ChunkValidationD2

/-!
# The D2 runtime never reads `Env.store`

`Env.store` (the merged recorded storage `w.main.values ++ codes`, E2) is consulted only by
`Env.codeOf`, which only the D3 `FunctionCall` hook calls (`codeAvailable`); with `d2Hooks` a
`FunctionCall` is out of domain before any lookup. So `applyNewChunkD2 d2Hooks` gives the
same result for any two stores (`applyNewChunkD2_store`); this is what lets the normal form
drop the recorded values the relation never looks up.
-/

namespace ReexecV3D2

open NearSpec NearSpecV3 NearSpecV3.D2

variable (E : Env) (s1 s2 : HStore)

theorem applyAction_store (r : Rcpt) (a : ActionR) (i n : Nat) (inputs : List (Option Bytes))
    (deployed attempted : List Bytes) (st : ActSt) (act : Act) :
    applyAction d2Hooks ⟨{ E with store := s1 }, r, a, i, n, inputs, deployed, attempted⟩ st act =
    applyAction d2Hooks ⟨{ E with store := s2 }, r, a, i, n, inputs, deployed, attempted⟩ st act := by
  rfl

theorem actionLoop_store (r : Rcpt) (a : ActionR) (inputs : List (Option Bytes))
    (deployed attempted : List Bytes) :
    ∀ (i : Nat) (acts : List Act) (acc : ActSt × AR),
    actionLoop d2Hooks { E with store := s1 } r a inputs deployed attempted i acts acc =
    actionLoop d2Hooks { E with store := s2 } r a inputs deployed attempted i acts acc
  | _, [], _ => rfl
  | i, act :: rest, (st, res) => by
    rw [actionLoop, actionLoop]
    simp only [applyAction_store E s1 s2, actionLoop_store r a inputs deployed attempted (i + 1) rest]

theorem forwardOrBuffer_store (rs : RS) (r : Rcpt) :
    forwardOrBuffer { E with store := s1 } rs r = forwardOrBuffer { E with store := s2 } rs r := rfl

theorem emitReceipts_store (p : Bytes) : ∀ rs k l,
    emitReceipts { E with store := s1 } p rs k l = emitReceipts { E with store := s2 } p rs k l
  | _, _, [] => rfl
  | rs, k, nr :: rest => by
    rw [emitReceipts, emitReceipts]
    simp only [emitReceipts_store p _ _ rest, forwardOrBuffer_store E s1 s2]

theorem applyActionReceipt_store (rs : RS) (r : Rcpt) (a : ActionR) :
    applyActionReceipt d2Hooks { E with store := s1 } rs r a =
    applyActionReceipt d2Hooks { E with store := s2 } rs r a := by
  unfold applyActionReceipt
  simp only [actionLoop_store E s1 s2, emitReceipts_store E s1 s2]

theorem processReceipt_store (rs : RS) (r : Rcpt) :
    processReceipt d2Hooks { E with store := s1 } rs r = processReceipt d2Hooks { E with store := s2 } rs r := by
  unfold processReceipt
  simp only [applyActionReceipt_store E s1 s2]

theorem processWithTotals_store (rs : RS) (r : Rcpt) :
    processWithTotals d2Hooks { E with store := s1 } rs r =
    processWithTotals d2Hooks { E with store := s2 } rs r := by
  unfold processWithTotals
  simp only [processReceipt_store E s1 s2]

theorem drain_store : ∀ (fuel : Nat) (rs : RS),
    processWithInstant.drain d2Hooks { E with store := s1 } fuel rs =
    processWithInstant.drain d2Hooks { E with store := s2 } fuel rs
  | 0, _ => rfl
  | fuel + 1, rs => by
    rw [processWithInstant.drain, processWithInstant.drain]
    simp only [processWithTotals_store E s1 s2, drain_store fuel]

theorem processWithInstant_store (rs : RS) (r : Rcpt) :
    processWithInstant d2Hooks { E with store := s1 } rs r =
    processWithInstant d2Hooks { E with store := s2 } rs r := by
  unfold processWithInstant
  simp only [processWithTotals_store E s1 s2, drain_store E s1 s2]

theorem fwdLoop_store (s : Nat) : ∀ f i x,
    fwdLoop { E with store := s1 } s f i x = fwdLoop { E with store := s2 } s f i x
  | 0, _, _ => rfl
  | f + 1, i, (rs, k, pops) => by
    rw [fwdLoop, fwdLoop]
    simp only [fwdLoop_store s f]

theorem forwardFromBuffer_store (rs : RS) :
    forwardFromBuffer { E with store := s1 } rs = forwardFromBuffer { E with store := s2 } rs := by
  unfold forwardFromBuffer forwardFromBufferToShard
  simp only [fwdLoop_store E s1 s2]

theorem processTxD2_store (x : RS × List Bytes) (tf : TxD2 × Bool) :
    processTxD2 { E with store := s1 } x tf = processTxD2 { E with store := s2 } x tf := by
  unfold processTxD2
  simp only [forwardOrBuffer_store E s1 s2]

theorem processTxD2_store' :
    processTxD2 { E with store := s1 } = processTxD2 { E with store := s2 } := by
  funext x tf; exact processTxD2_store E s1 s2 x tf

theorem processLocals_store (rs : RS) (l : List Rcpt) :
    processLocals d2Hooks { E with store := s1 } rs l = processLocals d2Hooks { E with store := s2 } rs l := by
  unfold processLocals
  simp only [processWithInstant_store E s1 s2]

theorem delayPop_store : ∀ (f : Nat) (rs : RS),
    delayPop { E with store := s1 } f rs = delayPop { E with store := s2 } f rs
  | 0, _ => rfl
  | f + 1, rs => by
    rw [delayPop, delayPop]
    simp only [delayPop_store f]

theorem processDelayed_store : ∀ (f : Nat) (rs : RS),
    processDelayed d2Hooks { E with store := s1 } f rs = processDelayed d2Hooks { E with store := s2 } f rs
  | 0, _ => rfl
  | f + 1, rs => by
    rw [processDelayed, processDelayed]
    simp only [delayPop_store E s1 s2, processWithInstant_store E s1 s2, processDelayed_store f]

theorem processIncoming_store (rs : RS) (l : List Rcpt) :
    processIncoming d2Hooks { E with store := s1 } rs l =
    processIncoming d2Hooks { E with store := s2 } rs l := by
  unfold processIncoming
  simp only [processWithInstant_store E s1 s2]

theorem yieldLoop_store (next : Nat) : ∀ (f : Nat) (x : RS × Nat × Nat),
    yieldLoop { E with store := s1 } next f x = yieldLoop { E with store := s2 } next f x
  | 0, (_, _, _) => rfl
  | f + 1, (rs, i, k) => by
    rw [yieldLoop, yieldLoop]
    simp only [forwardOrBuffer_store E s1 s2, yieldLoop_store next f]

theorem bandwidthRequests_store (rs : RS) :
    bandwidthRequests { E with store := s1 } rs = bandwidthRequests { E with store := s2 } rs := rfl

/-- **The D2 main transition does not depend on `Env.store`.** -/
theorem applyNewChunkD2_store (prims : Prims) (t : PTrie) (vu : Option ValidatorUpdateFacts)
    (lastProps : List (Bytes × Nat)) (incoming : List Rcpt) (txs : List (TxD2 × Bool))
    (ownCong : Congestion) :
    applyNewChunkD2 d2Hooks prims { E with store := s1 } t vu lastProps incoming txs ownCong =
    applyNewChunkD2 d2Hooks prims { E with store := s2 } t vu lastProps incoming txs ownCong := by
  unfold applyNewChunkD2
  simp only [forwardFromBuffer_store E s1 s2, processTxD2_store' E s1 s2, processLocals_store E s1 s2,
    processDelayed_store E s1 s2, processIncoming_store E s1 s2, yieldLoop_store E s1 s2,
    bandwidthRequests_store E s1 s2]

end ReexecV3D2
