import NearSpecV3.ChunkValidationD1

/-! # `Runtime.EmptyTxs`

`applyNewChunkD1 prims ctx t receipts []`: D1 with an empty transaction list.  D1 and D0 differ in
the receipt phase only in how the compute is tracked: D0 counts receipts (`i`, incremented by `1`,
charged `i * Params.G`), while D1 carries an accumulator `comp` incremented by `Params.G`.  Both
are otherwise textually identical, so they agree whenever `comp = i * Params.G`.

This file proves that, then specialises it: with no transactions,
* `processTxs ctx st [] = .ok st` (definitional),
* the local-receipt phase runs on `st.locals = []` and is the identity,
* the incoming-receipt phase starts at `comp = 0 = 0 * Params.G`,
* `st.outs = st.fwd = st.locals = []`, so the D1 output decoration is vacuous.

The main statement is `Work.Runtime.EmptyTxs`.
-/

set_option maxRecDepth 100000

namespace Work.Runtime

open NearSpec NearSpecV3 NearSpec.TransferV1

namespace EmptyTxs

/-! ## Generic `Except` lemmas -/

theorem bind_ok_ {α β : Type} (a : α) (f : α → Except String β) : (Except.ok a >>= f) = f a := rfl

theorem map_bnd {α β γ : Type} (g : β → γ) (x : Except String α) (f : α → Except String β) :
    (x >>= f).map g = x >>= fun a => (f a).map g := by cases x <;> rfl

theorem bnd_map {α β γ : Type} (g : β → γ) (m : Except String α)
    (F : α → Except String γ) (G : α → Except String β) (h : ∀ a, F a = (G a).map g) :
    (m >>= F) = (m >>= G).map g := by
  cases m with
  | error e => rfl
  | ok a => exact h a

theorem bnd_congr {α β γ : Type} (m : Except String α) (F : α → Except String γ)
    (G : α → Except String β) (g : β → γ) (h : ∀ a, F a = (G a).map g) :
    (m >>= F) = m >>= fun a => (G a).map g := by
  cases m with
  | error e => rfl
  | ok a => exact h a

/-- `Except.map` on the left of a bind: the result of `N.map φ` is fed to `H`. -/
theorem map_bind_congr {α β γ : Type} (N : Except String α) (φ : α → β)
    (H : β → Except String γ) : (N.map φ) >>= H = N >>= fun a => H (φ a) := by
  cases N with
  | error e => rfl
  | ok a => rfl

/-! ## The sub-lemmas

`applReceipts_nil` / `applReceiptsC_nil` are the `rfl` base cases; `receiptsCore` is the induction
over the receipt list showing that D0 with the counter `i` and D1 with the compute accumulator
`comp = i * Params.G` do exactly the same thing, D1 additionally returning the final compute
`(i + rs.length) * Params.G`. -/

theorem applReceipts_nil (ctx : ApplyCtx) (i : Nat) (st : Acc × List Limit) :
    applyReceipts ctx i st [] = .ok st := rfl

theorem applReceiptsC_nil (ctx : ApplyCtx) (comp : Nat) (acc : Acc) (ls : List Limit) :
    applyReceiptsC ctx comp (acc, ls) [] = .ok (acc, ls, comp) := rfl

/-- D0 at counter `i` and D1 with compute `i * Params.G` agree, D1 returning the final compute. -/
theorem receiptsCore (ctx : ApplyCtx) (rs : List Receipt) :
    ∀ (i : Nat) (acc : Acc) (ls : List Limit),
      applyReceiptsC ctx (i * Params.G) (acc, ls) rs =
        (applyReceipts ctx i (acc, ls) rs).map
          (fun p => (p.1, p.2, (i + rs.length) * Params.G)) := by
  induction rs with
  | nil => intro i acc ls; rfl
  | cons r rs ih =>
    intro i acc ls
    have harith : i * Params.G + Params.G = (i + 1) * Params.G := (Nat.succ_mul i Params.G).symm
    have hlen : i + (r :: rs).length = (i + 1) + rs.length := by
      rw [List.length_cons]; omega
    rw [applyReceiptsC.eq_2, applyReceipts.eq_2, harith, hlen]
    by_cases hg : i * Params.G ≥ ctx.gasLimit
    · rw [if_pos hg, if_pos hg]; rfl
    · rw [if_neg hg, if_neg hg]
      by_cases hsys : (r.predecessorId == AccountId.system) = true
      · rw [if_pos hsys, if_pos hsys]
        show (applySystemReceipt acc r >>= fun a => applyReceiptsC ctx ((i + 1) * Params.G)
            (a, ls) rs) =
          Except.map (fun p : Acc × List Limit => (p.1, p.2, ((i + 1) + rs.length) * Params.G))
            (applySystemReceipt acc r >>= fun a => applyReceipts ctx (i + 1) (a, ls) rs)
        rw [map_bnd]; exact bnd_congr _ _ _ _ (fun a => ih (i + 1) a ls)
      · rw [if_neg hsys, if_neg hsys]
        cases hM : applyReceipt { blockHeight := ctx.height, blockGasPrice := ctx.gasPrice } acc r with
        | none =>
          cases hF : acc.trie.find (accountKeyPath r.receiverId) with
          | none => rfl
          | some v => rfl
        | some acc' =>
          show (List.foldlM (fun (ls : List Limit) (rf : Receipt) =>
              match tryForward ctx ls rf with
              | some ls' => Except.ok ls'
              | none => Except.error "out of domain (e.forwarded): generated receipt buffered")
              ls (acc'.refunds.drop acc.refunds.length)
            >>= fun l => applyReceiptsC ctx ((i + 1) * Params.G) (acc', l) rs) =
          Except.map (fun p : Acc × List Limit => (p.1, p.2, ((i + 1) + rs.length) * Params.G))
            (List.foldlM (fun (ls : List Limit) (rf : Receipt) =>
              match tryForward ctx ls rf with
              | some ls' => Except.ok ls'
              | none => Except.error "out of domain (e.forwarded): generated receipt buffered")
              ls (acc'.refunds.drop acc.refunds.length)
            >>= fun l => applyReceipts ctx (i + 1) (acc', l) rs)
          rw [map_bnd]; exact bnd_congr _ _ _ _ (fun l => ih (i + 1) acc' l)

/-- `receiptsCore` at `i = 0`; the compute D1 returns is `rs.length * Params.G`. -/
theorem receiptsCore_zero (ctx : ApplyCtx) (rs : List Receipt) (acc : Acc) (ls : List Limit) :
    applyReceiptsC ctx 0 (acc, ls) rs =
      (applyReceipts ctx 0 (acc, ls) rs).map (fun p => (p.1, p.2, rs.length * Params.G)) := by
  simpa using receiptsCore ctx rs 0 acc ls

/-! ## The common prefix of `applyNewChunk` / `applyNewChunkD1` -/

/-- The steps both D0 and D1 run before looking at the receipts. -/
def pre (prims : Prims) (ctx : ApplyCtx) (t : PTrie) : Except String (PTrie × List Limit) := do
  queueEmpty (← readKey t keyDelayedIdx "DelayedReceiptIndices") "delayed receipt queue"
  let (t, so) ← schedStep prims ctx t
  let shards ← bufferedShards (← readKey t keyBufferedIdx "BufferedReceiptIndices")
  for s in shards do
    let _ ← readKey t (keyGroupsData s) "BufferedReceiptGroupsQueueData"
  let limits : List Limit := ctx.statuses.map fun (s, ci, missed) =>
    ⟨s, (if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own), so.grant ctx.own s⟩
  pure (t, limits)

/-- The common consumer of `applyReceipts ... receipts`: the yield-queue check and the D0 output. -/
def consumers (ctx : ApplyCtx) (acc : Acc) (ls : List Limit) : Except String MainOut := do
  queueEmpty (← readKey acc.trie keyYieldIdx "PromiseYieldIndices") "promise yield queue"
  pure ⟨acc.trie, acc.outcomes, acc.refunds, acc.gasBurnt, acc.tokensBurnt⟩

/-- The decoration turning a D0 output into a D1 output (no transactions: no statuses, no local
ids, no extra outcomes or outgoing receipts). -/
def decOut (x : MainOut) : MainOutD1 :=
  { trie := x.trie, outcomes := x.outcomes.map (fun o => { o := o, status := OStatus.value }),
    outgoing := x.outgoing, gasUsed := x.gasUsed, tokensBurnt := x.tokensBurnt, localIds := [] }

/-- The D0 consumer, decorated: the last `do` block of D1. -/
def consumersDec (ctx : ApplyCtx) (acc : Acc) (ls : List Limit) : Except String MainOutD1 := do
  queueEmpty (← readKey acc.trie keyYieldIdx "PromiseYieldIndices") "promise yield queue"
  pure (decOut ⟨acc.trie, acc.outcomes, acc.refunds, acc.gasBurnt, acc.tokensBurnt⟩)

/-- D0's tail: incoming receipts from `i = 0`, then the yield-queue check. -/
def suffixD0 (ctx : ApplyCtx) (p : PTrie × List Limit) (receipts : List Receipt) :
    Except String MainOut := do
  let (acc, _) ← applyReceipts ctx 0 (⟨p.1, [], [], 0, 0⟩, p.2) receipts
  queueEmpty (← readKey acc.trie keyYieldIdx "PromiseYieldIndices") "promise yield queue"
  pure ⟨acc.trie, acc.outcomes, acc.refunds, acc.gasBurnt, acc.tokensBurnt⟩

/-- D1's tail with no transactions: `processTxs` is the identity on `[]` and the local-receipt phase
is on `st.locals = []`, so the two `applyReceiptsC` calls collapse into one with `comp = 0`. -/
def suffixD1 (ctx : ApplyCtx) (p : PTrie × List Limit) (receipts : List Receipt) :
    Except String MainOutD1 := do
  let st ← processTxs ctx ⟨p.1, [], [], [], [], p.2, 0, 0⟩ []
  if st.locals.any (fun r => !AccountId.isNamed r.receiverId) then
    throw "out of domain (r.shape): local receipt to a non-named account"
  let (acc, ls, comp) ← applyReceiptsC ctx st.gas (⟨st.trie, [], [], st.gas, st.tokens⟩, st.ls) st.locals
  let (acc, _, _) ← applyReceiptsC ctx comp (acc, ls) receipts
  queueEmpty (← readKey acc.trie keyYieldIdx "PromiseYieldIndices") "promise yield queue"
  pure ⟨acc.trie, st.outs ++ acc.outcomes.map (fun o => { o := o, status := OStatus.value }),
        st.fwd ++ acc.refunds, acc.gasBurnt, acc.tokensBurnt, st.locals.map Receipt.receiptId⟩

theorem applyNewChunk_eq_pre (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (receipts : List Receipt) :
    applyNewChunk prims ctx t receipts = pre prims ctx t >>= (fun p => suffixD0 ctx p receipts) := by
  unfold applyNewChunk pre suffixD0
  simp only [bind_assoc, pure_bind]

theorem applyNewChunkD1_eq_pre (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (receipts : List Receipt) :
    applyNewChunkD1 prims ctx t receipts [] = pre prims ctx t >>= (fun p => suffixD1 ctx p receipts) := by
  unfold applyNewChunkD1 pre suffixD1
  simp only [bind_assoc, pure_bind]

theorem consumersDec_eq (ctx : ApplyCtx) (acc : Acc) (ls : List Limit) :
    consumersDec ctx acc ls = (consumers ctx acc ls).map decOut := by
  unfold consumersDec consumers decOut
  rw [map_bnd]
  refine bnd_congr _ _ _ _ (fun v => ?_)
  rw [map_bnd]
  exact bnd_congr _ _ _ _ (fun _ => rfl)

theorem suffixD0_eq (ctx : ApplyCtx) (p : PTrie × List Limit) (receipts : List Receipt) :
    suffixD0 ctx p receipts = (applyReceipts ctx 0 (⟨p.1, [], [], 0, 0⟩, p.2) receipts) >>=
      (fun q => consumers ctx q.1 q.2) := by
  unfold suffixD0 consumers
  rfl

/-- `processTxs` on `[]` and the empty local-receipt phase leave the initial state alone. -/
theorem suffixD1_eq (ctx : ApplyCtx) (p : PTrie × List Limit) (receipts : List Receipt) :
    suffixD1 ctx p receipts = (applyReceiptsC ctx 0 (⟨p.1, [], [], 0, 0⟩, p.2) receipts) >>=
      (fun q => consumersDec ctx q.1 q.2.1) := by
  unfold suffixD1 consumersDec decOut
  rw [processTxs, bind_ok_]
  have h1 : (⟨p.1, [], [], [], [], p.2, 0, 0⟩ : TxSt).locals.any
      (fun r => !AccountId.isNamed r.receiverId) = false := rfl
  rw [h1]
  simp only [Bool.false_eq_true, if_false]
  rfl

/-- The D1 tail is the decorated D0 tail: the only difference is `comp` vs `i` (bridged by
`receiptsCore_zero`) and the `decOut` decoration. -/
theorem suffixD1_eq_decOut (ctx : ApplyCtx) (p : PTrie × List Limit) (receipts : List Receipt) :
    suffixD1 ctx p receipts = (suffixD0 ctx p receipts).map decOut := by
  rw [suffixD1_eq, suffixD0_eq, map_bnd]
  rw [receiptsCore_zero ctx receipts ⟨p.1, [], [], 0, 0⟩ p.2, map_bind_congr]
  exact bnd_congr _ _ _ _ (fun a => consumersDec_eq ctx a.1 a.2)

/-! ## The theorem -/

end EmptyTxs

theorem EmptyTxs (prims : NearSpecV3.Prims) (ctx : NearSpecV3.ApplyCtx) (t : NearSpec.PTrie)
    (receipts : List NearSpec.Receipt) (out : NearSpecV3.MainOut)
    (h : NearSpecV3.applyNewChunk prims ctx t receipts = .ok out) :
    ∃ out' : NearSpecV3.MainOutD1,
      NearSpecV3.applyNewChunkD1 prims ctx t receipts [] = .ok out' ∧
      out'.trie = out.trie ∧
      out'.outcomes = out.outcomes.map (fun o => { o := o, status := NearSpecV3.OStatus.value }) ∧
      out'.outgoing = out.outgoing ∧ out'.gasUsed = out.gasUsed ∧
      out'.tokensBurnt = out.tokensBurnt ∧ out'.localIds = [] := by
  rw [EmptyTxs.applyNewChunk_eq_pre] at h
  cases hp : EmptyTxs.pre prims ctx t with
  | error e => rw [hp] at h; cases h
  | ok p =>
    rw [hp, EmptyTxs.bind_ok_] at h
    refine ⟨EmptyTxs.decOut out, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [EmptyTxs.applyNewChunkD1_eq_pre, hp, EmptyTxs.bind_ok_, EmptyTxs.suffixD1_eq_decOut, h]
    rfl

end Work.Runtime
