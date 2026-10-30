import NearSpecV3.Successor.TierO2

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 — the global-actions switch: component agreements

`globalActions` changes, besides the interpreter flag (`callHost_RR_global`, `HostCommStep.lean`):
the action-log translation (`managerGlobal`, `finishActsGlobal`), the stored-receipt and transaction
codecs (`GlobalCodecs`), the queue policy (`globalQueuePolicy`) and the driver's routing fields.
This file proves the agreements that hold on every input the D2 side decides:

* **Keys and actions.** `pPkGlobal_of_pPk`, `pBaseGlobal_of_pBase`, `pActGlobal_of_pBaseAct`: where the
  D2 decoder decodes, the global one decodes to the same value and rest.
* **Where the global decoder newly accepts, the D2 decoder excludes** (`w.shape`):
  `pPk_mlDsa_ood`, `pBase_global_ood` (tags 9, 10, 11), `pSig_mlDsa` (tag 2: the same truncation error
  or `oodMlDsaSig`), `pRcpt_distribution_ood` (tag 4).
* **Action log.** `finishActsGlobal_of_finishActs`, and `managerGlobal_eq_manager` on a log without
  raw (global) actions.
* **Queue routing.** `globalTarget_of_not_distribution`: on a non-distribution receipt whose
  shard is in the layout, the global target is the D2 shard.

What is not here (README §6, "O3"): the delegate-action and transaction re-serialization
(`pActGlobal` rebuilds a delegate's payload, `pTxD2Global` the transaction body, from the decoded
fields; D2 keeps the consumed bytes), the lower run's invariant (flag off, trie-backed, no raw
actions) across a whole interpreter run, and the engine walk with `ga` differing.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3 NearSpecV3.Wasm GlobalCodecs

/-! ## Keys -/

theorem pPublicKey_tag_le (w : String) (bs : Bytes) (pk : PublicKey) (rest : Bytes)
    (h : pPublicKey w bs = .ok (pk, rest)) : pk.tag ≤ 2 := by
  unfold pPublicKey at h
  simp only [bind, Except.bind] at h
  cases hu : pU8 (w ++ " key type") bs with
  | error e => rw [hu] at h; cases h
  | ok q =>
    obtain ⟨t, b⟩ := q
    rw [hu] at h
    simp only at h
    rcases t with _ | _ | _ | t
    all_goals simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    all_goals (repeat' split at h)
    all_goals first
      | (cases h <;> simp)
      | skip

/-- Where `D2.pPk` decodes a key, `pPkGlobal` decodes the same key. -/
theorem pPkGlobal_of_pPk (w : String) (bs : Bytes) (x : PublicKey × Bytes) (h : pPk w bs = .ok x) :
    pPkGlobal w bs = .ok x := by
  unfold pPk at h
  unfold pPkGlobal
  simp only [bind, Except.bind] at h ⊢
  cases hp : pPublicKey w bs with
  | error e => rw [hp] at h; cases h
  | ok q =>
    obtain ⟨pk, rest⟩ := q
    rw [hp] at h
    simp only at h ⊢
    have hle := pPublicKey_tag_le w bs pk rest hp
    have hgt : ¬ pk.tag > 2 := by omega
    simp only [hgt, if_false]
    split at h
    · cases h
    · exact h

/-- On an ML-DSA-65 key, `D2.pPk` excludes. -/
theorem pPk_mlDsa_ood (w : String) (bs : Bytes) (pk : PublicKey) (rest : Bytes)
    (hp : pPublicKey w bs = .ok (pk, rest)) (ht : pk.tag = 2) : pPk w bs = .error oodMlDsaKey := by
  unfold pPk
  simp only [bind, Except.bind, hp, ht]
  rfl

/-! ## Actions -/

/-- Where `D2.pBase` decodes an action body, `pBaseGlobal` decodes the same one. -/
theorem pBaseGlobal_of_pBase (tag : Nat) (bs : Bytes) (x : Base × Bytes) (h : pBase tag bs = .ok x) :
    pBaseGlobal tag bs = .ok x := by
  unfold pBaseGlobal
  match tag, h with
  | 9, h => simp [pBase] at h
  | 10, h => simp [pBase] at h
  | 11, h => simp [pBase] at h
  | 4, h =>
    simp only [pBaseGlobalKeyed]
    simp only [pBase, bind, Except.bind] at h ⊢
    cases hs : pU128 "stake" bs with
    | error e => rw [hs] at h; cases h
    | ok q =>
      rw [hs] at h; simp only at h ⊢
      cases hk : pPk "stake key" q.2 with
      | error e => rw [hk] at h; cases h
      | ok k => rw [hk] at h; rw [pPkGlobal_of_pPk _ _ _ hk]; exact h
  | 5, h =>
    simp only [pBaseGlobalKeyed]
    simp only [pBase, bind, Except.bind] at h ⊢
    cases hk : pPk "add key" bs with
    | error e => rw [hk] at h; cases h
    | ok k => rw [hk] at h; rw [pPkGlobal_of_pPk _ _ _ hk]; exact h
  | 6, h =>
    simp only [pBaseGlobalKeyed]
    simp only [pBase, bind, Except.bind] at h ⊢
    cases hk : pPk "delete key" bs with
    | error e => rw [hk] at h; cases h
    | ok k => rw [hk] at h; rw [pPkGlobal_of_pPk _ _ _ hk]; exact h
  | 12, h =>
    simp only [pBaseGlobalKeyed]
    simp only [pBase, bind, Except.bind] at h ⊢
    cases hk : pPk "gas key" bs with
    | error e => rw [hk] at h; cases h
    | ok k => rw [hk] at h; rw [pPkGlobal_of_pPk _ _ _ hk]; exact h
  | 13, h =>
    simp only [pBaseGlobalKeyed]
    simp only [pBase, bind, Except.bind] at h ⊢
    cases hk : pPk "gas key" bs with
    | error e => rw [hk] at h; cases h
    | ok k => rw [hk] at h; rw [pPkGlobal_of_pPk _ _ _ hk]; exact h
  | 0, h => exact h
  | 1, h => exact h
  | 2, h => exact h
  | 3, h => exact h
  | 7, h => exact h
  | 8, h => exact h
  | n + 14, h => exact h

/-- On tags 9, 10, 11 `D2.pBase` excludes (`w.shape`). -/
theorem pBase_global_ood (bs : Bytes) :
    pBase 9 bs = .error oodDeployGlobal ∧ pBase 10 bs = .error oodUseGlobal ∧
      pBase 11 bs = .error oodStateInit := ⟨rfl, rfl, rfl⟩

/-- `pBase` never yields a state-init body (its tag is excluded), so `baseRaw` keeps the bytes. -/
theorem pBase_not_stateInit (tag : Nat) (bs : Bytes) (d : L4.Dsi) (rest : Bytes) :
    pBase tag bs ≠ .ok (.stateInit d, rest) := by
  intro h
  unfold pBase at h
  split at h
  all_goals (try simp only [bind, Except.bind, pure, Except.pure] at h)
  all_goals (repeat' split at h)
  all_goals cases h

theorem baseRaw_of_pBase (raw : Bytes) (tag : Nat) (bs : Bytes) (b : Base) (rest : Bytes)
    (h : pBase tag bs = .ok (b, rest)) : baseRaw raw b = raw := by
  unfold baseRaw
  cases b with
  | stateInit d => exact absurd h (pBase_not_stateInit tag bs d rest)
  | _ => rfl

/-- Where `D2.pBaseAct` decodes, `pActGlobal` decodes the same base action. -/
theorem pActGlobal_of_pBaseAct (raw : Bytes) (b : BaseAct) (rest : Bytes) (h : pBaseAct raw = .ok (b, rest)) :
    pActGlobal raw = .ok (.base b, rest) := by
  unfold pBaseAct at h
  unfold pActGlobal
  simp only [bind, Except.bind] at h ⊢
  cases ht : pU8 "action tag" raw with
  | error e => rw [ht] at h; cases h
  | ok q =>
    obtain ⟨t, bs⟩ := q
    rw [ht] at h; simp only at h ⊢
    split at h
    · cases h
    · rename_i hnt
      simp only [hnt, Bool.false_eq_true, ↓reduceIte]
      cases hb : pBase t bs with
      | error e => rw [hb] at h; cases h
      | ok y =>
        obtain ⟨bb, bs'⟩ := y
        rw [hb] at h
        rw [pBaseGlobal_of_pBase t bs _ hb]
        simp only [pure, Except.pure] at h ⊢
        cases h
        rw [baseRaw_of_pBase _ t bs _ _ hb]

/-- On an ML-DSA-65 signature `D2.pSig` fails exactly as `pSigGlobal` does on truncation, and
otherwise excludes. -/
theorem pSig_mlDsa (w : String) (bs rest : Bytes) (hb : pU8 (w ++ " signature type") bs = .ok (2, rest)) :
    (∃ e, pTake 3309 w rest = .error e ∧ pSig w bs = .error e ∧ pSigGlobal w bs = .error e) ∨
      pSig w bs = .error oodMlDsaSig := by
  unfold pSig pSigGlobal
  simp only [bind, Except.bind, hb]
  cases hp : pTake 3309 w rest with
  | error e => left; exact ⟨e, rfl, rfl, rfl⟩
  | ok q => right; rfl

/-! ## Receipts -/

/-- A distribution receipt (tag 4) is a `D2.pRcpt` exclusion. -/
theorem pRcpt_distribution_ood (bs : Bytes) (pred recv rid rest : Bytes)
    (h1 : pAccountId "predecessor_id" bs = .ok (pred, rest)) :
    ∀ rest2 rest3 rest4, pAccountId "receiver_id" rest = .ok (recv, rest2) →
      pHash "receipt_id" rest2 = .ok (rid, rest3) → pU8 "ReceiptEnum tag" rest3 = .ok (4, rest4) →
      pRcpt bs = .error oodGcd := by
  intro rest2 rest3 rest4 h2 h3 h4
  unfold pRcpt
  simp only [bind, Except.bind, h1, h2, h3, h4]
  rfl

/-! ## Action log -/

theorem mapM_ok_of {α β : Type} (f g : α → Except String β) (hfg : ∀ a x, f a = .ok x → g a = .ok x) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → l.mapM g = .ok r
  | [], r, h => h
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h ⊢
    cases hf : f a with
    | error e => rw [hf] at h; cases h
    | ok x =>
      rw [hf] at h; rw [hfg a x hf]; simp only at h ⊢
      cases hm : l.mapM f with
      | error e => rw [hm] at h; cases h
      | ok r' => rw [hm] at h; rw [mapM_ok_of f g hfg l r' hm]; exact h

/-- Where `D3.finishActs` produces actions, `finishActsGlobal` produces the same ones. -/
theorem finishActsGlobal_of_finishActs (r : MR) (acts : List Act) (h : finishActs r = .ok acts) :
    finishActsGlobal r = .ok acts := by
  unfold finishActs at h
  unfold finishActsGlobal
  refine mapM_ok_of _ _ ?_ _ _ h
  intro a x hx
  obtain ⟨raw, fc⟩ := a
  rcases fc with _ | ⟨g, w', mb, ab, dep⟩
  all_goals simp only at hx ⊢
  all_goals
    split at hx
    · rename_i b heq; rw [pActGlobal_of_pBaseAct _ _ _ heq]; exact hx
    · cases hx
    · split at hx <;> cases hx

/-- A log entry without a raw (global) action. -/
def NoRaw (log : Array MAct) : Prop := ∀ e ∈ log, e.rawAction = none

theorem forIn_range_pure_id {β : Type} (n : Nat) (b : β) (f : Nat → β → Except String (ForInStep β))
    (hf : ∀ i, i < n → ∀ b, f i b = .ok (.yield b)) : forIn [0:n] b f = .ok b := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have : ∀ (l : List Nat) (b : β), (∀ i ∈ l, i < n) → forIn l b f = .ok b := by
    intro l
    induction l with
    | nil => intro b _; rfl
    | cons a l ih =>
      intro b hl
      simp only [List.forIn_cons]
      rw [hf a (hl a (List.mem_cons_self)) b]
      exact ih b (fun i hi => hl i (List.mem_cons_of_mem _ hi))
  apply this
  intro i hi
  simp [List.mem_range'] at hi
  omega

theorem map_eq_self (f : MAct → MAct) (log : Array MAct) (h : ∀ e ∈ log, f e = e) : log.map f = log := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map]
    exact h _ (Array.getElem_mem h2)

/-- **The action-log translation agrees on logs without global actions.** -/
theorem managerGlobal_eq_manager (log : Array MAct) (ah : Bytes) (h : Nat) (hn : NoRaw log) :
    managerGlobal log ah h = manager log ah h := by
  unfold managerGlobal
  rw [map_eq_self _ log (fun e he => by simp only [hn e he])]
  simp only [bind, Except.bind]
  cases hm : manager log ah h with
  | error e => rfl
  | ok q =>
    obtain ⟨rs, idx, resumes⟩ := q
    simp only
    rw [forIn_range_pure_id]
    · rfl
    · intro i hi b
      have hr : (log[i]?.bind (·.rawAction)) = none := by
        rw [Array.getElem?_eq_getElem hi]
        simp only [Option.bind_some]
        exact hn log[i] (Array.getElem_mem hi)
      simp only [hr]
      rfl

/-! ## Queue routing -/

/-- On a non-distribution receipt whose D2 shard is in the layout, the global queue target is the D2
shard. -/
theorem globalTarget_of_not_distribution (l : Layout) (r : Rcpt) (h : rcptIsDistribution r = false)
    (hl : l.shardIds.contains (l.shardOf r.recv) = true) :
    StorageExecution.globalTarget l r = .ok (l.shardOf r.recv) := by
  unfold StorageExecution.globalTarget
  rw [routedShard_of_not_distribution r l h]
  dsimp only
  rw [hl]
  rfl

#print axioms pPkGlobal_of_pPk
#print axioms pBaseGlobal_of_pBase
#print axioms pActGlobal_of_pBaseAct
#print axioms pSig_mlDsa
#print axioms pRcpt_distribution_ood
#print axioms finishActsGlobal_of_finishActs
#print axioms managerGlobal_eq_manager
#print axioms globalTarget_of_not_distribution

end NearSpecV3.Successor
