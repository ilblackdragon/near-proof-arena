import NearSpecV3.SupplyRuntime
import NearSpecV3.D2.Validators
import NearSpecV3.D2.RuntimeD2

/-!
# §5 Write confinement: which keys a runtime step may touch

`NearSpecV3/SupplyRuntime.lean` proves the *arithmetic* of every balance-writing site: each write
either conserves the measure `Σ(amount + locked) + Σ gasBal + tokensBurnt`, lowers it (burn), or
raises it by a reward. Its own header records the limit of that result: the enumeration of sites is
"an argument over the source, not a proof", because nothing there shows that a given site cannot
write some *other* account. This file supplies the structural half of that argument in Lean.

The overlay (`D2/State.lean`) is the only path from the runtime to account balances: an account's
record lives at the trie key `kAccount a`, and every balance write goes through `Ovl.setAcct` /
`Ovl.set` into the prospective overlay, which `Ovl.commit` folds into the committed overlay. So
"this step does not touch account `b`" is exactly "`kAccount b` is absent from the prospective
overlay at every point", and that is a property a step's *definition* can be checked against.

## What this file proves

* §5.1 Structural overlay lemmas: writing one key leaves every other key's lookup alone, both for
  the prospective overlay (`lookup_set_other`) and through a commit (`lookup_commit_of_avoids`).
  `Avoids k o` is the invariant "`k` is absent from `o.prosp`".
* §5.2 The account key `kAccount` is injective, so "different accounts" is "different keys".
* §5.3 Key disjointness: an account key is never a code, access-key, contract-data, queue, buffered
  or bandwidth-scheduler key. This is what lets the structural lemmas apply to the runtime's
  non-account writes.
* §5.4 `schedOvl` — step 3 of `applyNewChunkD2`, and step 2 of `applyMissingChunkD2` — writes only
  `kBw` and commits. **It changes no account's lookup at all**, so the bandwidth scheduler cannot
  create or destroy NEAR.
* §5.5 `validatorUpdate`'s write set: an account that is neither named by a shard stake-info entry
  nor the treasury account has the *same trie lookup* before and after the call
  (`validatorUpdate_keeps`, and `validatorUpdate_keeps_ofTrie` with its input side condition
  discharged as at the runtime's two call sites). Together with §4's `validatorStep_total` this
  makes "the mint site credits named accounts only, and moves each balance by exactly its reward" a
  machine-checked statement about the runtime function, not a reading of the source.

The statement is phrased as lookup preservation rather than as `Avoids` on the result, because
`validatorUpdate` ends in `Ovl.commit`, which empties the prospective overlay: `Avoids k o1` holds of
*every* key once the function returns, so it cannot by itself say which keys were written. §5.5.1
records that the anonymous stake-info lambda of `validatorUpdate` is definitionally the named
`validatorEntryStep`, which is what lets the per-entry lemmas apply to the spec's own definition.

## What this file does not prove

The inventory argument still needs a statement that *every* overlay write in the runtime is reached
by one of the listed sites; that is symbolic execution of the successor relation. What is closed
here is the other direction — that each site's write set is confined to the keys it claims — which is
the half that the per-site arithmetic cannot supply on its own. §4's largest gap (the reward amounts
are taken from the claim's facts rather than recomputed) is untouched by this file. §5.5 confines the
*mint site's writes*; it does not say the rewards those writes carry are the ledger the epoch manager
computed.
-/

namespace NearSpecV3.D2

open NearSpec NearSpecV3

/-! ## §5.1 Structural overlay lemmas -/

theorem beq_false_of_ne {a b : Bytes} (h : a ≠ b) : (a == b) = false := by
  cases hx : a == b with
  | false => rfl
  | true => exact absurd (beq_iff_eq.mp hx) h

/-- `kvPut` of a different key leaves a key's lookup alone. -/
theorem kvFind_put_other (k k' : Bytes) (h : k' ≠ k) (v : Option Bytes)
    (l : List (Bytes × Option Bytes)) :
    kvFind k' (kvPut k v l) = kvFind k' l := by
  have h' : (k == k') = false := beq_false_of_ne (fun hk => h hk.symm)
  induction l with
  | nil => simp [kvPut, kvFind, h']
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases hka : a = k
    · subst hka
      simp [kvPut, kvFind, h']
    · by_cases hak : a = k'
      · subst hak
        simp [kvPut, kvFind, hka]
      · simp [kvPut, kvFind, hka, hak]
        exact ih

/-- **A write to one key leaves every other key's lookup unchanged.** -/
theorem lookup_set_other {o : Ovl} {k k' : Bytes} (h : k' ≠ k) (v : Bytes) :
    (o.set k v).lookup k' = o.lookup k' := by
  simp only [Ovl.set, Ovl.lookup]
  rw [kvFind_put_other k k' h]

/-- `k` is absent from the prospective overlay. -/
def Avoids (k : Bytes) (o : Ovl) : Prop := kvFind k o.prosp = none

/-- A write to a different key preserves absence. -/
theorem kvFind_put_absent {k k' : Bytes} (h : k' ≠ k) (v : Option Bytes)
    (l : List (Bytes × Option Bytes)) (hl : kvFind k l = none) :
    kvFind k (kvPut k' v l) = none := by
  rw [kvFind_put_other k' k (fun hk => h hk.symm) v l]; exact hl

theorem avoids_set {o : Ovl} {k k' : Bytes} (ho : Avoids k o) (hk : k' ≠ k) (v : Bytes) :
    Avoids k (o.set k' v) := by
  simp only [Avoids, Ovl.set]
  exact kvFind_put_absent hk (some v) o.prosp ho

theorem avoids_rollback (o : Ovl) (k : Bytes) : Avoids k o.rollback := by
  simp [Avoids, Ovl.rollback, kvFind]

theorem avoids_commit (o : Ovl) (k : Bytes) : Avoids k o.commit := by
  simp [Avoids, Ovl.commit, kvFind]

theorem avoids_ofTrie (t : PTrie) (k : Bytes) : Avoids k (Ovl.ofTrie t) := by
  simp [Avoids, Ovl.ofTrie, kvFind]

theorem kvFind_cons_some (k a : Bytes) (v : Option Bytes) (ps : List (Bytes × Option Bytes))
    (h : a = k) : kvFind k ((a, v) :: ps) = some v := by
  subst h; simp [kvFind]

theorem kvFind_cons_none (k a : Bytes) (v : Option Bytes) (ps : List (Bytes × Option Bytes))
    (h : a ≠ k) : kvFind k ((a, v) :: ps) = kvFind k ps := by
  simp [kvFind, h]

theorem kvFind_cons_none_iff (k a : Bytes) (v : Option Bytes)
    (ps : List (Bytes × Option Bytes)) :
    kvFind k ((a, v) :: ps) = none ↔ a ≠ k ∧ kvFind k ps = none := by
  by_cases h : a = k
  · rw [kvFind_cons_some k a v ps h]
    exact ⟨fun hx => absurd hx (by simp), fun hx => absurd h hx.1⟩
  · rw [kvFind_cons_none k a v ps h]
    exact ⟨fun hx => ⟨h, hx⟩, fun hx => hx.2⟩

/-- Folding writes from a list from which `k` is absent leaves `k`'s lookup in the target alone. -/
theorem kvFind_foldl_put_absent (k : Bytes) :
    ∀ (l : List (Bytes × Option Bytes)) (c : List (Bytes × Option Bytes)),
      kvFind k l = none →
      kvFind k (l.foldl (fun c p => kvPut p.1 p.2 c) c) = kvFind k c := by
  intro l
  induction l with
  | nil => intro c _; rfl
  | cons p ps ih =>
    intro c hl
    obtain ⟨a, v⟩ := p
    rw [kvFind_cons_none_iff] at hl
    simp only [List.foldl_cons]
    rw [ih (kvPut a v c) hl.2]
    exact kvFind_put_other a k (fun h => hl.1 h.symm) v c

theorem kvFind_nil (k : Bytes) : kvFind k ([] : List (Bytes × Option Bytes)) = none := rfl

/-- **A commit that avoids `k` leaves `k`'s lookup alone.** -/
theorem lookup_commit_of_avoids {o : Ovl} {k : Bytes} (ho : Avoids k o) :
    o.commit.lookup k = o.lookup k := by
  have hf := kvFind_foldl_put_absent k o.prosp o.committed ho
  simp only [Ovl.commit, Ovl.lookup, Avoids] at ho ⊢
  rw [kvFind_nil, ho, hf]

/-! ## §5.2 The account key is injective -/

theorem kAccount_inj {a b : Bytes} (h : kAccount a = kAccount b) : a = b := by
  simp [kAccount] at h; exact h

theorem kAccount_ne {a b : Bytes} (h : a ≠ b) : kAccount a ≠ kAccount b :=
  fun hk => h (kAccount_inj hk)

/-! ## §5.3 An account key is not any other kind of trie key

Every non-account key constructor starts with a first byte at least `1`, while `kAccount a` starts
with `0`. These are the disjointness facts the runtime's non-account writes need. -/

theorem kAccount_ne_kCode (a b : Bytes) : kAccount a ≠ kCode b := by simp [kAccount, kCode]
theorem kAccount_ne_kAK (a b : Bytes) (pk : PublicKey) : kAccount a ≠ kAK b pk := by
  simp [kAccount, kAK, kAKPrefix]
theorem kAccount_ne_kDataPrefix (a b : Bytes) : kAccount a ≠ kDataPrefix b := by
  simp [kAccount, kDataPrefix]
theorem kAccount_ne_kReceivedData (a b d : Bytes) : kAccount a ≠ kReceivedData b d := by
  simp [kAccount, kReceivedData]
theorem kAccount_ne_kPostponed (a b d : Bytes) : kAccount a ≠ kPostponed b d := by
  simp [kAccount, kPostponed]
theorem kAccount_ne_kPostponedId (a b d : Bytes) : kAccount a ≠ kPostponedId b d := by
  simp [kAccount, kPostponedId]
theorem kAccount_ne_kPendingCount (a b r : Bytes) : kAccount a ≠ kPendingCount b r := by
  simp [kAccount, kPendingCount]
theorem kAccount_ne_kDelayed (a : Bytes) (i : Nat) : kAccount a ≠ kDelayed i := by
  simp [kAccount, kDelayed]
theorem kAccount_ne_kDelayedIdx (a : Bytes) : kAccount a ≠ kDelayedIdx := by
  simp [kAccount, kDelayedIdx]
theorem kAccount_ne_kYieldIdx (a : Bytes) : kAccount a ≠ kYieldIdx := by simp [kAccount, kYieldIdx]
theorem kAccount_ne_kYieldTimeout (a : Bytes) (i : Nat) : kAccount a ≠ kYieldTimeout i := by
  simp [kAccount, kYieldTimeout]
theorem kAccount_ne_kYieldReceipt (a b d : Bytes) : kAccount a ≠ kYieldReceipt b d := by
  simp [kAccount, kYieldReceipt]
theorem kAccount_ne_kBufIdx (a : Bytes) : kAccount a ≠ kBufIdx := by simp [kAccount, kBufIdx]
theorem kAccount_ne_kBuf (a : Bytes) (s i : Nat) : kAccount a ≠ kBuf s i := by simp [kAccount, kBuf]
theorem kAccount_ne_kBw (a : Bytes) : kAccount a ≠ kBw := by simp [kAccount, kBw]
theorem kAccount_ne_kGroupsData (a : Bytes) (s : Nat) : kAccount a ≠ kGroupsData s := by
  simp [kAccount, kGroupsData]
theorem kAccount_ne_kGroupsItem (a : Bytes) (s i : Nat) : kAccount a ≠ kGroupsItem s i := by
  simp [kAccount, kGroupsItem]
theorem kAccount_ne_kYieldStatus (a b d : Bytes) : kAccount a ≠ kYieldStatus b d := by
  simp [kAccount, kYieldStatus]
theorem kAccount_ne_kYieldToData (a b y : Bytes) : kAccount a ≠ kYieldToData b y := by
  simp [kAccount, kYieldToData]
theorem kAccount_ne_kDataToYield (a b d : Bytes) : kAccount a ≠ kDataToYield b d := by
  simp [kAccount, kDataToYield]

/-! ## §5.4 The bandwidth scheduler cannot touch an account

`schedOvl` (`RuntimeD2.lean:159-165`) reads `kBw`, runs the pure scheduler, and commits
`o.set kBw out.state`. Its only write is to the scheduler's own key, so every account's lookup is
unchanged: step 3 of `applyNewChunkD2` and step 2 of `applyMissingChunkD2` cannot create or destroy
NEAR. -/

/-- **The scheduler's only write is to `kBw`.** Given that the incoming overlay has no prospective
write to `kAccount a` (`Avoids`, the invariant of the runtime's chunk entry — `applyNewChunkD2` and
`applyMissingChunkD2` both start from `Ovl.ofTrie t`, whose prospective overlay is empty), the
scheduler leaves that account's lookup alone. -/
theorem schedOvl_acct_lookup {prims : Prims} {ctx : ApplyCtx} {o o' : Ovl} {so : SchedOut}
    {a : Bytes} (ho : Avoids (kAccount a) o)
    (h : schedOvl prims ctx o = .ok (o', so)) :
    o'.lookup (kAccount a) = o.lookup (kAccount a) := by
  unfold schedOvl at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hso⟩ := h
      rw [hso]
      have hA : Avoids (kAccount a) (o.set kBw so.state) :=
        avoids_set ho (fun h => kAccount_ne_kBw a h.symm) so.state
      rw [lookup_commit_of_avoids hA, lookup_set_other (kAccount_ne_kBw a) so.state]
    · simp at h

theorem foldlM_avoids {α : Type} (f : Ovl → α → Except String Ovl) {k : Bytes}
    (hstep : ∀ (o o1 : Ovl) (x : α), f o x = .ok o1 → Avoids k o → Avoids k o1)
    (l : List α) (o o1 : Ovl) (h : l.foldlM f o = .ok o1) :
    Avoids k o → Avoids k o1 := by
  induction l generalizing o with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact id
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    simp only [bind, Except.bind] at h
    cases hfx : f o x with
    | error e => rw [hfx] at h; simp at h
    | ok o' =>
      rw [hfx] at h
      simp only at h
      exact fun ho => ih o' h (hstep o o' x hfx ho)

def validatorEntryStep (rewards lastP : List (Bytes × Nat)) (o : Ovl)
    (p : Bytes × Nat) : Except String Ovl := do
  match ← o.getAcct p.1 with
  | some x =>
    let locked := match lookupAmt rewards p.1 with
      | some r => x.locked + r
      | none => x.locked
    if locked ≥ two128 then throw (panicked "update_validator_accounts overflow")
    if locked < p.2 then throw (inconsistent "FATAL: staking invariant does not hold")
    let ret := locked - max p.2 ((lookupAmt lastP p.1).getD 0)
    if x.amount + ret ≥ two128 then throw (panicked "update_validator_accounts - set_amount")
    pure (o.setAcct p.1 { x with locked := locked - ret, amount := x.amount + ret })
  | none =>
    if p.2 > 0 then throw (inconsistent "account with max of stakes is not found")
    pure o

def treasuryStepRaw (o : Ovl) (t : Bytes) (rewards : List (Bytes × Nat)) : Except String Ovl := do
  let x ← match ← o.getAcct t with
    | some x => pure x
    | none => throw (inconsistent "Protocol treasury account is not found")
  let r ← ok? (lookupAmt rewards t)
    (inconsistent "Validator reward for the protocol treasury account is not found")
  if x.amount + r ≥ two128 then throw (panicked "update_validator_accounts - treasure_reward")
  pure (o.setAcct t { x with amount := x.amount + r })

theorem validatorEntryStep_avoids {rewards lastP : List (Bytes × Nat)} {o o1 : Ovl}
    {p : Bytes × Nat} {b : Bytes} (hb : p.1 ≠ b)
    (h : validatorEntryStep rewards lastP o p = .ok o1) :
    Avoids (kAccount b) o → Avoids (kAccount b) o1 := by
  intro ho
  unfold validatorEntryStep at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hg : o.getAcct p.1 with
  | error e => rw [hg] at h; simp at h
  | ok v =>
    rw [hg] at h
    simp only at h
    cases v with
    | none =>
      by_cases hpos : p.2 > 0
      · rw [ite_eq_left hpos] at h; simp at h
      · rw [ite_eq_right hpos] at h
        simp only [Except.ok.injEq] at h
        subst h; exact ho
    | some x =>
      cases hr : lookupAmt rewards p.1 with
      | none =>
        rw [hr] at h
        simp only at h
        by_cases h1 : x.locked ≥ two128
        · rw [ite_eq_left h1] at h; simp at h
        · rw [ite_eq_right h1] at h
          by_cases h2 : x.locked < p.2
          · rw [ite_eq_left h2] at h; simp at h
          · rw [ite_eq_right h2] at h
            by_cases h3 : x.amount + (x.locked - max p.2 ((lookupAmt lastP p.1).getD 0)) ≥ two128
            · rw [ite_eq_left h3] at h; simp at h
            · rw [ite_eq_right h3] at h
              simp only [Except.ok.injEq] at h
              subst h; exact avoids_set ho (kAccount_ne hb) _
      | some r =>
        rw [hr] at h
        simp only at h
        by_cases h1 : x.locked + r ≥ two128
        · rw [ite_eq_left h1] at h; simp at h
        · rw [ite_eq_right h1] at h
          by_cases h2 : x.locked + r < p.2
          · rw [ite_eq_left h2] at h; simp at h
          · rw [ite_eq_right h2] at h
            by_cases h3 : x.amount + (x.locked + r - max p.2 ((lookupAmt lastP p.1).getD 0)) ≥ two128
            · rw [ite_eq_left h3] at h; simp at h
            · rw [ite_eq_right h3] at h
              simp only [Except.ok.injEq] at h
              subst h; exact avoids_set ho (kAccount_ne hb) _

theorem validatorFold_avoids {rewards lastP : List (Bytes × Nat)} :
    ∀ (stakeInfo : List (Bytes × Nat)) (o o1 : Ovl) (b : Bytes),
      (∀ p ∈ stakeInfo, p.1 ≠ b) →
      stakeInfo.foldlM (validatorEntryStep rewards lastP) o = .ok o1 →
      Avoids (kAccount b) o → Avoids (kAccount b) o1 := by
  intro stakeInfo
  induction stakeInfo with
  | nil =>
    intro o o1 b _ h ho
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ho
  | cons p ps ih =>
    intro o o1 b hb h ho
    rw [List.foldlM_cons] at h
    simp only [bind, Except.bind] at h
    cases hstep : validatorEntryStep rewards lastP o p with
    | error e => rw [hstep] at h; simp at h
    | ok o' =>
      rw [hstep] at h
      simp only at h
      refine ih o' o1 b ?_ h ?_
      · intro q hq
        exact hb q (List.mem_cons_of_mem _ hq)
      · exact validatorEntryStep_avoids (hb p (List.mem_cons_self ..)) hstep ho

theorem treasuryStepRaw_avoids {o o1 : Ovl} {t b : Bytes} {rewards : List (Bytes × Nat)}
    (hb : t ≠ b) (h : treasuryStepRaw o t rewards = .ok o1) :
    Avoids (kAccount b) o → Avoids (kAccount b) o1 := by
  intro ho
  unfold treasuryStepRaw at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hg : o.getAcct t with
  | error e => rw [hg] at h; simp at h
  | ok v =>
    rw [hg] at h
    simp only at h
    cases v with
    | none => simp at h
    | some x =>
      cases hr : ok? (lookupAmt rewards t)
          (inconsistent "Validator reward for the protocol treasury account is not found") with
      | error e => rw [hr] at h; simp at h
      | ok r =>
        rw [hr] at h
        simp only at h
        by_cases h1 : x.amount + r ≥ two128
        · rw [ite_eq_left h1] at h; simp at h
        · rw [ite_eq_right h1] at h
          simp only [Except.ok.injEq] at h
          subst h; exact avoids_set ho (kAccount_ne hb) _

def validatorUpdateE (l : Layout) (own : Nat) (o : Ovl) (f : ValidatorUpdateFacts)
    (last : List (Bytes × Nat)) : Except String Ovl := do
  let onShard := fun (a : Bytes) => l.shardOf a == own
  let stakeInfo := f.stakeInfo.filter (onShard ·.1)
  let rewards := f.validatorRewards.filter (onShard ·.1)
  let lastP := lastProposals l own last
  let o ← stakeInfo.foldlM (validatorEntryStep rewards lastP) o
  let o ← match f.treasury with
    | some t =>
      if onShard t && !(stakeInfo.any (·.1 == t)) then do
        let x ← match ← o.getAcct t with
          | some x => pure x
          | none => throw (inconsistent "Protocol treasury account is not found")
        let r ← ok? (lookupAmt rewards t)
          (inconsistent "Validator reward for the protocol treasury account is not found")
        if x.amount + r ≥ two128 then throw (panicked "update_validator_accounts - treasure_reward")
        pure (o.setAcct t { x with amount := x.amount + r })
      else pure o
    | none => pure o
  pure o.commit

theorem validatorUpdate_eq_entries (l : Layout) (own : Nat) (o : Ovl)
    (f : ValidatorUpdateFacts) (last : List (Bytes × Nat)) :
    validatorUpdate l own o f last = validatorUpdateE l own o f last := rfl

/-! ## §5.5 The whole function

`validatorUpdate` ends in `o.commit`, which empties the prospective overlay, so `Avoids` is trivially
true of its result for every key and cannot by itself say which keys the function wrote. The
informative statement is that an account the function does not name has the same trie lookup
afterwards as before — that is what "the write set is confined to the shard's stake info plus the
treasury" means for a function handing back a committed overlay.

The proof rewrites `validatorUpdate` to the named-entry form `validatorUpdateE`
(`validatorUpdate_eq_entries`), whose stake-info step is the named `validatorEntryStep`, then
case-splits the fold and the treasury branch exactly as the code does. -/

/-- `k`'s lookup is unchanged between the two overlays. -/
def Keeps (k : Bytes) (o o1 : Ovl) : Prop := o1.lookup k = o.lookup k

theorem setAcct_keeps {o : Ovl} {a b : Bytes} {x : Acct} (hb : a ≠ b) :
    Keeps (kAccount b) o (o.setAcct a x) := by
  simp only [Keeps, Ovl.setAcct]
  exact lookup_set_other (Ne.symm (kAccount_ne hb)) x.encode

/-! ### §5.5.1 The named step is the original lambda -/

theorem validatorEntryStep_eq_lambda (rewards lastP : List (Bytes × Nat)) :
    (fun (o : Ovl) (a, maxStake) => do
      match ← o.getAcct a with
      | some x =>
        let locked := match lookupAmt rewards a with
          | some r => x.locked + r
          | none => x.locked
        if locked ≥ two128 then throw (panicked "update_validator_accounts overflow")
        if locked < maxStake then throw (inconsistent "FATAL: staking invariant does not hold")
        let ret := locked - max maxStake ((lookupAmt lastP a).getD 0)
        if x.amount + ret ≥ two128 then throw (panicked "update_validator_accounts - set_amount")
        pure (o.setAcct a { x with locked := locked - ret, amount := x.amount + ret })
      | none =>
        if maxStake > 0 then throw (inconsistent "account with max of stakes is not found")
        pure o : Ovl → Bytes × Nat → Except String Ovl)
    = validatorEntryStep rewards lastP := rfl

/-! ### §5.5.2 The per-entry step keeps an unnamed account's lookup -/

theorem validatorEntryStep_keeps {rewards lastP : List (Bytes × Nat)} {o o1 : Ovl}
    {p : Bytes × Nat} {b : Bytes} (hb : p.1 ≠ b)
    (h : validatorEntryStep rewards lastP o p = .ok o1) :
    Keeps (kAccount b) o o1 := by
  unfold validatorEntryStep at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hg : o.getAcct p.1 with
  | error e => rw [hg] at h; simp at h
  | ok v =>
    rw [hg] at h
    simp only at h
    cases v with
    | none =>
      by_cases hpos : p.2 > 0
      · rw [ite_eq_left hpos] at h; simp at h
      · rw [ite_eq_right hpos] at h
        simp only [Except.ok.injEq] at h
        subst h; rfl
    | some x =>
      cases hr : lookupAmt rewards p.1 with
      | none =>
        rw [hr] at h; simp only at h
        by_cases h1 : x.locked ≥ two128
        · rw [ite_eq_left h1] at h; simp at h
        · rw [ite_eq_right h1] at h
          by_cases h2 : x.locked < p.2
          · rw [ite_eq_left h2] at h; simp at h
          · rw [ite_eq_right h2] at h
            by_cases h3 : x.amount + (x.locked - max p.2 ((lookupAmt lastP p.1).getD 0)) ≥ two128
            · rw [ite_eq_left h3] at h; simp at h
            · rw [ite_eq_right h3] at h
              simp only [Except.ok.injEq] at h
              subst h
              exact setAcct_keeps hb
      | some r =>
        rw [hr] at h; simp only at h
        by_cases h1 : x.locked + r ≥ two128
        · rw [ite_eq_left h1] at h; simp at h
        · rw [ite_eq_right h1] at h
          by_cases h2 : x.locked + r < p.2
          · rw [ite_eq_left h2] at h; simp at h
          · rw [ite_eq_right h2] at h
            by_cases h3 : x.amount + (x.locked + r - max p.2 ((lookupAmt lastP p.1).getD 0)) ≥ two128
            · rw [ite_eq_left h3] at h; simp at h
            · rw [ite_eq_right h3] at h
              simp only [Except.ok.injEq] at h
              subst h
              exact setAcct_keeps hb

theorem validatorFold_keeps {rewards lastP : List (Bytes × Nat)} :
    ∀ (stakeInfo : List (Bytes × Nat)) (o o1 : Ovl) (b : Bytes),
      (∀ p ∈ stakeInfo, p.1 ≠ b) →
      stakeInfo.foldlM (validatorEntryStep rewards lastP) o = .ok o1 →
      Keeps (kAccount b) o o1 := by
  intro stakeInfo
  induction stakeInfo with
  | nil =>
    intro o o1 b _ h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact rfl
  | cons p ps ih =>
    intro o o1 b hb h
    rw [List.foldlM_cons] at h
    simp only [bind, Except.bind] at h
    cases hstep : validatorEntryStep rewards lastP o p with
    | error e => rw [hstep] at h; simp at h
    | ok o' =>
      rw [hstep] at h
      simp only at h
      exact (ih o' o1 b (fun q hq => hb q (List.mem_cons_of_mem _ hq)) h).trans
        (validatorEntryStep_keeps (hb p (List.mem_cons_self ..)) hstep)

theorem treasuryStepRaw_keeps {o o1 : Ovl} {t b : Bytes} {rewards : List (Bytes × Nat)}
    (hb : t ≠ b) (h : treasuryStepRaw o t rewards = .ok o1) :
    Keeps (kAccount b) o o1 := by
  unfold treasuryStepRaw at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hg : o.getAcct t with
  | error e => rw [hg] at h; simp at h
  | ok v =>
    rw [hg] at h
    simp only at h
    cases v with
    | none => simp at h
    | some x =>
      cases hr : ok? (lookupAmt rewards t)
          (inconsistent "Validator reward for the protocol treasury account is not found") with
      | error e => rw [hr] at h; simp at h
      | ok r =>
        rw [hr] at h
        simp only at h
        by_cases h1 : x.amount + r ≥ two128
        · rw [ite_eq_left h1] at h; simp at h
        · rw [ite_eq_right h1] at h
          simp only [Except.ok.injEq] at h
          subst h
          exact setAcct_keeps hb

/-! ### §5.5.3 The whole function -/

/-- **`validatorUpdate` writes no key outside the shard's stake info plus the treasury.** An account
`b` that is neither named by a shard stake-info entry on this shard nor the treasury account has the
same trie lookup after the call as before it: the function creates and destroys no state under
`kAccount b`.

This is the structural companion of §4's `validatorStep_total` and `treasuryStep_total`. Those say
that the writes *that do happen* move the balance by exactly a reward; this says that no other
account's balance is written at all. -/
theorem validatorUpdate_keeps {l : Layout} {own : Nat} {o o1 : Ovl}
    {f : ValidatorUpdateFacts} {last : List (Bytes × Nat)} {b : Bytes}
    (hinfo : ∀ p ∈ f.stakeInfo.filter (fun a => l.shardOf a.1 == own), p.1 ≠ b)
    (htr : ∀ t, f.treasury = some t → t ≠ b)
    (ho : Avoids (kAccount b) o)
    (h : validatorUpdate l own o f last = .ok o1) :
    Keeps (kAccount b) o o1 := by
  rw [validatorUpdate_eq_entries] at h
  unfold validatorUpdateE at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hfold : List.foldlM
      (validatorEntryStep (f.validatorRewards.filter (fun a => l.shardOf a.1 == own))
        (lastProposals l own last)) o
      (f.stakeInfo.filter (fun a => l.shardOf a.1 == own)) with
  | error e => rw [hfold] at h; simp at h
  | ok o' =>
    rw [hfold] at h
    simp only at h
    have hA : Avoids (kAccount b) o' := validatorFold_avoids _ _ _ _ hinfo hfold ho
    have hK : Keeps (kAccount b) o o' := validatorFold_keeps _ _ _ _ hinfo hfold
    cases ht : f.treasury with
    | none =>
      simp only [ht, Except.ok.injEq] at h
      subst h
      unfold Keeps
      rw [lookup_commit_of_avoids hA]
      exact hK
    | some t =>
      simp only [ht] at h
      split at h
      · rename_i hguard
        cases hget : o'.getAcct t with
        | error e => rw [hget] at h; simp at h
        | ok v =>
          rw [hget] at h
          cases v with
          | none => simp at h
          | some x =>
            cases hok : ok? (lookupAmt
                (f.validatorRewards.filter (fun a => l.shardOf a.1 == own)) t)
                (inconsistent "Validator reward for the protocol treasury account is not found") with
            | error e => rw [hok] at h; simp at h
            | ok r =>
              rw [hok] at h
              simp only at h
              by_cases h1 : x.amount + r ≥ two128
              · rw [ite_eq_left h1] at h; simp at h
              · rw [ite_eq_right h1] at h
                simp only [Except.ok.injEq] at h
                subst h
                unfold Keeps at hK
                unfold Keeps
                have hset : Avoids (kAccount b) (o'.setAcct t { x with amount := x.amount + r }) :=
                  avoids_set hA (kAccount_ne (htr t ht)) _
                have hsetK : (o'.setAcct t { x with amount := x.amount + r }).lookup (kAccount b)
                    = o'.lookup (kAccount b) := setAcct_keeps (htr t ht)
                rw [lookup_commit_of_avoids hset]
                exact hsetK.trans hK
      · simp only [Except.ok.injEq] at h
        subst h
        unfold Keeps
        rw [lookup_commit_of_avoids hA]
        exact hK

/-! ### §5.5.4 The statement at the real call site

`validatorUpdate_keeps` carries an `Avoids` hypothesis on its input overlay. The runtime's only call
site builds that overlay with `Ovl.ofTrie` (`D2/RuntimeD2.lean:178`, and `applyMissingChunkD2`'s call
at `:235`), whose `prosp` is `[]`, so `Avoids k o` holds for every key by `rfl` and the hypothesis is
free where it matters. -/

theorem Avoids_ofTrie (t : PTrie) (k : Bytes) : Avoids k (Ovl.ofTrie t) := rfl

/-- **The confinement result with no side condition on the input overlay.** The mint site hands back
a committed overlay in which an account outside the shard's stake info and the treasury has exactly
the trie lookup it had in the trie the call started from. -/
theorem validatorUpdate_keeps_ofTrie {l : Layout} {own : Nat} {t : PTrie} {o1 : Ovl}
    {f : ValidatorUpdateFacts} {last : List (Bytes × Nat)} {b : Bytes}
    (hinfo : ∀ p ∈ f.stakeInfo.filter (fun a => l.shardOf a.1 == own), p.1 ≠ b)
    (htr : ∀ t', f.treasury = some t' → t' ≠ b)
    (h : validatorUpdate l own (Ovl.ofTrie t) f last = .ok o1) :
    Keeps (kAccount b) (Ovl.ofTrie t) o1 :=
  validatorUpdate_keeps hinfo htr (Avoids_ofTrie t _) h

end NearSpecV3.D2
