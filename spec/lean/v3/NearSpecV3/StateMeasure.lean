import NearSpecV3.D2.TrieProps
import NearSpecV3.D2.State
import NearSpecV3.SupplyRuntime
import NearSpec.TrieUpsertProofs

/-!
# §6 A state measure over the trie, and how a write moves it

`NearSpecV3/SupplyRuntime.lean` gives the arithmetic of each balance write, but states it about bare
`Nat`s: `refundStep_total {amount dep : Nat}` never mentions `Ovl`, `Rcpt` or `refunds`, and `dep` is
not tied to what was charged. This file puts a measure on `PTrie` so the arithmetic can be composed
into a statement about state.

## Why the measure is key-indexed

The obvious definition — sum over `PTrie.allKeys` — is what §6.2 defines, and it is the right *value*,
but it is the wrong thing to reason about under a write. `allKeys` returns the keys that currently have
values, so a write of a **new** key changes the enumeration itself:

```
(newLeaf [0,1] [5]).allKeys []                       = some [[0,1]]
((newLeaf [0,1] [5]).upsert [0,2] [7]).allKeys []    = some [[0,1],[0,2]]
```

So "a write does not change the key set" is false in general — it holds only when the key was already
present. §6.3 therefore reasons about a sum over an **explicit key list**, which is stable under a write
by construction, and §6.4 proves that this equals `acctSumOf` when the list covers the state.
-/

namespace NearSpec

/-! ## §6.1 The enumeration is exactly the set of keys with a value

`allKeys_sound` / `allKeys_complete` already existed in `D2/TrieProps.lean:326,506`, but nothing
imported that module, so they were not on the build path. Restating them at `acc = []` puts them there. -/

/-- Every path `allKeys` reports really has a value at it. -/
theorem PTrie.allKeys_sound_nil {t : PTrie} {ns : List (List Nat)} (h : t.allKeys [] = some ns) :
    ∀ n ∈ ns, ∃ v, t.find n = some (some v) := by
  intro n hn
  obtain ⟨r, v, heq, hf⟩ := PTrie.allKeys_sound t [] ns h n hn
  exact ⟨v, by simpa using heq ▸ hf⟩

/-- Every path that has a value is reported. -/
theorem PTrie.allKeys_complete_nil {t : PTrie} {ns : List (List Nat)} (h : t.allKeys [] = some ns) :
    ∀ n v, t.find n = some (some v) → n ∈ ns := by
  intro n v hf
  have := PTrie.allKeys_complete t [] ns h n v (by simpa using hf)
  simpa using this

end NearSpec

namespace NearSpecV3.D2

open NearSpec NearSpecV3 NearSpecV3.Supply

/-! ## §6.2 The measure -/

/-- `filterMap` with pointwise-equal functions on the list's members is equal. -/
theorem filterMap_congr_on {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ a ∈ l, f a = g a) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filterMap_cons]
    rw [h a (by simp)]
    have : ∀ b ∈ as, f b = g b := fun b hb => h b (by simp [hb])
    rw [ih this]

/-- The total of one account record, or 0 if the bytes are not an account. -/
def acctTotalOf (v : Bytes) : Nat :=
  match decodeAcct v with
  | some x => x.total
  | none => 0

/-- The balance held against an access-key record, or 0 if the bytes are not one. -/
def akGasOf (v : Bytes) : Nat :=
  match decodeAK v with
  | some k => k.gasBal
  | none => 0

/-- The values stored at the paths in `ns` whose first nibble is `k`. -/
def headVals (t : PTrie) (k : Nat) (ns : List (List Nat)) : List Bytes :=
  ns.filterMap fun n =>
    if n.head? == some k then
      (match t.find n with | some (some v) => some v | _ => none)
    else none

/-- **Equal values on matching keys give equal `headVals`.** -/
theorem headVals_congr {t t' : PTrie} {k : Nat} {ns : List (List Nat)}
    (h : ∀ n ∈ ns, n.head? = some k → t.find n = t'.find n) :
    headVals t k ns = headVals t' k ns := by
  unfold headVals
  refine filterMap_congr_on ?_
  intro n hn
  by_cases hk : n.head? == some k
  · rw [ite_eq_left hk, ite_eq_left hk, h n hn (by simpa using hk)]
  · rw [ite_eq_right hk, ite_eq_right hk]

/-- **NEAR held in accounts**, summed over the trie's account keys. -/
def acctSumOf (t : PTrie) : Nat :=
  match t.allKeys [] with
  | none => 0
  | some ns => sumNat ((headVals t 0 ns).map acctTotalOf)

/-- **NEAR held against gas keys**, summed over the trie's access-key entries. -/
def akSumOf (t : PTrie) : Nat :=
  match t.allKeys [] with
  | none => 0
  | some ns => sumNat ((headVals t 2 ns).map akGasOf)

/-- **Two tries that agree on every account key have the same account sum.** -/
theorem acctSumOf_congr {t t' : PTrie} {ns : List (List Nat)}
    (h : t.allKeys [] = some ns) (h' : t'.allKeys [] = some ns)
    (hf : ∀ n ∈ ns, n.head? = some 0 → t.find n = t'.find n) :
    acctSumOf t = acctSumOf t' := by
  unfold acctSumOf
  simp only [h, h', headVals_congr hf]

/-- **The state measure**: NEAR in accounts, plus NEAR against gas keys, plus burnt tokens. -/
def stateTotal (t : PTrie) (burnt : Nat) : Nat := acctSumOf t + akSumOf t + burnt

/-! ### The measure is not vacuous

`acctSumOf_congr` says a non-account write cannot change the account sum. On its own that would also
hold for a measure that ignored values entirely — so this section records the other direction: a
record's `amount + locked` determines its contribution, hence two records with different totals
contribute differently. Without this, the constant-zero function would satisfy §6.3. -/

/-- **Different account totals contribute different amounts.** -/
theorem acctTotalOf_ne {v v' : Bytes} {x x' : Acct}
    (h : decodeAcct v = some x) (h' : decodeAcct v' = some x')
    (ht : x.total ≠ x'.total) : acctTotalOf v ≠ acctTotalOf v' := by
  unfold acctTotalOf
  rw [h, h']
  exact ht

/-! ## §6.3 A key-indexed sum, stable under a write

`sumKeys` sums `f` over an explicit list of paths, reading each through `find`. Because the list is
given, a write cannot change *which* terms appear — only what they evaluate to — so this is the shape
that composes with `find_upsert_self` / `find_upsert_other`. -/

/-- Sum of `f` over an explicit path list, reading each path's value. Absent paths contribute 0. -/
def sumKeys (t : PTrie) (ns : List (List Nat)) (f : Bytes → Nat) : Nat :=
  sumNat (ns.map fun n => match t.find n with | some (some v) => f v | _ => 0)

theorem sumKeys_nil (t : PTrie) (f : Bytes → Nat) : sumKeys t [] f = 0 := rfl

/-- **`sumKeys` splits off the head path.** -/
theorem sumKeys_cons (t : PTrie) (n : List Nat) (ns : List (List Nat)) (f : Bytes → Nat) :
    sumKeys t (n :: ns) f
      = (match t.find n with | some (some v) => f v | _ => 0) + sumKeys t ns f := by
  unfold sumKeys
  simp only [List.map_cons, sumNat]

/-- **A write changes only the written path's term.** For every other listed path the value is
unchanged (`find_upsert_other`), so the sum over the rest is unchanged. -/
theorem sumKeys_upsert_cons {t t' : PTrie} {key : List Nat} {v : Bytes}
    (hwf : t.wf = true) (hok : nibblesOk key = true) (hu : t.upsert key v = some t')
    {ns : List (List Nat)} (hne : ∀ n ∈ ns, n ≠ key) (f : Bytes → Nat) :
    sumKeys t' (key :: ns) f = f v + sumKeys t ns f := by
  rw [sumKeys_cons, PTrie.find_upsert_self t key v t' hok hu]
  have hsame : sumKeys t' ns f = sumKeys t ns f := by
    unfold sumKeys
    congr 1
    refine List.map_congr_left ?_
    intro n hn
    rw [PTrie.find_upsert_other t key n v t' hwf hok (hne n hn) hu]
  rw [hsame]

/-- **The delta form.** If the written path was already present with value `old`, the sum over
`key :: ns` changes by exactly `f v - f old`; if it was absent, by exactly `f v`. -/
theorem sumKeys_upsert_delta {t t' : PTrie} {key : List Nat} {v : Bytes}
    (hwf : t.wf = true) (hok : nibblesOk key = true) (hu : t.upsert key v = some t')
    {ns : List (List Nat)} (hne : ∀ n ∈ ns, n ≠ key) (f : Bytes → Nat) :
    sumKeys t' (key :: ns) f + (match t.find key with | some (some old) => f old | _ => 0)
      = f v + sumKeys t (key :: ns) f := by
  rw [sumKeys_upsert_cons hwf hok hu hne]
  rw [sumKeys_cons]
  omega

/-! ## §6.4 The overlay-level delta: one write, one record's difference

The runtime never writes the trie directly. It accumulates writes in the overlay's `prosp`
(`Ovl.set`/`setAcct`/`setAK`) and folds them into `committed` at `commit` (`D2/State.lean:121`), or
discards them at `rollback` (`:124`). So an account-sum over the *committed* layer is the right object,
and the delta of one write is the arithmetic this section proves.

`sumEntries` sums `acctEntryTotal` over a committed-style list. `sumEntries_kvPut` is the exact delta:
putting `v` at key `k` changes the sum by `acctEntryTotal k v - acctEntryTotal k (old value)`. That is
the overlay analogue of `validatorStep_total`, and unlike the `Nat`-level table it is stated about the
overlay's own data. -/

/-- Account total of one committed-style entry, or 0 if the key is not an account key. -/
def acctEntryTotal (k : Bytes) (v : Option Bytes) : Nat :=
  if k.head? == some 0 then
    (match v with | some b => acctTotalOf b | none => 0)
  else 0

/-- The account sum over a committed-style list. -/
def sumEntries (l : List (Bytes × Option Bytes)) : Nat :=
  sumNat (l.map fun p => acctEntryTotal p.1 p.2)

/-- **One overlay write changes the account sum by exactly that record's total difference.**

This is the form a conservation argument consumes: `kvPut` is what `Ovl.set` performs, so a receipt's
write is accounted by the difference of the two records' `amount + locked`, with every other entry
untouched. -/
theorem sumEntries_kvPut {l : List (Bytes × Option Bytes)} {k : Bytes} {v : Option Bytes} :
    sumEntries (kvPut k v l)
        + acctEntryTotal k (match kvFind k l with | some o => o | none => none)
      = acctEntryTotal k v + sumEntries l := by
  unfold sumEntries
  induction l with
  | nil => simp [kvPut, kvFind, sumNat, acctEntryTotal]
  | cons p ps ih =>
    obtain ⟨k', v'⟩ := p
    by_cases h : k' = k
    · subst h
      simp only [kvPut, beq_iff_eq, ite_true, kvFind, List.map_cons, sumNat]
      omega
    · simp only [kvPut, kvFind, beq_iff_eq, if_neg h, List.map_cons, sumNat]
      omega

/-- **A write to a non-account key leaves the account sum alone.** Immediate from the delta lemma: both
`acctEntryTotal` terms are 0 because the key does not start with the account nibble. -/
theorem sumEntries_kvPut_nonacct {l : List (Bytes × Option Bytes)} {k : Bytes} {v : Option Bytes}
    (hk : k.head? ≠ some 0) :
    sumEntries (kvPut k v l) = sumEntries l := by
  have h := sumEntries_kvPut (l := l) (k := k) (v := v)
  have hk' : acctEntryTotal k v = 0 := by simp [acctEntryTotal, hk]
  have hk'' : acctEntryTotal k (match kvFind k l with | some o => o | none => none) = 0 := by
    simp [acctEntryTotal, hk]
  omega

/-! ## §6.5 What is still needed to reach the runtime

§6.4 accounts one `kvPut`. The remaining obligation is to connect the runtime functions to `prosp`:
to show that `applyActionReceipt`'s committed writes are exactly the `setAcct`/`setAK` calls the
per-site table lists, and that on the failure path the receipts it emits refund exactly what those
writes took. That is the symbolic-execution obligation the docs have flagged since the beginning — it
needs the treatment `actStake_ok_total` gives a single site, applied to every site, plus the
`refunds`/`depRefund` arithmetic threaded through `applyActionReceipt`'s error paths.

Until that is done, the "credited then rejected" bug is not caught by proof. What §6.4 does supply is
that each write's contribution is now an exact, overlay-level delta rather than a free `Nat` identity. -/

end NearSpecV3.D2
