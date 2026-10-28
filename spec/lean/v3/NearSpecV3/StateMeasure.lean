import NearSpecV3.D2.TrieProps
import NearSpecV3.D2.State
import NearSpecV3.SupplyRuntime
import NearSpec.TrieUpsertProofs

/-!
# §6 A state measure over the overlay

`NearSpecV3/SupplyRuntime.lean` gives the arithmetic of each balance write, but states it about bare
`Nat`s: `refundStep_total {amount dep : Nat}` says nothing about the overlay the runtime actually
builds. This file defines a measure on `PTrie` so that arithmetic can be composed into a statement
about real state.

`PTrie.allKeys` enumerates the keys of a fully revealed trie as **nibble paths**, and
`PTrie.allKeys_sound` / `PTrie.allKeys_complete` (`D2/TrieProps.lean:326,506`) prove the enumeration is
exactly the set of keys with a value. §6.1 restates that pair at `acc = []`; §6.2 builds the measure.

Working in nibble space matters: the enumeration returns paths that need not be `nibbles` of any byte
string (a revealed node may split a byte), so going through `packNibbles`/`nibbles` would need a
well-formedness side condition the runtime does not carry. Reading values with `find n` on the path
itself avoids that round trip.

## Scope

The measure is over the **committed** state (the trie), because that is what `commit`/`rollback`
(`D2/Receipts.lean:162`) decides between — which is exactly the fork a "credited then rejected" bug
would exploit. `burnt` is carried as an argument: `tokensBurnt` lives in the receipt state, not the
trie.
-/

namespace NearSpec

/-! ## §6.1 The enumeration is exactly the set of keys with a value -/

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

/-! ## §6.2 Sums over the enumerated keys -/

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

/-- The values stored at the paths in `ns` whose first nibble is `k`. Isolating "which keys match,
and what do they hold" from "what is the sum" makes value congruence a plain rewrite. -/
def headVals (t : PTrie) (k : Nat) (ns : List (List Nat)) : List Bytes :=
  ns.filterMap fun n =>
    if n.head? == some k then
      (match t.find n with | some (some v) => some v | _ => none)
    else none

/-- **Equal values on matching keys give equal `headVals`.** This is the lemma that makes a write to a
*non*-matching key provably irrelevant to the sum. -/
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

/-- **The state measure**: NEAR in accounts, plus NEAR against gas keys, plus burnt tokens. -/
def stateTotal (t : PTrie) (burnt : Nat) : Nat := acctSumOf t + akSumOf t + burnt

/-! ## §6.3 Congruence: the measure only depends on the account keys -/

/-- `sumNat` of equal mapped lists is equal. -/
theorem sumNat_map_congr {l l' : List Bytes} {f : Bytes → Nat} (h : l = l') :
    sumNat (l.map f) = sumNat (l'.map f) := by rw [h]

/-- **Two tries that agree on every account key have the same account sum**, when their enumerations
succeed and agree on which keys exist. -/
theorem acctSumOf_congr {t t' : PTrie} {ns : List (List Nat)}
    (h : t.allKeys [] = some ns) (h' : t'.allKeys [] = some ns)
    (hf : ∀ n ∈ ns, n.head? = some 0 → t.find n = t'.find n) :
    acctSumOf t = acctSumOf t' := by
  unfold acctSumOf
  simp only [h, h', headVals_congr hf]

/-- **A write that preserves every account key's value preserves the account sum.** -/
theorem acctSumOf_eq_of_find_eq {t t' : PTrie} {ns : List (List Nat)}
    (h : t.allKeys [] = some ns) (h' : t'.allKeys [] = some ns)
    (hf : ∀ n ∈ ns, t.find n = t'.find n) :
    acctSumOf t = acctSumOf t' :=
  acctSumOf_congr h h' (fun n hn _ => hf n hn)

/-! ## §6.4 The measure is sensitive to account values

§6.3 shows the measure *cannot* change when account values do not. That alone would also hold for a
degenerate measure that ignored values entirely, so this section records the other direction: the
decoded total of a record determines its contribution, so two records with different totals contribute
differently. Without this, a "measure" that always returned 0 would satisfy §6.3 and the refund bug
would be invisible. -/

/-- **Different account totals contribute different amounts.** A measure that ignored values would fail
this. -/
theorem acctTotalOf_ne {v v' : Bytes} {x x' : Acct}
    (h : decodeAcct v = some x) (h' : decodeAcct v' = some x')
    (ht : x.total ≠ x'.total) : acctTotalOf v ≠ acctTotalOf v' := by
  unfold acctTotalOf
  rw [h, h']
  exact ht

/-- **The measure splits over a listed account.** Appending one account's value to the list adds
exactly that record's total, which is the form a conservation proof consumes at a write site. -/
theorem acctSum_cons (v : Bytes) (vs : List Bytes) :
    sumNat ((v :: vs).map acctTotalOf) = acctTotalOf v + sumNat (vs.map acctTotalOf) := by
  simp [sumNat]

/-! ## §6.5 What is still needed to close the runtime link

The measure is now defined and §6.3/§6.4 say it is both *insensitive to non-account writes* and
*sensitive to account values*. Closing "the runtime conserves the measure" needs one more ingredient:

**Enumeration stability under `upsert`.** `find_upsert_self` / `find_upsert_other`
(`NearSpec/TrieUpsertProofs.lean:381,467`) describe `find` after a write, but `acctSumOf` sums over
`allKeys`, so the delta statement needs

  `t.upsert key v = some t' → t'.allKeys [] = t.allKeys []`

i.e. that a write changes no key's *presence* — only one key's value. That is not proved here, and it
is not available in `TrieProps`: `allKeys_sound`/`allKeys_complete` pin down *which* keys a given
enumeration returns, but not how the enumeration changes across an `upsert`.

With that stability lemma, `acctSumOf_upsert_acct` would follow immediately: the key sets agree, and
`find_upsert_other` + `find_upsert_self` give value agreement everywhere except the written key. Then
composing over `applyChange`/`applyChanges` (`D2/State.lean:146,154`) and through
`applyActionReceipt`'s commit/rollback fork (`D2/Receipts.lean:162`) would yield the conservation
statement that catches the credited-then-rejected bug.

This is the honest boundary of the current work: the measure exists and is provably sensitive to
exactly what matters, but the runtime-conservation theorem is not yet derived from it. -/

end NearSpecV3.D2
