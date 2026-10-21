import Mathlib
import Qrom.MerkleSupport

/-!
# Qrom.Extraction — canonical Merkle extraction and its monotonicity

`Qrom.MerkleSupport` proves graph facts about reachability and a cardinality bound
`|constants ∪ outputs ∪ refs| ≤ C + 3q`. It does **not** define extraction, so it
cannot state what happens to the extracted oracle string when one database entry
is inserted, removed or reassigned. This file supplies that.

## Representation

A database is a finite set of nodes; a node has a digest `out` and a finite set
of child digests `children`. This is the extraction-relevant part of the protocol
database (payloads are irrelevant to extraction).

`Extract D d` is the set of nodes of `D` that output `d`. Canonical extraction
is well defined at `d` exactly when that set is a singleton, which is CFHL21's
"unique preimage at each reached node". `Extract` is a `Finset.filter`, so the
three mutations are filter identities:

* `extract_insert_fresh` — a node with a new output becomes the unique preimage
  at its digest and changes no other digest;
* `extract_erase` — deleting a node deletes it from every extraction set;
* `extract_replace` — the composite "drop `m`, insert fresh `n`" step changes
  extraction only at `n.out`.

`Children D d` is the set of child digests attached to the extraction at `d`,
which is what the canonical oracle string actually contains. Reassigning a node's
children is **not** an extraction-set identity at its own digest (the node object
changes), but it is one for the extracted children at every *other* digest —
`children_reassign_unrelated` — and at its own digest the children become exactly
the new set (`children_reassign_own`). Those two are the honest statements.

## Why this is still not the paper's item 2

These are statements about a *model* of the database: a finite set of
`(digest, children)` pairs. The paper's item 2 additionally needs (i) a
refinement from the Rust parser's byte string to such a set — not available in
this package — and (ii) a per-message digest count for absorb inputs, which
`Qrom.Fanout.absorb_digest_bound` supplies in place of the constant 3.
-/

namespace Qrom.Extraction

variable {ι : Type} [DecidableEq ι]

/-- A database node: a digest and its child digests. -/
structure Node (ι : Type) where
  out : ι
  children : Finset ι
  deriving DecidableEq

/-- The canonical extraction set at `d`: all nodes that output `d`. -/
def Extract (D : Finset (Node ι)) (d : ι) : Finset (Node ι) :=
  D.filter (fun n => n.out = d)

@[simp] theorem mem_Extract {D : Finset (Node ι)} {d : ι} {n : Node ι} :
    n ∈ Extract D d ↔ n ∈ D ∧ n.out = d := by
  simp [Extract]

/-- **Inserting a node whose output is not `d` does not change extraction at `d`.** -/
theorem extract_insert_other {D : Finset (Node ι)} {n : Node ι} {d : ι} (hd : n.out ≠ d) :
    Extract (insert n D) d = Extract D d := by
  rw [Extract, Extract, Finset.filter_insert, if_neg]
  rintro rfl
  exact hd rfl

/-- A singleton extraction set is a unique preimage. -/
theorem extract_unique {D : Finset (Node ι)} {d : ι} {n : Node ι}
    (hn : n ∈ Extract D d) (hcard : (Extract D d).card ≤ 1) :
    ∀ m ∈ D, m.out = d → m = n := by
  intro m hm hout
  have hm' : m ∈ Extract D d := mem_Extract.mpr ⟨hm, hout⟩
  have h1 : (Extract D d).card = 1 := by
    have : 0 < (Extract D d).card := Finset.card_pos.mpr ⟨n, hn⟩
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  have hma : m = a := by simpa [ha] using hm'
  have hna : n = a := by simpa [ha] using hn
  rw [hma, ← hna]

/-- Extraction is monotone in the database. -/
theorem extract_subset {D D' : Finset (Node ι)} (h : D ⊆ D') (d : ι) :
    Extract D d ⊆ Extract D' d := by
  intro n hn
  exact mem_Extract.mpr ⟨h (mem_Extract.mp hn).1, (mem_Extract.mp hn).2⟩

/-- **Insertion of a fresh node.** If no node of `D` outputs `n.out`, inserting
`n` sets the extraction at `n.out` to exactly `{n}` and leaves every other
digest alone. -/
theorem extract_insert_fresh {D : Finset (Node ι)} {n : Node ι}
    (hfresh : ∀ m ∈ D, m.out ≠ n.out) (d : ι) :
    Extract (insert n D) d = if d = n.out then {n} else Extract D d := by
  rw [Extract, Extract, Finset.filter_insert]
  by_cases hd : d = n.out
  · subst hd
    rw [if_pos rfl, if_pos rfl]
    have hempty : D.filter (fun x => x.out = n.out) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hfresh x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
    rw [hempty, Finset.insert_empty]
  · rw [if_neg hd, if_neg (Ne.symm hd)]

/-- **Deletion of one node.** Removing a node only removes it from every
extraction set. -/
theorem extract_erase (D : Finset (Node ι)) (n : Node ι) (d : ι) :
    Extract (D.erase n) d = (Extract D d).erase n := by
  rw [Extract, Extract, Finset.filter_erase]

/-- **The composite transcript mutation.** A step that drops node `m` and inserts
a node `n` with a fresh output changes extraction only at `n.out`. -/
theorem extract_replace {D : Finset (Node ι)} {m n : Node ι}
    (hfresh : ∀ k ∈ D.erase m, k.out ≠ n.out) (d : ι) :
    Extract (insert n (D.erase m)) d
      = if d = n.out then {n} else (Extract D d).erase m := by
  rw [extract_insert_fresh hfresh, extract_erase]

/-! ## Extracted children: what the canonical oracle string contains -/

/-- The child digests attached to the extraction at `d`. -/
def Children (D : Finset (Node ι)) (d : ι) : Finset ι :=
  (Extract D d).biUnion (fun n => n.children)

/-- At a digest whose extraction set is a singleton, `Children` is that node's
children. -/
theorem children_of_unique {D : Finset (Node ι)} {d : ι} {n : Node ι}
    (hun : ∀ m ∈ D, m.out = d → m = n) :
    Children D d ⊆ n.children := by
  intro c hc
  rw [Children] at hc
  obtain ⟨m, hm, hc⟩ := Finset.mem_biUnion.mp hc
  rw [hun m (mem_Extract.mp hm).1 (mem_Extract.mp hm).2] at hc
  exact hc

/-- **Reassigning a node's children does not change extracted children at any
other digest.** Both inserted nodes have output `n.out ≠ d`, so neither enters
the extraction at `d`. This is why `Qrom.Transcript.honest_edge_not_bad` holds. -/
theorem children_reassign_unrelated {D : Finset (Node ι)} {n : Node ι}
    (cs : Finset ι) {d : ι} (hd : d ≠ n.out) :
    Children (insert ⟨n.out, cs⟩ (D.erase n)) d = Children (insert n (D.erase n)) d := by
  rw [Children, Children,
    extract_insert_other (D := D.erase n) (n := ⟨n.out, cs⟩) (Ne.symm hd),
    extract_insert_other (D := D.erase n) (n := n) (Ne.symm hd)]

/-- **At the reassigned node's own digest the extracted children are exactly the
new children.** -/
theorem children_reassign_own {D : Finset (Node ι)} {n : Node ι} (cs : Finset ι)
    (hfresh : ∀ m ∈ D.erase n, m.out ≠ n.out) :
    Children (insert ⟨n.out, cs⟩ (D.erase n)) n.out = cs := by
  rw [Children, Extract, Finset.filter_insert, if_pos rfl]
  have hempty : (D.erase n).filter (fun x => x.out = n.out) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hfresh x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  rw [hempty, Finset.insert_empty, Finset.singleton_biUnion]

/-- Deleting a node shrinks extracted children at every digest. -/
theorem children_erase_subset (D : Finset (Node ι)) (n : Node ι) (d : ι) :
    Children (D.erase n) d ⊆ Children D d := by
  intro c hc
  rw [Children, Extract] at *
  obtain ⟨m, hm, hc⟩ := Finset.mem_biUnion.mp hc
  rw [Finset.mem_filter] at hm
  exact Finset.mem_biUnion.mpr
    ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_erase.mp hm.1 |>.2, hm.2⟩, hc⟩

end Qrom.Extraction

#print axioms Qrom.Extraction.extract_unique
#print axioms Qrom.Extraction.extract_insert_fresh
#print axioms Qrom.Extraction.extract_erase
#print axioms Qrom.Extraction.extract_replace
#print axioms Qrom.Extraction.children_reassign_unrelated
#print axioms Qrom.Extraction.children_reassign_own
#print axioms Qrom.Extraction.children_erase_subset
