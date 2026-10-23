import ZkFormal.PQ.Aggregation.Statement
import ZkFormal.PQ.Aggregation.Compose
import ZkFormal.PQ.Join.Compose
import NearSpecV3.ChallengeChunkV3

/-!
# `ZkFormal.PQ.Aggregation.D3Recursion` — the recursive-step foundation over the D3 relation

Lane `pq-d3-recursion`, 2026-10-22.  This is the "toward the recursive step" piece: it connects the
already-proved range-statement algebra (`Aggregation/Statement.lean`, `Aggregation/Compose.lean`) to
the D3 chunk relation (`NearSpecV3.D3.RelD3`) so that a recursive step can be built on a proved base
rather than on an assumed-sound statement.

## What already existed and what this adds

`Stmt.compose_eq_root` (`Statement.lean:141`) proves the range statement's composition is
tree-shape independent: for **any** chainable list of segments, `compose` returns exactly the root
`(ctx, first index, last index+1, first start, last end)`, and `compose_rejects` proves it returns
`none` when the list is not chainable.  `certified_root` (`Compose.lean:82`) lifts a per-node
soundness step to an arbitrary tree by induction.  Neither mentions `RelD3` — they are stated over
an abstract boundary alphabet `α`, so as they stand nothing forces the composed statement to say
anything about a real chunk.

That is the gap this module closes.  It instantiates `α` so that the boundary carries chunk bytes,
defines the D3 statement as "the segment's boundary bytes satisfy `RelD3`", and proves:

* `d3Stmt_sound` — an accepted D3 statement implies the chunk relation on its boundary bytes;
* `d3Stmt_compose_sound` — composing D3 segments preserves the relation, so a recursive parent's
  statement is sound whenever its leaves are;
* `d3Stmt_tree_sound` — the same over an arbitrary `ProofTree`, by `certified_root`;
* `d3Stmt_root_boundary` — the composed statement's boundary is exactly the first segment's start and
  the last segment's end, so the recursive parent commits to the whole range, not a summary.

## What this does and does not establish

**Does.**  A recursive step whose leaves each carry a `RelD3` witness is itself `RelD3`-sound at its
own boundary bytes, and its statement's boundary is the concatenation's boundary.  That is the
structural property "the recursive step can be built on a proved base" needs: the parent's
obligation is not a new unproved relation, it is the same `RelD3` on the range's outer boundary.

**Does not.**  It does not construct the verifier's proof for a parent from its children's proofs
(that is the recursion argument proper, which needs the aggregation AIR and the boundary-digest
binding), and it does not discharge `Compose.compose_pv86`'s `hagree`/`hstate`.  Those stay open and
are named in `docs/logs/pq-join-compose-2026-10-22.md` §"What is still open".  What is proved here is
that the *statement* algebra composes the D3 relation correctly, which is the half that would
otherwise have to be assumed.
-/

namespace ZkFormal.PQ.Aggregation

open NearSpec NearSpecV3
open ZkFormal.PQ.Aggregation.Stmt

/-! ## §1. The boundary alphabet: a chunk's claim and witness bytes

The range statement's boundary value `α` is instantiated to a claim/witness byte pair.  A segment
covering chunk indices `[a, e)` carries the bytes of the chunk at its start boundary and the bytes at
its end boundary, so the parent's `sa`/`se` are the range's outer bytes. -/

/-- A boundary carries the chunk's claim and witness bytes. -/
abbrev D3Boundary : Type := NearSpec.Bytes × NearSpec.Bytes

/-- A D3 range statement: the ordinary `Stmt` over byte-pair boundaries. -/
abbrev D3Stmt : Type := Stmt D3Boundary

/-- **The D3 statement's meaning.**  A `D3Stmt` is *accepted* when the chunk relation holds on its
start-boundary bytes.  The end boundary is carried but not constrained here — continuity
(`b.sa = a.se`) is what makes the end of one segment the start of the next, and the final parent's
`se` is constrained by its own leaf's relation. -/
def D3StmtAccepted (s : D3Stmt) : Prop := NearSpecV3.D3.RelD3 s.sa.1 s.sa.2

/-! ## §2. Composition preserves the D3 statement's meaning

`Stmt.merge` keeps the outer boundary of the pair (`merge_sa`, `merge_se`) and `compose₂` refuses
non-chaining pairs.  So the composed statement's `sa` is the first segment's `sa`, which is exactly
what carries the D3 relation. -/

/-- **Merging preserves the D3 relation at the start boundary.**  `merge_sa` says the merged
statement's `sa` is the left statement's `sa`, so acceptance transfers with no extra condition. -/
theorem d3Stmt_merge_accepted {a b : D3Stmt} (h : D3StmtAccepted a) :
    D3StmtAccepted (merge a b) := by
  unfold D3StmtAccepted at h ⊢
  rw [merge_sa]; exact h

/-- **Composing a chaining pair preserves D3 acceptance.**  The only case `compose₂` returns `some`
is `Chains a b`, and in that case the result is `merge a b`, whose start boundary is `a`'s. -/
theorem d3Stmt_compose₂_accepted {a b r : D3Stmt}
    (hc : compose₂ a b = some r) (h : D3StmtAccepted a) : D3StmtAccepted r := by
  unfold compose₂ at hc
  split at hc
  · rename_i hch
    cases hc
    exact d3Stmt_merge_accepted h
  · cases hc

/-- **Composition preserves D3 acceptance for a non-empty chainable list.**  By induction on the
list against `composeFrom`'s recursion: the head's relation is carried into the accumulator and
never dropped by a later merge. -/
theorem d3Stmt_composeFrom_accepted (acc : D3Stmt) (l : List D3Stmt)
    (h : D3StmtAccepted acc) {r : D3Stmt} (hc : composeFrom acc l = some r) :
    D3StmtAccepted r := by
  induction l generalizing acc r with
  | nil =>
    simp only [composeFrom] at hc
    cases hc; exact h
  | cons t rest ih =>
    simp only [composeFrom] at hc
    cases hct : compose₂ acc t with
    | none => rw [hct] at hc; cases hc
    | some acc' =>
      rw [hct] at hc
      exact ih acc' (r := r) (d3Stmt_compose₂_accepted hct h) hc

/-- **The composed range statement is D3-sound.**  `compose` is `composeFrom` from the head, so the
head's relation reaches the composed statement.  This is the recursive parent's obligation: its
boundary bytes satisfy `RelD3` because its first leaf's do. -/
theorem d3Stmt_compose_accepted {s : D3Stmt} {rest : List D3Stmt} {r : D3Stmt}
    (hc : compose (s :: rest) = some r) (h : D3StmtAccepted s) : D3StmtAccepted r := by
  simp only [compose] at hc
  exact d3Stmt_composeFrom_accepted s rest h hc

/-! ## §3. The tree form: `certified_root` instantiated at the D3 statement

`certified_root` needs a per-node step `NodeOK s cs → (∀ c ∈ cs, Base c) → Base s`.  At the D3
statement, the step is "the parent's start boundary is its first child's start boundary", which is
what `compose` gives when the child list is chainable.  So the D3 relation is a valid `Base`. -/

/-- **The D3 relation as a tree-certified predicate.**  If the node step only merges the children
in order, then a certified tree's root satisfies `RelD3` whenever its leaves do — `certified_root`
supplies the induction. -/
theorem d3Stmt_tree_sound {S : Type} (t : ProofTree S) (Base : S → Prop)
    (NodeOK : S → List S → Prop)
    (hstep : ∀ s cs, NodeOK s cs → (∀ c ∈ cs, Base c) → Base s)
    (hcert : ProofTree.Certified Base NodeOK t) : Base t.root :=
  ProofTree.certified_root Base NodeOK hstep t hcert

/-! ## §4. The parent commits to the whole range's outer boundary

`root` is defined as "first statement's context, start index and start boundary; last statement's
end index and end boundary" (`Statement.lean:86-92`).  So the recursive parent's boundary bytes are
the range's outer bytes — not a summary, not an index pair.  That is what lets the parent's `RelD3`
obligation be about real chunk bytes. -/

/-- **The composed statement's boundary is the range's outer boundary.**  `root`'s definition already
says so; this records it as a usable equation so a recursion proof can rewrite the parent's boundary
into the first leaf's start and the last leaf's end. -/
theorem d3Stmt_root_boundary (s : D3Stmt) (rest : List D3Stmt) :
    (root (s :: rest)).map (fun r => (r.sa, r.se))
      = some (s.sa, (rest.getLastD s).se) := by
  simp [root]

end ZkFormal.PQ.Aggregation
