import NearSpecV3.ChunkValidationD1

/-! Proof notes (the statement and route this lemma was proved against):

Presentation identity at the header comparison. `OutD1.leaf ⟨o, .value, []⟩ = sha256 (u32 2 ++ o.id ++ sha256 (OutD1.partialEncode …))` and `Outcome.leaf o = sha256 (u32 2 ++ o.id ++ sha256 (Outcome.partialEncode o))`; the two partial encodings differ only by associativity of `++` (`OStatus.encode .value` is `[2] ++ u32 0` with `u32 : Nat → Bytes`). Proof sketch: `theorem pe (o) : OutD1.partialEncode {o := o, status := OStatus.value} = Outcome.partialEncode o := by unfold OutD1.partialEncode Outcome.partialEncode; simp only [OStatus.encode, List.append_assoc]` then `theorem leaf_value (o) : OutD1.leaf ⟨o, OStatus.value, []⟩ = Outcome.leaf o := by unfold OutD1.leaf Outcome.leaf; rw [pe]`, then `outcomeRoot_map_value` by `unfold outcomeRootD1 outcomeRoot; congr 1; induction os with | nil => rfl | cons a t ih => simp only [List.map_cons, ih, leaf_value]`. It is consumed by the root lockstep at the D1-only step `check (H.prevOutcomeRoot == outcomeRootD1 out.outcomes)`. Note that `Work.Runtime.EmptyTxs` also mentions `OStatus.value`, so the vocabulary is shared.
-/

namespace Work.Root

/-! ## The leaf presentation identity

`OutD1.leaf {o := o, status := OStatus.value, logs := []}` and `Outcome.leaf o` are both
`sha256 (u32 2 ++ o.id ++ sha256 partial)`, and the two partial encodings are the *same* byte
string: `OutD1.partialEncode` ends with `OStatus.encode .value = [2] ++ u32 0` while
`Outcome.partialEncode` ends with the literal `[2] ++ u32 0`; they differ only by the
parenthesisation of the final `++` (which `List.append_assoc` repairs).  Consequently the
leaf lists `os.map OutD1.leaf` and `os.map Outcome.leaf` are *equal as lists*, and the two
merkle roots (`merkleRoot` is a function of the leaf list) coincide. -/
theorem Outcome (os : List NearSpec.Outcome) :
    NearSpecV3.outcomeRootD1 (os.map (fun o => { o := o, status := NearSpecV3.OStatus.value })) =
      NearSpec.outcomeRoot os := by
  -- The two `PartialExecutionOutcome` encodings agree: `OStatus.encode .value = [2] ++ u32 0`
  -- is exactly the literal tail of `Outcome.partialEncode`, modulo `++` associativity.
  have pe : ∀ o : NearSpec.Outcome,
      NearSpecV3.OutD1.partialEncode { o := o, status := NearSpecV3.OStatus.value } =
        NearSpec.Outcome.partialEncode o := by
    intro o
    unfold NearSpecV3.OutD1.partialEncode NearSpec.Outcome.partialEncode
    simp only [NearSpecV3.OStatus.encode, List.append_assoc]
  -- Hence the leaves agree (both have `logs = []`).
  have leaf_value : ∀ o : NearSpec.Outcome,
      NearSpecV3.OutD1.leaf ⟨o, NearSpecV3.OStatus.value, []⟩ = NearSpec.Outcome.leaf o := by
    intro o
    unfold NearSpecV3.OutD1.leaf NearSpec.Outcome.leaf
    rw [pe o]
  -- The two roots are `merkleRoot` applied to the two leaf lists, which are equal.
  unfold NearSpecV3.outcomeRootD1 NearSpec.outcomeRoot
  congr 1
  induction os with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, ih, leaf_value]

end Work.Root
