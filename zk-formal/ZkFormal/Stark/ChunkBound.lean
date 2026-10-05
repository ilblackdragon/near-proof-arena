import ZkFormal.Stark.L2Facts
import ZkFormal.Stark.QueryBound

/-!
# ZkFormal.Stark.ChunkBound — `QUERY`-chunk budget of the compiled verifier

`chunk_queryBound : ChunkQueryBoundStmt`: `Bcs.compile V` makes at most
`V.numChunks` queries that `Bcs.chunkDec` decodes.  Every other query is a
wide-hash half `tag :: 1/2 :: m` with `tag ∈ {0x00,…,0x04}`, which
`chunkDec` rejects (it needs first byte `tagQuery = 0x05`).
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Stark

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Air

/-- Every query of `oa` has `QUERY`-chunk weight zero. -/
inductive ZQ {α : Type} : OracleComp hashSpec α → Prop
  | pure (a : α) : ZQ (.pure a)
  | query (q : Bytes) (k : Bytes → OracleComp hashSpec α) :
      qWeight Bcs.chunkDec q = 0 → (∀ r, ZQ (k r)) → ZQ (.query q k)

namespace ZQ

theorem bind {α β : Type} {oa : OracleComp hashSpec α} {f : α → OracleComp hashSpec β}
    (h : ZQ oa) (hf : ∀ r, ZQ (f r)) : ZQ (OracleComp.bind oa f) := by
  induction h with
  | pure a => exact hf a
  | query q k hq _ ih => exact .query q _ hq ih

theorem toQB {α : Type} {oa : OracleComp hashSpec α} (h : ZQ oa) :
    OracleComp.QueryBound (qWeight Bcs.chunkDec) oa 0 := by
  induction h with
  | pure a => exact .pure a 0
  | query q k hq _ ih =>
    exact OracleComp.QueryBound.query (spec := hashSpec) q k 0 (by rw [hq]; exact Nat.le_refl 0) fun r => by
      rw [hq]; exact ih r

end ZQ

theorem WH_zq (tag : UInt8) (htag : tag ≠ Bcs.tagQuery) (m : Bytes) : ZQ (WH tag m) := by
  have hw : ∀ j : UInt8, qWeight Bcs.chunkDec (tag :: j :: m) = 0 := by
    intro j
    simp only [qWeight, Bcs.chunkDec, htag, false_and, ite_false, Option.isSome_none]
    rfl
  unfold WH H OracleComp.ask
  exact .query _ _ (hw 1) fun a => .query _ _ (hw 2) fun b => .pure _

theorem tagAbs_ne : tagAbs ≠ Bcs.tagQuery := by decide
theorem tagChal_ne : tagChal ≠ Bcs.tagQuery := by decide
theorem tagInit_ne : tagInit ≠ Bcs.tagQuery := by decide
theorem tagLeaf_ne : tagLeaf ≠ Bcs.tagQuery := by decide
theorem tagNode_ne : tagNode ≠ Bcs.tagQuery := by decide

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

theorem chain_zq (d : Bytes) (ps : List (PSlot K)) : ZQ (chain (F := F) d ps) := by
  induction ps generalizing d with
  | nil => exact .pure _
  | cons p ps ih =>
    cases p with
    | msg vs raw =>
      simp only [chain]
      exact (WH_zq _ tagAbs_ne _).bind fun d' => (ih d').bind fun _ => .pure _
    | chal ood =>
      simp only [chain]
      exact (WH_zq _ tagChal_ne _).bind fun d' => (ih d').bind fun _ => .pure _

theorem qWeight_le_one (x : Bytes) : qWeight Bcs.chunkDec x ≤ 1 := by
  unfold qWeight; split <;> omega

theorem H_chunk {β : Type} (m : Bytes) (f : Bytes → OracleComp hashSpec β) :
    OracleComp.QueryBound (qWeight Bcs.chunkDec) (OracleComp.bind (H m) fun y => f y) 1 ↔
      ∀ y, OracleComp.QueryBound (qWeight Bcs.chunkDec) (f y) (1 - qWeight Bcs.chunkDec m) := by
  constructor
  · intro h; cases h with | query _ _ _ _ hk => exact hk
  · intro hk; exact .query (spec := hashSpec) m _ 1 (qWeight_le_one m) hk

theorem queryAnswers_chunk (d : Bytes) (n : Nat) :
    OracleComp.QueryBound (qWeight Bcs.chunkDec) (queryAnswers d n) n := by
  induction n with
  | zero => exact .pure _ _
  | succ n ih =>
    simp only [queryAnswers]
    refine ZkFormal.QueryBound.bind (b := 1) ih fun ys => ?_
    exact (H_chunk _ _).2 fun y => .pure _ _

theorem mpLeaves_zq (n : Nat) (ws : List Nat) (xs : List Nat) (r : Bytes) :
    ZQ (mpLeaves (F := F) n ws xs r) := by
  induction xs generalizing r with
  | nil => exact .pure _
  | cons x xs ih =>
    simp only [mpLeaves]
    split
    · exact .pure _
    · refine (WH_zq _ tagLeaf_ne _).bind fun h => (ih _).bind fun res => ?_
      rcases res with _ | ⟨hs, op, r''⟩ <;> exact .pure _

theorem mpNode_zq (lvl : Nat) (ws : List Nat) (x : Nat) (lft rgt r : Bytes) :
    ZQ (mpNode (F := F) lvl ws x lft rgt r) := by
  simp only [mpNode]
  split
  · exact .pure _
  · exact (WH_zq _ tagNode_ne _).bind fun _ => .pure _

theorem mpUp_finish_zq (k lvl : Nat) (ws : List Nat) (x : Nat) (lft rgt r1 : Bytes)
    (recur : Bytes → OracleComp hashSpec (Option (List (Nat × Bytes) × Opened F × Bytes)))
    (hrec : ∀ r2, ZQ (recur r2)) :
    ZQ (OracleComp.bind (mpNode (F := F) lvl ws (x / 2) lft rgt r1) fun
        | none => .pure none
        | some (nh, rows?, r2) =>
          OracleComp.bind (recur r2) fun
            | none => .pure none
            | some (hs, op, r3) =>
              .pure (some (nh :: hs, (match rows? with
                | some rows => ((k, x / 2), rows) :: op
                | none => op), r3))) := by
  refine (mpNode_zq _ _ _ _ _ _).bind fun res => ?_
  rcases res with _ | ⟨nh, rows?, r2⟩
  · exact .pure _
  · refine (hrec r2).bind fun res => ?_
    rcases res with _ | ⟨hs, op, r3⟩ <;> exact .pure _

theorem mpUp_zq (k lvl : Nat) (ws : List Nat) :
    ∀ (N : Nat) (nodes : List (Nat × Bytes)) (r : Bytes), nodes.length ≤ N →
      ZQ (mpUp (F := F) k lvl ws nodes r) := by
  intro N
  induction N with
  | zero =>
    intro nodes r h
    match nodes with
    | [] => exact .pure _
  | succ N ih =>
    intro nodes r hN
    match nodes with
    | [] => exact .pure _
    | (x, h) :: tl =>
      match tl with
      | (x', h') :: rest =>
        simp only [mpUp]
        have hr : rest.length ≤ N := by simp at hN; omega
        have hr' : ((x', h') :: rest).length ≤ N := by simp at hN; omega
        split
        · exact mpUp_finish_zq k lvl ws x h h' r _ fun r2 => ih rest r2 hr
        · split
          · exact .pure _
          · split
            · exact mpUp_finish_zq k lvl ws x h _ _ _ fun r2 => ih _ r2 hr'
            · exact mpUp_finish_zq k lvl ws x _ h _ _ fun r2 => ih _ r2 hr'
      | [] =>
        simp only [mpUp]
        split
        · exact .pure _
        · split
          · exact mpUp_finish_zq k lvl ws x h _ _ _ fun r2 => ih [] r2 (by simp)
          · exact mpUp_finish_zq k lvl ws x _ h _ _ fun r2 => ih [] r2 (by simp)

theorem mpLevels_zq (mats : List (Nat × Nat)) (n : Nat) :
    ∀ (k : Nat) (nodes : List (Nat × Bytes)) (r : Bytes), ZQ (mpLevels (F := F) mats n k nodes r) := by
  intro k
  induction k with
  | zero =>
    intro nodes r
    simp only [mpLevels]
    split <;> exact .pure _
  | succ k ih =>
    intro nodes r
    simp only [mpLevels]
    refine (mpUp_zq (F := F) k (n - k) (levelWidths mats k) _ nodes r (Nat.le_refl _)).bind
      fun res => ?_
    rcases res with _ | ⟨nodes', op, r'⟩
    · exact .pure _
    · refine (ih nodes' r').bind fun res => ?_
      split <;> exact .pure _

theorem multiproof_zq (mats : List (Nat × Nat)) (root : Bytes) (S : List Nat) (r : Bytes) :
    ZQ (multiproof (F := F) mats root S r) := by
  simp only [multiproof]
  refine (mpLeaves_zq _ _ S r).bind fun res => ?_
  rcases res with _ | ⟨leaves, op, r'⟩
  · exact .pure _
  · refine (mpLevels_zq mats _ _ leaves r').bind fun res => ?_
    split <;> exact .pure _

theorem openAll_zq (n0 : Nat) (xs : List Nat) :
    ∀ (os : List (List (Nat × Nat) × Bytes)) (r : Bytes), ZQ (openAll (F := F) n0 xs os r) := by
  intro os
  induction os with
  | nil => intro r; exact .pure _
  | cons o os ih =>
    intro r
    obtain ⟨mats, root⟩ := o
    simp only [openAll]
    refine (multiproof_zq mats root _ r).bind fun res => ?_
    rcases res with _ | ⟨op, r'⟩
    · exact .pure _
    · refine (ih r').bind fun res => ?_
      split <;> exact .pure _

end

/-- **(Q3)** At most `numChunks` `QUERY`-chunk queries. -/
theorem chunk_queryBound : ChunkQueryBoundStmt := by
  intro F K _ _ _ _ V pub cb pb
  simp only [Bcs.compile]
  split
  · exact .pure _ _
  split
  · exact .pure _ _
  next hdr ps rest hp =>
  refine OracleComp.QueryBound.mono (n := 0 + (0 + (V.numChunks + 0))) ?_ (by omega)
  refine ZkFormal.QueryBound.bind (ZQ.toQB (WH_zq _ tagInit_ne _)) fun d0 => ?_
  refine ZkFormal.QueryBound.bind (ZQ.toQB (chain_zq (F := F) d0 ps)) fun ed => ?_
  refine ZkFormal.QueryBound.bind (queryAnswers_chunk _ _) fun answers => ?_
  refine (ZQ.toQB ((openAll_zq (F := F) _ _ _ rest).bind fun res => ?_))
  split <;> exact .pure _

/-- The chunk budget of L2's `starkTree` for the np IOP. -/
theorem np_starkTree_chunk {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]
    [DecidableEq K] (A : Air) (prm : Params) (pub cb pb : Bytes) :
    OracleComp.QueryBound (qWeight Bcs.chunkDec)
      ((Bcs.starkTree (F := F) (Iop.verifier F K A prm)).tree pub cb pb) prm.numChunks :=
  chunk_queryBound F K (Iop.verifier F K A prm) pub cb pb

end ZkFormal.Stark
