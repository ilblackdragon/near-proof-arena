import ZkFormal.Stark.Statements

/-!
# ZkFormal.Stark.QueryBound — the compiled verifier's query budget

Proves `compile_queryBound : CompileQueryBoundStmt`: the BCS-compiled
verifier of any `IopSpec` with `IopBounds V S O D` makes at most
`compileBound V S O D` oracle queries on every path.

Tool: `QBP P oa n` — every path of `oa` makes at most `n` queries *and*
every result satisfies `P`, so that later budgets may depend on invariants of
earlier results (list lengths of the Merkle node frontier).
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Stark

open ArenaCore ArenaCore.Security Lean.Grind

/-- Unit-weight query bound with a postcondition on results. -/
inductive QBP {α : Type} (P : α → Prop) : OracleComp hashSpec α → Nat → Prop
  | pure (a : α) (n : Nat) : P a → QBP P (.pure a) n
  | query (q : Bytes) (k : Bytes → OracleComp hashSpec α) (n : Nat) :
      1 ≤ n → (∀ r, QBP P (k r) (n - 1)) → QBP P (.query q k) n

namespace QBP

theorem mono {α : Type} {P : α → Prop} {oa : OracleComp hashSpec α} {n m : Nat}
    (h : QBP P oa n) (hnm : n ≤ m) : QBP P oa m := by
  induction h generalizing m with
  | pure a n ha => exact .pure a m ha
  | query q k n h1 _ ih => exact .query q k m (by omega) fun r => ih r (by omega)

theorem weaken {α : Type} {P Q : α → Prop} {oa : OracleComp hashSpec α} {n : Nat}
    (h : QBP P oa n) (hPQ : ∀ a, P a → Q a) : QBP Q oa n := by
  induction h with
  | pure a n ha => exact .pure a n (hPQ a ha)
  | query q k n h1 _ ih => exact .query q k n h1 ih

theorem toQB {α : Type} {P : α → Prop} {oa : OracleComp hashSpec α} {n : Nat}
    (h : QBP P oa n) : OracleComp.QueryBound unitWeight oa n := by
  induction h with
  | pure a n _ => exact .pure a n
  | query q k n h1 _ ih =>
    exact OracleComp.QueryBound.query (spec := hashSpec) (w := unitWeight) q k n h1 fun r => ih r

theorem bind {α β : Type} {P : α → Prop} {Q : β → Prop} {oa : OracleComp hashSpec α}
    {f : α → OracleComp hashSpec β} {a b : Nat} (h : QBP P oa a)
    (hf : ∀ r, P r → QBP Q (f r) b) : QBP Q (OracleComp.bind oa f) (a + b) := by
  induction h with
  | pure x a hx => exact (hf x hx).mono (Nat.le_add_left _ _)
  | query q k a h1 _ ih =>
    refine .query q _ (a + b) (by omega) fun r => ?_
    have e : a - 1 + b = a + b - 1 := by omega
    rw [← e]; exact ih r

theorem bind_le {α β : Type} {P : α → Prop} {Q : β → Prop} {oa : OracleComp hashSpec α}
    {f : α → OracleComp hashSpec β} {a b n : Nat} (h : QBP P oa a)
    (hf : ∀ r, P r → QBP Q (f r) b) (hle : a + b ≤ n) : QBP Q (OracleComp.bind oa f) n :=
  (bind h hf).mono hle

theorem pure' {α : Type} {P : α → Prop} {a : α} (n : Nat) (h : P a) :
    QBP P (OracleComp.pure a) n := .pure a n h

end QBP

theorem H_qbp (m : Bytes) : QBP (fun _ => True) (H m) 1 :=
  .query m _ 1 (Nat.le_refl 1) fun _ => .pure _ _ trivial

theorem WH_qbp (tag : UInt8) (m : Bytes) : QBP (fun _ => True) (WH tag m) 2 := by
  unfold WH
  exact QBP.bind (a := 1) (b := 1) (H_qbp _) fun a _ =>
    (QBP.bind (a := 1) (b := 0) (H_qbp _) fun b _ => QBP.pure' (P := fun _ => True) 0 trivial)

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

theorem chain_qbp (d : Bytes) (ps : List (PSlot K)) :
    QBP (fun _ => True) (chain (F := F) d ps) (2 * ps.length) := by
  induction ps generalizing d with
  | nil => exact .pure _ _ trivial
  | cons p ps ih =>
    cases p with
    | msg vs raw =>
      simp only [chain]
      refine QBP.bind_le (WH_qbp _ _) (fun d' _ => ?_) (b := 2 * ps.length) (by simp; omega)
      exact QBP.bind_le (ih d') (fun _ _ => QBP.pure' 0 trivial) (by omega)
    | chal ood =>
      simp only [chain]
      refine QBP.bind_le (WH_qbp _ _) (fun d' _ => ?_) (b := 2 * ps.length) (by simp; omega)
      exact QBP.bind_le (ih d') (fun _ _ => QBP.pure' 0 trivial) (by omega)

end

theorem queryAnswers_qbp (d : Bytes) (n : Nat) :
    QBP (fun ys => ys.length = n) (queryAnswers d n) n := by
  induction n with
  | zero => exact .pure _ _ rfl
  | succ n ih =>
    simp only [queryAnswers]
    refine QBP.bind_le ih (fun ys hys => ?_) (b := 1) (by omega)
    exact QBP.bind_le (H_qbp _) (fun y _ => QBP.pure' 0 (by simp [hys])) (by omega)

section Merkle
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

/-- Postcondition: the returned node list has length at most `n`. -/
def NodesLe {β : Type} (n : Nat) (res : Option (List (Nat × Bytes) × β)) : Prop :=
  ∀ hs b, res = some (hs, b) → hs.length ≤ n

theorem NodesLe_mono {β : Type} {n m : Nat} (h : n ≤ m) :
    ∀ res : Option (List (Nat × Bytes) × β), NodesLe n res → NodesLe m res :=
  fun _ hr hs b e => Nat.le_trans (hr hs b e) h

theorem mpLeaves_qbp (n : Nat) (ws : List Nat) (xs : List Nat) (r : Bytes) :
    QBP (NodesLe xs.length) (mpLeaves (F := F) n ws xs r) (2 * xs.length) := by
  induction xs generalizing r with
  | nil => exact .pure _ _ (by intro hs b h; simp at h; simp [← h.1])
  | cons x xs ih =>
    simp only [mpLeaves]
    split
    · exact .pure _ _ (by intro hs b h; cases h)
    · refine QBP.bind_le (WH_qbp _ _) (fun h _ => ?_) (b := 2 * xs.length) (by simp; omega)
      refine QBP.bind_le (ih _) (fun res hres => ?_) (b := 0) (by omega)
      rcases res with _ | ⟨hs, op, r''⟩
      · exact .pure _ _ (by intro hs b h; cases h)
      · exact .pure _ _ (by
          intro hs' b h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]; simp only [List.length_cons]
          have := hres hs (op, r'') rfl; omega)

theorem mpNode_qbp (lvl : Nat) (ws : List Nat) (x : Nat) (lft rgt r : Bytes) :
    QBP (fun _ => True) (mpNode (F := F) lvl ws x lft rgt r) 4 := by
  simp only [mpNode]
  split
  · exact .pure _ _ trivial
  · exact QBP.bind_le (WH_qbp _ _) (fun _ _ => QBP.pure' 0 trivial) (by omega)

/-- The `finish` step of `mpUp`: one parent (≤ 4 queries) then the rest. -/
theorem mpUp_finish_qbp (k lvl : Nat) (ws : List Nat) (x : Nat) (lft rgt r1 : Bytes) (m : Nat)
    (recur : Bytes → OracleComp hashSpec (Option (List (Nat × Bytes) × Opened F × Bytes)))
    (hrec : ∀ r2, QBP (NodesLe m) (recur r2) (4 * m)) :
    QBP (NodesLe (m + 1))
      (OracleComp.bind (mpNode (F := F) lvl ws (x / 2) lft rgt r1) fun
        | none => .pure none
        | some (nh, rows?, r2) =>
          OracleComp.bind (recur r2) fun
            | none => .pure none
            | some (hs, op, r3) =>
              .pure (some (nh :: hs, (match rows? with
                | some rows => ((k, x / 2), rows) :: op
                | none => op), r3))) (4 * (m + 1)) := by
  refine QBP.bind_le (mpNode_qbp _ _ _ _ _ _) (fun res _ => ?_) (b := 4 * m) (by omega)
  rcases res with _ | ⟨nh, rows?, r2⟩
  · exact .pure _ _ (by intro hs b h; cases h)
  · refine QBP.bind_le (hrec r2) (fun res hres => ?_) (b := 0) (by omega)
    rcases res with _ | ⟨hs, op, r3⟩
    · exact .pure _ _ (by intro hs b h; cases h)
    · exact .pure _ _ (by
        intro hs' b h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; simp only [List.length_cons]
        have := hres hs _ rfl; omega)

theorem mpUp_qbp (k lvl : Nat) (ws : List Nat) :
    ∀ (N : Nat) (nodes : List (Nat × Bytes)) (r : Bytes), nodes.length ≤ N →
      QBP (NodesLe nodes.length) (mpUp (F := F) k lvl ws nodes r) (4 * nodes.length) := by
  intro N
  induction N with
  | zero =>
    intro nodes r h
    match nodes with
    | [] => exact .pure _ _ (by intro hs b h; simp at h; simp [← h.1])
  | succ N ih =>
    intro nodes r hN
    match nodes with
    | [] => exact .pure _ _ (by intro hs b h; simp at h; simp [← h.1])
    | (x, h) :: tl =>
      match tl with
      | (x', h') :: rest =>
        simp only [mpUp]
        have hr : rest.length ≤ N := by simp at hN; omega
        have hr' : ((x', h') :: rest).length ≤ N := by simp at hN; omega
        split
        · exact ((mpUp_finish_qbp k lvl ws x h h' r _ _ fun r2 => ih rest r2 hr).weaken
            (NodesLe_mono (by simp))).mono (by simp; omega)
        · split
          · exact .pure _ _ (by intro hs b h; cases h)
          · split
            · exact ((mpUp_finish_qbp k lvl ws x h _ _ _ _ fun r2 => ih _ r2 hr').weaken
                (NodesLe_mono (by simp))).mono (by simp)
            · exact ((mpUp_finish_qbp k lvl ws x _ h _ _ _ fun r2 => ih _ r2 hr').weaken
                (NodesLe_mono (by simp))).mono (by simp)
      | [] =>
        simp only [mpUp]
        split
        · exact .pure _ _ (by intro hs b h; cases h)
        · split
          · exact ((mpUp_finish_qbp k lvl ws x h _ _ _ _ fun r2 => ih [] r2 (by simp)).weaken
              (NodesLe_mono (by simp))).mono (by simp)
          · exact ((mpUp_finish_qbp k lvl ws x _ h _ _ _ fun r2 => ih [] r2 (by simp)).weaken
              (NodesLe_mono (by simp))).mono (by simp)

theorem mpLevels_qbp (mats : List (Nat × Nat)) (n Q : Nat) :
    ∀ (k : Nat) (nodes : List (Nat × Bytes)) (r : Bytes), nodes.length ≤ Q →
      QBP (fun _ => True) (mpLevels (F := F) mats n k nodes r) (4 * Q * k) := by
  intro k
  induction k with
  | zero =>
    intro nodes r _
    simp only [mpLevels]
    split <;> exact .pure _ _ trivial
  | succ k ih =>
    intro nodes r hQ
    simp only [mpLevels]
    refine QBP.bind_le (mpUp_qbp (F := F) k (n - k) (levelWidths mats k) _ nodes r (Nat.le_refl _))
      (fun res hres => ?_) (b := 4 * Q * k) (by rw [Nat.mul_succ]; have := Nat.mul_le_mul_left 4 hQ; omega)
    rcases res with _ | ⟨nodes', op, r'⟩
    · exact .pure _ _ trivial
    · refine QBP.bind_le (ih nodes' r' ?_) (fun _ _ => ?_) (b := 0) (by omega)
      · have := hres nodes' (op, r') rfl; omega
      · split <;> exact .pure _ _ trivial

theorem multiproof_qbp (mats : List (Nat × Nat)) (root : Bytes) (S : List Nat) (r : Bytes) :
    QBP (fun _ => True) (multiproof (F := F) mats root S r)
      (2 * S.length + 4 * S.length * treeLog mats) := by
  simp only [multiproof]
  refine QBP.bind_le (mpLeaves_qbp _ _ S r) (fun res hres => ?_)
    (b := 4 * S.length * treeLog mats) (Nat.le_refl _)
  rcases res with _ | ⟨leaves, op, r'⟩
  · exact .pure _ _ trivial
  · refine QBP.bind_le (mpLevels_qbp mats _ S.length _ leaves r' (hres leaves (op, r') rfl))
      (fun res _ => ?_) (b := 0) (by simp [treeLog])
    split <;> exact .pure _ _ trivial

theorem dedupSorted_length : ∀ l : List Nat, (sortDedup.dedupSorted l).length ≤ l.length
  | a :: b :: rest => by
    simp only [sortDedup.dedupSorted]
    have := dedupSorted_length (b :: rest)
    split <;> simp_all <;> omega
  | [] => by simp [sortDedup.dedupSorted]
  | [a] => by simp [sortDedup.dedupSorted]

theorem sortDedup_length (xs : List Nat) : (sortDedup xs).length ≤ xs.length := by
  simp only [sortDedup]
  exact Nat.le_trans (dedupSorted_length _) (by simp [List.length_mergeSort])

theorem openAll_qbp (n0 : Nat) (xs : List Nat) (D : Nat) :
    ∀ (os : List (List (Nat × Nat) × Bytes)) (r : Bytes), (∀ o ∈ os, treeLog o.1 ≤ D) →
      QBP (fun _ => True) (openAll (F := F) n0 xs os r)
        (os.length * (2 * xs.length + 4 * xs.length * D)) := by
  intro os
  induction os with
  | nil => intro r _; exact .pure _ _ trivial
  | cons o os ih =>
    intro r hD
    obtain ⟨mats, root⟩ := o
    simp only [openAll]
    have hS := sortDedup_length (xs.map fun x => x >>> (n0 - treeLog mats))
    simp only [List.length_map] at hS
    have hm : treeLog mats ≤ D := hD _ List.mem_cons_self
    refine QBP.bind_le (multiproof_qbp mats root _ r) (fun res _ => ?_)
      (b := os.length * (2 * xs.length + 4 * xs.length * D)) ?_
    · rcases res with _ | ⟨op, r'⟩
      · exact .pure _ _ trivial
      · refine QBP.bind_le (ih r' fun o ho => hD o (List.mem_cons_of_mem _ ho)) (fun res _ => ?_)
          (b := 0) (by omega)
        split <;> exact .pure _ _ trivial
    · rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      generalize (sortDedup (List.map (fun x => x >>> (n0 - treeLog mats)) xs)).length = b at hS ⊢
      generalize treeLog mats = d at hm ⊢
      have h1 : 4 * b * d ≤ 4 * xs.length * D := by
        rw [Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul hS hm)
      omega

end Merkle

section Compile
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

theorem parseSlots_length (hdr : List Nat) :
    ∀ (ss : List Slot) (r : Bytes) (ps : List (PSlot K)) (r' : Bytes),
      parseSlots (F := F) hdr ss r = some (ps, r') → ps.length = ss.length := by
  intro ss
  induction ss with
  | nil => intro r ps r' h; simp [parseSlots] at h; simp [← h.1]
  | cons s ss ih =>
    intro r ps r' h
    cases s with
    | chal ood =>
      simp only [parseSlots] at h
      split at h
      · cases h
      · next ps0 r0 e =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; simp [ih r ps0 r0 e]
    | msg parts =>
      simp only [parseSlots] at h
      split at h
      · cases h
      · split at h
        · cases h
        · next ps0 r0 e =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]; simp [ih _ ps0 r0 e]

theorem parsePrefix_facts (V : IopSpec F K) (pb : Bytes) (hdr : List Nat) (ps : List (PSlot K))
    (rest : Bytes) (h : parsePrefix (F := F) V pb = some (hdr, ps, rest)) :
    V.headerOk hdr = true ∧ ps.length = (V.schedule hdr).length := by
  simp only [parsePrefix] at h
  split at h
  · cases h
  · next hdr0 _ _ =>
    split at h
    · next hok =>
      split at h
      · cases h
      · next ps0 r0 e =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hok, parseSlots_length _ _ _ _ _ e⟩
    · cases h

theorem positions_length (V : IopSpec F K) (n0 : Nat) :
    ∀ answers : List Bytes, (V.positions n0 answers).length = answers.length * V.posPerChunk := by
  intro answers
  induction answers with
  | nil => simp [IopSpec.positions]
  | cons a as ih =>
    simp only [IopSpec.positions, List.flatMap_cons, List.length_append, List.length_map,
      List.length_range, List.length_cons] at ih ⊢
    rw [ih, Nat.succ_mul]; omega

theorem zip_fst_mem {α β : Type} {a : α} {b : β} :
    ∀ {l₁ : List α} {l₂ : List β}, (a, b) ∈ l₁.zip l₂ → a ∈ l₁
  | _ :: _, _ :: _, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩ | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (zip_fst_mem h)
  | [], _, h => by simp at h
  | _ :: _, [], h => by simp at h

end Compile

/-- **(Q1)** The BCS-compiled verifier respects `compileBound`. -/
theorem compile_queryBound : CompileQueryBoundStmt := by
  intro F K _ _ _ _ V S O D hB pub cb pb
  apply QBP.toQB (P := fun _ => True)
  simp only [Bcs.compile]
  split
  · exact .pure _ _ trivial
  split
  · exact .pure _ _ trivial
  next hdr ps rest hp =>
  obtain ⟨hok, hlen⟩ := parsePrefix_facts V pb hdr ps rest hp
  have hS := hB.sched hdr hok
  have hO := hB.oracles hdr hok
  have hD := hB.depth hdr hok
  let Q := V.numQueries
  let M := 2 * Q + 4 * Q * D
  refine QBP.bind_le (WH_qbp _ _) (fun d0 _ => ?_) (b := 2 * S + V.numChunks + O * M) (by
    simp only [compileBound, M, Q]; omega)
  refine QBP.bind_le (chain_qbp (F := F) d0 ps) (fun ed _ => ?_) (b := V.numChunks + O * M)
    (by rw [hlen]; have := Nat.mul_le_mul_left 2 hS; omega)
  obtain ⟨entries, dfin⟩ := ed
  refine QBP.bind_le (queryAnswers_qbp dfin V.numChunks) (fun answers hans => ?_) (b := O * M)
    (Nat.le_refl _)
  have hxs : (V.positions (V.queryLog hdr) answers).length = Q := by
    rw [positions_length, hans]; rfl
  have hos : ∀ o ∈ (schedOracles (V.schedule hdr)).zip (PT.oracles ⟨cb, entries⟩ : List Bytes),
      treeLog o.1 ≤ D := fun o ho => hD _ (zip_fst_mem (b := o.2) ho)
  refine QBP.bind_le (openAll_qbp (F := F) _ _ D _ rest hos) (fun res _ => ?_) (b := 0) ?_
  · split <;> exact .pure _ _ trivial
  · rw [hxs, List.length_zip]
    have : min (schedOracles (V.schedule hdr)).length (PT.oracles ⟨cb, entries⟩ : List Bytes).length
        ≤ O := Nat.le_trans (Nat.min_le_left _ _) hO
    have := Nat.mul_le_mul_right (2 * Q + 4 * Q * D) this
    omega

end ZkFormal.Stark
