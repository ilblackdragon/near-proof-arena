import ZkFormal.Bcs.StarkOpen

/-!
# ZkFormal.Bcs.StarkAlign — the global oracle list of L4's verifier vs. the view

L4 opens oracles in the global order `schedOracles sched` zipped with the
transcript's roots; the byte-level IOP addresses them as `(entry, tree)`
(`oracleIndex`).  `align` relates the two; `vals_exist` builds the opened
values at one query position, certified by MMCS paths, and shows the rows
`decideA` reads equal the rows L4's `check` reads.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace ZkFormal.Bcs.Adapter

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

theorem Fa2.append {α β : Type} {R : α → β → Prop} {a1 a2 : List α} {b1 b2 : List β}
    (h1 : Fa2 R a1 b1) (h2 : Fa2 R a2 b2) : Fa2 R (a1 ++ a2) (b1 ++ b2) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem Fa2.of_getElem {α β : Type} {R : α → β → Prop} : ∀ (l1 : List α) (l2 : List β),
    l1.length = l2.length → (∀ i (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]) → Fa2 R l1 l2
  | [], [], _, _ => .nil
  | a :: l1, b :: l2, hl, h => .cons (h 0 (by simp) (by simp))
      (Fa2.of_getElem l1 l2 (by simpa using hl) fun i h1 h2 => h (i + 1) (by simp; omega) (by simp; omega))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem Forall2.append {α β : Type} {R : α → β → Prop} {a1 a2 : List α} {b1 b2 : List β}
    (h1 : Forall2 R a1 b1) (h2 : Forall2 R a2 b2) : Forall2 R (a1 ++ a2) (b1 ++ b2) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem Forall2.length {α β : Type} {R : α → β → Prop} {a : List α} {b : List β}
    (h : Forall2 R a b) : a.length = b.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- The oracle blocks of a schedule from entry index `k` on. -/
def oracleIndexFrom (k : Nat) (sched : List Stark.Slot) : List (Nat × Nat × List (Nat × Nat)) :=
  (sched.zipIdx k).flatMap fun
    | (.msg parts, r) => (oracleShapes parts).zipIdx.map fun (m, t) => (r, t, m)
    | (.chal _, _) => []

theorem oracleIndex_eq (sched : List Stark.Slot) : oracleIndex sched = oracleIndexFrom 0 sched := rfl

/-- Alignment of an oracle block `(r, t, mats)` with L4's `(mats, root)`. -/
def AlignR (esF : List EntryV) (schedF : List Stark.Slot) (rtm : Nat × Nat × List (Nat × Nat))
    (g : List (Nat × Nat) × Bytes) : Prop :=
  g.1 = rtm.2.2 ∧ ∃ roots clear parts, esF[rtm.1]? = some (.msg roots clear) ∧ roots[rtm.2.1]? = some g.2 ∧
    schedF[rtm.1]? = some (.msg parts) ∧ (oracleShapes parts)[rtm.2.1]? = some rtm.2.2

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-- The roots of L4's transcript entries, in order. -/
def entOr (entries : List (Stark.Entry K Bytes)) : List Bytes :=
  entries.flatMap fun
    | .msg ps => ps.filterMap fun | .oracle o => some o | _ => none
    | .chal _ => []

theorem entOr_eq (cb : Bytes) (entries : List (Stark.Entry K Bytes)) :
    (⟨cb, entries⟩ : Stark.PT K Bytes).oracles = entOr entries := by
  unfold Stark.PT.oracles entOr
  congr 1
  funext e
  cases e with
  | msg ps =>
    simp only
    congr 1
    funext p
    cases p <;> rfl
  | chal _ => rfl

theorem align (hdr : List Nat) (esF : List EntryV) (schedF : List Stark.Slot) :
    ∀ (sched : List Stark.Slot) (ps : List (Stark.PSlot K)) (entries : List (Stark.Entry K Bytes))
      (es : List EntryV) (preS : List Stark.Slot) (preE : List EntryV),
      schedF = preS ++ sched → esF = preE ++ es → preS.length = preE.length →
      Fa2 (SlotParse (F := F) hdr) sched ps → Rel3 (SlotRel (F := F)) ps entries es →
      Fa2 (AlignR esF schedF) (oracleIndexFrom preS.length sched)
        ((Stark.schedOracles sched).zip (entOr entries))
  | [], [], [], [], _, _, _, _, _, _, _ => by simp [oracleIndexFrom, Stark.schedOracles]; exact .nil
  | s :: ss, p :: ps, e :: entries, v :: es, preS, preE, hS, hE, hl, .cons hsp hsp', .cons hr hr' => by
    have ih := align hdr esF schedF ss ps entries es (preS ++ [s]) (preE ++ [v])
      (by rw [hS]; simp) (by rw [hE]; simp) (by simp [hl]) hsp' hr'
    simp only [List.length_append, List.length_singleton] at ih
    cases hr with
    | chal ood y =>
      cases s with
      | msg _ => exact hsp.elim
      | chal ood' =>
        simp only [oracleIndexFrom, List.zipIdx_cons, List.flatMap_cons, List.nil_append] at ih ⊢
        simpa [Stark.schedOracles, entOr] using ih
    | msg vs raw =>
      cases s with
      | chal _ => exact hsp.elim
      | msg parts =>
        obtain ⟨_, _, hn⟩ := hsp
        have e1 : Stark.schedOracles (.msg parts :: ss) = oracleShapes parts ++ Stark.schedOracles ss := rfl
        have e2 : entOr (Stark.Entry.msg vs :: entries) = Stark.rootsOf vs ++ entOr entries := rfl
        rw [e1, e2, List.zip_append hn.symm]
        have e3 : oracleIndexFrom preS.length (.msg parts :: ss) =
            (oracleShapes parts).zipIdx.map (fun (mt : List (Nat × Nat) × Nat) => (preS.length, mt.2, mt.1)) ++
              oracleIndexFrom (preS.length + 1) ss := by
          simp only [oracleIndexFrom, List.zipIdx_cons, List.flatMap_cons]
        rw [e3]
        refine Fa2.append ?_ ih
        apply Fa2.of_getElem
        · simp [hn]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_zip, Nat.zero_add]
          simp only [List.length_map, List.length_zipIdx] at h1
          refine ⟨rfl, Stark.rootsOf vs, Stark.clearOf vs raw, parts, ?_, ?_, ?_, ?_⟩
          · rw [hE, List.getElem?_append_right (by omega), ← hl, Nat.sub_self]; rfl
          · exact List.getElem?_eq_getElem _
          · rw [hS, List.getElem?_append_right (by omega), Nat.sub_self]; rfl
          · exact List.getElem?_eq_getElem _
  | [], _ :: _, _, _, _, _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, _, _, _, _, h, _ => by cases h
  | [], [], _ :: _, _, _, _, _, _, _, _, h => by cases h
  | [], [], [], _ :: _, _, _, _, _, _, _, h => by cases h
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, h => by cases h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, _, h => by cases h

/-- One oracle: values for every matrix, with L4's rows. -/
theorem oracle_vals (mats : List (Nat × Nat)) (op : Stark.Opened F) (n0 x : Nat) (P : (Nat × Nat) → Bytes → Prop)
    (hcert : ∀ mw ∈ mats, ∃ rows raw, op.lookup (mw.1, x >>> (n0 - mw.1)) = some rows ∧ P mw raw ∧
      Stark.readRows (F := F) (Stark.levelWidths mats mw.1) raw = some (rows, [])) :
    ∀ (ms : List (Nat × Nat)) (seen : List Nat), (∀ mw ∈ ms, mw ∈ mats) →
      ∃ vs, Forall2 P ms vs ∧ rowsOf (F := F) mats ms seen vs = Stark.rowsAt.go n0 op x ms seen
  | [], seen, _ => ⟨[], .nil, by simp [rowsOf, Stark.rowsAt.go]⟩
  | (m, w) :: ms, seen, hsub => by
    obtain ⟨rows, raw, hl, hp, hr⟩ := hcert (m, w) (hsub _ List.mem_cons_self)
    obtain ⟨vs, hvs, heq⟩ := oracle_vals mats op n0 x P hcert ms (m :: seen)
      (fun mw h => hsub mw (List.mem_cons_of_mem _ h))
    refine ⟨raw :: vs, .cons hp hvs, ?_⟩
    simp only [rowsOf, Stark.rowsAt.go, hr, heq]
    simp only at hl
    rw [hl]

theorem rowsAll_append (mats : List (Nat × Nat)) (os : List (List (Nat × Nat))) (vs rest : List Bytes)
    (hl : vs.length = mats.length) :
    rowsAll (F := F) (mats :: os) (vs ++ rest) = rowsOf (F := F) mats mats [] vs :: rowsAll (F := F) os rest := by
  simp only [rowsAll]
  rw [← hl, List.take_left' rfl, List.drop_left' rfl]

end

end ZkFormal.Bcs.Adapter
