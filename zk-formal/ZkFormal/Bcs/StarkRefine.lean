import ZkFormal.Bcs.StarkAlign

/-!
# ZkFormal.Bcs.StarkRefine — `compile_accepts : MultiproofStmt → CompileAcceptsStmt`

Lane L4's deployed verifier (`Stark.Bcs.compile`), accepting on a well-formed
oracle log, certifies `AcceptsIn (adapt V)` — the hypothesis `hV` of
`bcs_romSound`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace ZkFormal.Bcs.Adapter

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

theorem le_treeLog {mats : List (Nat × Nat)} {mw : Nat × Nat} (h : mw ∈ mats) : mw.1 ≤ Stark.treeLog mats := by
  unfold Stark.treeLog
  induction mats with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem Forall2.map_left {α β γ : Type} {R : β → γ → Prop} (f : α → β) :
    ∀ {l : List α} {l' : List γ}, Forall2 (fun a c => R (f a) c) l l' → Forall2 R (l.map f) l'
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons h (Forall2.map_left f hl)

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-- The header seen by every message entry's shape computation. -/
theorem viewHeader_take (V : Stark.IopSpec F K) (es : List EntryV) (hdr : List Nat)
    (h : viewHeader V es [] = some hdr) :
    ∀ r roots clear, es[r]? = some (.msg roots clear) → viewHeader V (es.take r) clear = some hdr := by
  intro r roots clear he
  cases es with
  | nil => simp at he
  | cons e0 es' =>
    cases r with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      simpa [viewHeader] using h
    | succ r =>
      simp only [List.take_succ_cons]
      cases e0 with
      | msg _ c => simpa [viewHeader] using h
      | chal _ => simp [viewHeader] at h

/-- **Values at one query position.** -/
theorem build (hmp : MultiproofStmt) (V : Stark.IopSpec F K) (tbl : Table) (wf : TableWF tbl)
    (cb : Bytes) (es : List EntryV) (hdr : List Nat)
    (hvh : ∀ r roots clear, es[r]? = some (.msg roots clear) → viewHeader V (es.take r) clear = some hdr)
    (xs : List Nat) (x : Nat) (hx : x ∈ xs) :
    ∀ (idx : List (Nat × Nat × List (Nat × Nat))) (G : List (List (Nat × Nat) × Bytes))
      (ops : List (Stark.Opened F)),
      Fa2 (AlignR es (V.schedule hdr)) idx G →
      Fa2 (fun (o : List (Nat × Nat) × Bytes) (op : Stark.Opened F) => ∃ r1 r2,
        evalT tbl (Stark.multiproof (F := F) o.1 o.2
          (Stark.sortDedup (xs.map fun x => x >>> (V.queryLog hdr - Stark.treeLog o.1))) r1) =
            some (some (op, r2))) G ops →
      (∀ g ∈ G, Stark.treeLog g.1 ≤ V.queryLog hdr) →
      ∃ vals, Forall2 (OpenAt (adapt V) tbl ⟨cb, es⟩)
          (idx.flatMap fun (rtm : Nat × Nat × List (Nat × Nat)) =>
            rtm.2.2.map fun mw => (rtm.1, rtm.2.1, (mw.1, x >>> (V.queryLog hdr - mw.1)))) vals ∧
        rowsAll (F := F) (G.map Prod.fst) vals =
          ((G.map Prod.fst).zip ops).map fun (mo : List (Nat × Nat) × Stark.Opened F) =>
            Stark.rowsAt (V.queryLog hdr) mo.1 mo.2 x
  | [], [], [], .nil, .nil, _ => ⟨[], .nil, by simp [rowsAll]⟩
  | (r, t, mats) :: idx, (mats', root) :: G, op :: ops, .cons ha hal, .cons hm hml, hdep => by
    obtain ⟨vals, hv, hrows⟩ := build hmp V tbl wf cb es hdr hvh xs x hx idx G ops hal hml
      (fun g hg => hdep g (List.mem_cons_of_mem _ hg))
    obtain ⟨hmm, roots, clear, parts, he, hroot, hs, hsh⟩ := ha
    simp only at hmm hroot hs hsh he
    subst hmm
    obtain ⟨r1, r2, hmp1⟩ := hm
    simp only at hmp1
    have hn : Stark.treeLog mats' ≤ V.queryLog hdr := hdep _ List.mem_cons_self
    have hS : x >>> (V.queryLog hdr - Stark.treeLog mats') ∈ Stark.sortDedup (xs.map fun x => x >>> (V.queryLog hdr - Stark.treeLog mats')) :=
      sortDedup_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)
    have hcert := hmp F K tbl mats' root _ r1 op r2 wf hmp1 _ hS
    -- the shape of this tree, as computed by the byte-level IOP
    have hrlen : r < es.length := (List.getElem?_eq_some_iff.mp he).1
    have hshape : (shapesA V (View.prefix ⟨cb, es⟩ r) clear)[t]? = some (Stark.treeLog mats') := by
      simp only [shapesA, View.prefix]
      rw [hvh r roots clear he, List.length_take, Nat.min_eq_left (Nat.le_of_lt hrlen)]
      simp only
      rw [hs]
      simp [hsh]
    obtain ⟨vs, hvs, hrw⟩ := oracle_vals (F := F) mats' op (V.queryLog hdr) x
      (fun mw v => OpenAt (adapt V) tbl ⟨cb, es⟩ (r, t, (mw.1, x >>> (V.queryLog hdr - mw.1))) v)
      (fun mw hmw => by
        obtain ⟨rows, raw, hl, hop, hrr⟩ := hcert mw hmw
        have hm := le_treeLog hmw
        have e : x >>> (V.queryLog hdr - Stark.treeLog mats') >>> (Stark.treeLog mats' - mw.1) = x >>> (V.queryLog hdr - mw.1) := by
          rw [← Nat.shiftRight_add]; congr 1; omega
        rw [e] at hl hop
        exact ⟨rows, raw, hl, ⟨.msg roots clear, root, Stark.treeLog mats', he, hroot, hshape, hop⟩, hrr⟩)
      mats' [] [] (by simp) (by simp)
    refine ⟨vs ++ vals, ?_, ?_⟩
    · simp only [List.flatMap_cons]
      exact Forall2.append (Forall2.map_left _ hvs) hv
    · simp only [List.map_cons, List.zip_cons_cons]
      rw [rowsAll_append _ _ _ _ (Forall2.length hvs).symm, hrw, hrows]
      rfl
  | [], _ :: _, _, h, _, _ => by cases h
  | _ :: _, [], _, h, _, _ => by cases h
  | _, [], _ :: _, _, h, _ => by cases h
  | _, _ :: _, [], _, h, _ => by cases h

end

end ZkFormal.Bcs.Adapter
