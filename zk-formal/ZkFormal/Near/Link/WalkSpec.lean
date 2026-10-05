import ZkFormal.Near.Link.WalkKey

/-!
# ZkFormal.Near.Link.WalkSpec — provided edges are spec walk steps

* `eps_chain` — from `(c, 0)`, `EPS` steps through empty-key extensions reach
  the walk target `(res c, 0)`;
* `edge_walk` — a provided nibble edge is a spec `Walk` of one symbol (key
  step, or child step followed by an `EPS` chain); an `END` edge is a spec
  `END` step; the `START` edge is the root's.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem walk_append {ns : List NodeRec} {s t u : Nat × Nat} {k1 k2 : List Nat}
    (h1 : Walk ns s k1 t) (h2 : Walk ns t k2 u) : Walk ns s (k1 ++ k2) u := by
  induction h1 with
  | nil => exact h2
  | eps hs _ ih => exact .eps hs (ih h2)
  | sym hx hs _ ih => exact .sym hx hs (ih h2)

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem child_depth {n c' l r : Nat} {pre po : List Nat} (hn : n < vs.length)
    (hm : (c', l, r, pre, po) ∈ vs[n].v.revealed) :
    ∃ hc : c' < vs.length, r = vs[c'].res ∧ vs[c'].depth = vs[n].depth + 1 := by
  obtain ⟨hc, -, -, hr, hd⟩ := parent_link h hn hm
  have := depth_lt h hn
  have hlt := vs_length_lt h.node
  exact ⟨hc, hr, (ofNat_inj (h.node.small _ (List.getElem_mem hc)).1 (by omega) hd.symm)⟩

theorem eps_chain : ∀ F c' (hc : c' < vs.length), vs.length ≤ vs[c'].depth + F →
    Walk (vs.map (·.v.toRec)) (c', 0) [] (vs[c'].res, 0)
  | 0, c', hc, hF => absurd (depth_lt h hc) (by omega)
  | F + 1, c', hc, hF => by
    have hres := h.node.res c' hc
    unfold NodeS.resOk at hres
    generalize hv : vs[c'].v = v at hres
    match v, hres with
    | .ext [] (.node c2 l2 cr pre po) mem, hres =>
      have hm : (c2, l2, cr, pre, po) ∈ vs[c'].v.revealed := by rw [hv]; simp [NodeV.revealed]
      obtain ⟨hc2, hcr, hd⟩ := child_depth h hc hm
      have hstep : Step (vs.map (·.v.toRec)) (c', 0) SYM_EPS (c2, 0) := by
        have := Step.eps (ns := vs.map (·.v.toRec)) (n := c') (c := c2) (k := []) (mem := leN' mem)
          (by rw [ns_get h hc, hv]; rfl)
        simpa using this
      rw [hres, hcr]
      exact .eps hstep (eps_chain F c2 hc2 (by omega))
    | .leaf .., hres => rw [hres]; exact .nil
    | .branch .., hres => rw [hres]; exact .nil
    | .ext (_ :: _) _ _, hres => rw [hres]; exact .nil
    | .ext [] .none _, hres => rw [hres]; exact .nil
    | .ext [] (.hash _) _, hres => rw [hres]; exact .nil

theorem eps_chain' {c' : Nat} (hc : c' < vs.length) :
    Walk (vs.map (·.v.toRec)) (c', 0) [] (vs[c'].res, 0) :=
  eps_chain h vs.length c' hc (by omega)

/-- A provided edge, read as spec steps. -/
def EdgeOk (vs : List NodeS) (e : Msg) : Prop :=
  (e.getD 2 0 = SYM_START → ∃ h0 : 0 < vs.length,
    e.getD 0 0 = 0 ∧ e.getD 1 0 = 0 ∧ e.getD 3 0 = vs[0].res ∧ e.getD 4 0 = 0) ∧
  (e.getD 2 0 < 16 → Walk (vs.map (·.v.toRec)) (e.getD 0 0, e.getD 1 0) [e.getD 2 0]
    (e.getD 3 0, e.getD 4 0)) ∧
  (e.getD 2 0 = SYM_END → e.getD 4 0 = 0 ∧
    Step (vs.map (·.v.toRec)) (e.getD 0 0, e.getD 1 0) SYM_END (e.getD 3 0, e.getD 4 0))

theorem edge_walk {n : Nat} (hn : n < vs.length) {e : Msg} (he : e ∈ edgesOf n vs[n]) :
    EdgeOk vs e := by
  have hns := ns_get h hn
  have hw := h.node.wf _ (List.getElem_mem hn)
  have h16 : SYM_START ≠ SYM_END ∧ ¬ SYM_START < 16 ∧ ¬ SYM_END < 16 := by decide
  unfold edgesOf at he
  rcases List.mem_append.mp he with he | he
  · split at he
    · next hn0 =>
      subst hn0
      simp only [List.mem_singleton] at he; subst he
      refine ⟨fun _ => ⟨hn, rfl, rfl, rfl, rfl⟩, fun h1 => absurd h1 h16.2.1, fun h1 => absurd h1 h16.1⟩
    · cases he
  · generalize hv : vs[n].v = v at he hw hns
    -- key edges of a leaf / extension
    have hkey : ∀ (k : List Nat) (i : Nat) (nr : NodeRec), (∀ x ∈ k, x < 16) → i < k.length →
        (vs.map (·.v.toRec))[n]? = some nr →
        (nr matches .leaf .. ∨ nr matches .ext ..) → nr.key = k →
        EdgeOk vs [n, i, k.getD i 0, n, i + 1] := by
      intro k i nr hk hi hns' hm hkk
      have hx : k.getD i 0 < 16 := by rw [getD_eq_getElem _ _ hi]; exact hk _ (List.getElem_mem hi)
      refine ⟨fun h1 => by
          simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; unfold SYM_START at h1; omega,
        fun _ => ?_, fun h1 => by
          simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; unfold SYM_END at h1; omega⟩
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      refine .sym hx (Step.key hns' hm ?_) .nil
      rw [hkk, getD_eq_getElem _ _ hi, List.getElem?_eq_getElem hi]
    cases v with
    | leaf k sl m =>
      obtain ⟨hk, -, -⟩ := hw
      rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, rfl⟩ := mem_keyEdges.mp he
        exact hkey k i _ hk hi hns (.inl rfl) rfl
      · split at he
        · simp only [List.mem_singleton] at he; subst he
          refine ⟨fun h1 => by
              simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; exact absurd h1.symm h16.1,
            fun h1 => by
              simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; exact absurd h1 h16.2.2,
            fun _ => ⟨rfl, ?_⟩⟩
          simp only [List.getD_cons_zero, List.getD_cons_succ]
          exact Step.endLeaf (by rw [hns]; rfl)
        · cases he
    | ext k kid m =>
      obtain ⟨hk, hne, -, -⟩ := hw
      rcases List.mem_append.mp he with he | he
      · obtain ⟨i, hi, rfl⟩ := mem_keyEdges.mp he
        rw [List.length_dropLast] at hi
        have e1 : k.dropLast.getD i 0 = k.getD i 0 := by
          rw [getD_eq_getElem _ _ (by rw [List.length_dropLast]; omega), getD_eq_getElem _ _ (by omega),
            List.getElem_dropLast]
        rw [e1]
        exact hkey k i _ hk (by omega) hns (.inr rfl) rfl
      · cases kid with
        | node c2 l2 cr p1 p2 =>
          cases hl : k.getLast? with
          | none => simp [hl] at he
          | some x =>
            simp only [hl, List.mem_singleton] at he; subst he
            have hxk : x ∈ k := List.mem_of_getLast? hl
            have hx := hk x hxk
            have hkl : 0 < k.length := List.length_pos_of_mem hxk
            have hm : (c2, l2, cr, p1, p2) ∈ vs[n].v.revealed := by rw [hv]; simp [NodeV.revealed]
            obtain ⟨hc2, hcr, -⟩ := child_depth h hn hm
            refine ⟨fun h1 => by
                simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; unfold SYM_START at h1; omega,
              fun _ => ?_, fun h1 => by
                simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; unfold SYM_END at h1; omega⟩
            simp only [List.getD_cons_zero, List.getD_cons_succ]
            have hstep : Step (vs.map (·.v.toRec)) (n, k.length - 1) x (n, k.length - 1 + 1) := by
              refine Step.key (nr := (NodeV.ext k (.node c2 l2 cr p1 p2) m).toRec) (by rw [hns]) (by simp [NodeV.toRec]) ?_
              simp only [NodeV.toRec, NodeRec.key]
              rw [← List.getLast?_eq_getElem?]; exact hl
            have heps : Step (vs.map (·.v.toRec)) (n, k.length) SYM_EPS (c2, 0) :=
              Step.eps (mem := leN' m) (by rw [hns]; rfl)
            rw [show k.length - 1 + 1 = k.length from by omega] at hstep
            rw [hcr]
            exact .sym hx hstep (.eps heps (eps_chain' h hc2))
        | none => simp at he
        | hash => simp at he
    | branch sv kids m =>
      obtain ⟨hl16, -, -, -⟩ := hw
      rcases List.mem_append.mp he with he | he
      · obtain ⟨⟨kd, j⟩, hp, hm⟩ := List.mem_filterMap.mp he
        obtain ⟨hj, hkd⟩ := mem_zip_range.mp hp
        cases kd with
        | node c2 l2 cr p1 p2 =>
          simp only [Option.some.injEq] at hm; subst hm
          have hrev : (c2, l2, cr, p1, p2) ∈ vs[n].v.revealed := by
            rw [hv]; simp only [NodeV.revealed, List.mem_filterMap]
            exact ⟨_, List.getElem_mem hj, by rw [hkd]⟩
          obtain ⟨hc2, hcr, -⟩ := child_depth h hn hrev
          refine ⟨fun h1 => by
              simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; unfold SYM_START at h1; omega,
            fun _ => ?_, fun h1 => by
              simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; unfold SYM_END at h1; omega⟩
          simp only [List.getD_cons_zero, List.getD_cons_succ]
          have hstep : Step (vs.map (·.v.toRec)) (n, 0) j (c2, 0) :=
            Step.child (mem := leN' m) (v := sv.map NSlot.toRec) (kids := kids.map NKid.toRec)
              (by rw [hns]; rfl) (by rw [List.getElem?_map, List.getElem?_eq_getElem hj, hkd]; rfl)
          rw [hcr]
          exact .sym (by omega) hstep (eps_chain' h hc2)
        | none => simp at hm
        | hash => simp at hm
      · rcases sv with _ | sl
        · simp at he
        · cases sl with
          | ref => simp at he
          | touched pre po =>
            simp only [List.mem_singleton] at he; subst he
            refine ⟨fun h1 => by
                simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; exact absurd h1.symm h16.1,
              fun h1 => by
                simp only [List.getD_cons_succ, List.getD_cons_zero] at h1; exact absurd h1 h16.2.2,
              fun _ => ⟨rfl, ?_⟩⟩
            simp only [List.getD_cons_zero, List.getD_cons_succ]
            exact Step.endBranch (by rw [hns]; rfl)

end Hyp

end Link

end ZkFormal.Near
