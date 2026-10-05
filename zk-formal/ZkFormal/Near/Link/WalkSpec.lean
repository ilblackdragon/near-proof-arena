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

end Hyp

end Link

end ZkFormal.Near
