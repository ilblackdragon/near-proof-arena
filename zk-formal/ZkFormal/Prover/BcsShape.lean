import ZkFormal.Prover.Statements

/-!
# ZkFormal.Prover.BcsShape — the honest commit loop follows the schedule

`Inv V pr cb ss τ`: the IOP transcript `τ` of the honest commit loop is reachable
and the slots still to run are `ss = (V.schedule pr.hdr).drop |τ.entries|`.
Under `ProverWf` it is preserved by both kinds of slots (`inv_msg`, `inv_chal`),
every message fits its slot (so its oracles have the schedule's shapes,
`msgShapes`), and at the end the transcript is at the query phase (`inv_end`).
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

/-- Oracle shapes of the parts of a message slot (as in `schedOracles`). -/
def partOracles (ps : List Part) : List (List (Nat × Nat)) :=
  ps.filterMap fun | .oracle m => some m | _ => none

theorem schedOracles_nil : schedOracles [] = [] := rfl

theorem schedOracles_msg (ps : List Part) (ss : List Slot) :
    schedOracles (.msg ps :: ss) = partOracles ps ++ schedOracles ss := by
  simp only [schedOracles, partOracles, List.flatMap_cons]; rfl

theorem schedOracles_chal (b : Bool) (ss : List Slot) :
    schedOracles (.chal b :: ss) = schedOracles ss := by
  simp [schedOracles, List.flatMap_cons]

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

/-! ## Fitting messages -/

/-- Pointwise `Fits` (`List.Forall₂`, which core lacks). -/
inductive Fits2 : List (PartV K (Oracle F)) → List Part → Prop
  | nil : Fits2 [] []
  | cons {p : PartV K (Oracle F)} {q : Part} {ps qs} :
      Udr.PartV.Fits p q → Fits2 ps qs → Fits2 (p :: ps) (q :: qs)

theorem forall2_of_fits : ∀ (ps : List (PartV K (Oracle F))) (parts : List Part),
    ps.length = parts.length →
    (∀ k (hk : k < ps.length), ∃ pt, parts[k]? = some pt ∧ Udr.PartV.Fits ps[k] pt) →
    Fits2 ps parts
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | p :: ps, q :: qs, hl, h => by
    refine .cons ?_ (forall2_of_fits ps qs (by simpa using hl) fun k hk => ?_)
    · obtain ⟨pt, h1, h2⟩ := h 0 (by simp)
      simp at h1; subst h1; exact h2
    · obtain ⟨pt, h1, h2⟩ := h (k + 1) (by simp; omega)
      exact ⟨pt, by simpa using h1, by simpa using h2⟩

theorem shapesOf_of_fits {o : Oracle F} {mats : List (Nat × Nat)}
    (h : Udr.PartV.Fits (K := K) (.oracle o) (.oracle mats)) : shapesOf o = mats := by
  obtain ⟨hl, hk⟩ := h
  apply List.ext_getElem (by simp [shapesOf, hl])
  intro k h1 h2
  have hk' : k < o.length := by simpa [shapesOf] using h1
  obtain ⟨sh, hs, hlog, hw, _⟩ := hk k hk'
  rw [List.getElem?_eq_getElem h2] at hs
  cases hs
  simp [shapesOf, hlog, hw]

/-- Messages fitting their parts: the oracles have the parts' shapes. -/
theorem msgShapes : ∀ {ps : List (PartV K (Oracle F))} {parts : List Part},
    Fits2 ps parts → (msgOracles ps).map shapesOf = partOracles parts
  | [], [], .nil => rfl
  | p :: ps, q :: qs, .cons h hs => by
    have ih := msgShapes hs
    have e1 : msgOracles (p :: ps) = (match p with | .oracle o => [o] | _ => []) ++ msgOracles ps := by
      cases p <;> rfl
    have e2 : partOracles (q :: qs) = (match q with | .oracle m => [m] | _ => []) ++ partOracles qs := by
      cases q <;> rfl
    rw [e1, e2, List.map_append, ih]
    cases p <;> cases q
    all_goals first
      | exact (h : False).elim
      | rfl
      | simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          shapesOf_of_fits h]

/-! ## The invariant -/

variable (V : IopSpec F K) (pr : IopProver F K) (cb : Bytes)

/-- Invariant of the honest commit loop. -/
def Inv (ss : List Slot) (τ : PT K (Oracle F)) : Prop :=
  Reach V pr cb τ ∧ (V.schedule pr.hdr).drop τ.entries.length = ss

variable {V pr cb}

theorem Reach.cb_eq {τ : PT K (Oracle F)} (h : Reach V pr cb τ) : τ.cb = cb := by
  induction h with
  | init => rfl
  | msg τ _ _ ih => exact ih
  | chal τ _ _ _ _ ih => exact ih

theorem slots_of_ne (hw : ProverWf V pr cb) {τ : PT K (Oracle F)} (h : Reach V pr cb τ)
    (hne : τ.entries ≠ []) : V.slots τ = V.schedule pr.hdr := by
  simp [IopSpec.slots, hw.header τ h hne]

theorem slots_of_nil {τ : PT K (Oracle F)} (hne : τ.entries = []) :
    V.slots τ = [.msg [.header V.numTables]] := by
  simp [IopSpec.slots, PT.header?, hne]

theorem getElem?_of_drop {α : Type} {l : List α} {n : Nat} {a : α} {rest : List α}
    (h : l.drop n = a :: rest) : l[n]? = some a := by
  rw [← List.head?_drop, h]; rfl

theorem drop_succ_of_drop {α : Type} {l : List α} {n : Nat} {a : α} {rest : List α}
    (h : l.drop n = a :: rest) : l.drop (n + 1) = rest := by
  rw [← List.tail_drop, h]; rfl

/-- The first slot of the schedule is a message (it carries the header). -/
theorem sched_head (hw : ProverWf V pr cb) :
    ∃ parts, (V.schedule pr.hdr)[0]? = some (.msg parts) := by
  have hr : Reach V pr cb ((PT.init cb : PT K (Oracle F)).push (pr.next (PT.init cb))) :=
    .msg _ .init ⟨_, by
      show (V.slots (PT.init cb : PT K (Oracle F)))[0]? = _
      simp [IopSpec.slots, PT.header?, PT.init]; rfl⟩
  have hne : ((PT.init cb : PT K (Oracle F)).push (pr.next (PT.init cb))).entries ≠ [] := by
    simp [PT.push, PT.init]
  obtain ⟨_, _, h3⟩ := hw.shaped _ hr
  obtain ⟨s, hs, hf⟩ := h3 0 (by simp [PT.push, PT.init])
  rw [slots_of_ne hw hr hne] at hs
  cases s with
  | msg parts => exact ⟨parts, hs⟩
  | chal b => simp [PT.push, PT.init, Udr.Entry.Fits] at hf

theorem inv_init : Inv V pr cb (V.schedule pr.hdr) (PT.init cb) := ⟨.init, rfl⟩

theorem inv_msg (hw : ProverWf V pr cb) {parts : List Part} {ss : List Slot}
    {τ : PT K (Oracle F)} (h : Inv V pr cb (.msg parts :: ss) τ) :
    Inv V pr cb ss (τ.push (pr.next τ)) ∧ Fits2 (pr.next τ) parts := by
  obtain ⟨hr, hd⟩ := h
  have hg := getElem?_of_drop hd
  have hnp : V.NextIsProver τ := by
    by_cases he : τ.entries = []
    · exact ⟨[.header V.numTables], by simp [slots_of_nil (V := V) he, he]⟩
    · exact ⟨parts, by rw [slots_of_ne hw hr he]; exact hg⟩
  have hr' : Reach V pr cb (τ.push (pr.next τ)) := .msg _ hr hnp
  have hne : (τ.push (pr.next τ)).entries ≠ [] := by simp [PT.push]
  refine ⟨⟨hr', ?_⟩, ?_⟩
  · simpa [PT.push] using drop_succ_of_drop hd
  · obtain ⟨_, _, h3⟩ := hw.shaped _ hr'
    obtain ⟨s, hs, hf⟩ := h3 τ.entries.length (by simp [PT.push])
    rw [slots_of_ne hw hr' hne, hg] at hs
    cases hs
    simp only [PT.push, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem_cons_zero, Udr.Entry.Fits] at hf
    exact forall2_of_fits _ _ hf.1 hf.2

theorem inv_chal (hw : ProverWf V pr cb) {ood : Bool} {ss : List Slot}
    {τ : PT K (Oracle F)} (h : Inv V pr cb (.chal ood :: ss) τ) (y : Bytes) :
    Inv V pr cb ss (τ.pushChal (Bcs.Transport.decChal (F := F) ood y)) := by
  obtain ⟨hr, hd⟩ := h
  have hg := getElem?_of_drop hd
  have he : τ.entries ≠ [] := by
    intro he
    obtain ⟨parts, hp⟩ := sched_head hw
    rw [he] at hg; simp at hg; rw [hg] at hp; cases hp
  refine ⟨.chal _ ood y hr (by rw [slots_of_ne hw hr he]; exact hg), ?_⟩
  simpa [PT.pushChal] using drop_succ_of_drop hd

theorem inv_end (hw : ProverWf V pr cb) {τ : PT K (Oracle F)} (h : Inv V pr cb [] τ) :
    V.AtQuery τ ∧ τ.header? = some pr.hdr := by
  obtain ⟨hr, hd⟩ := h
  have he : τ.entries ≠ [] := by
    intro he
    obtain ⟨parts, hp⟩ := sched_head hw
    rw [he] at hd; simp at hd; rw [hd] at hp; cases hp
  have hh := hw.header τ hr he
  refine ⟨⟨by simp [hh], ?_⟩, hh⟩
  rw [slots_of_ne hw hr he]
  have h1 := List.drop_eq_nil_iff.mp hd
  have h2 := (hw.shaped τ hr).2.1
  rw [slots_of_ne hw hr he] at h2
  omega

end

end ZkFormal.Prover
