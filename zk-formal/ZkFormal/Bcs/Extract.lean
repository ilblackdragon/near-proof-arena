import ZkFormal.Bcs.Commit

/-!
# ZkFormal.Bcs.Extract — the deterministic BCS extraction lemma

This is DESIGN.md §6.3 ("riskiest single lemma"), for an *abstract*
public-coin IOP whose prover messages are committed with any binding
commitment scheme `cs` (single-height Merkle: `Bcs.Merkle`; mixed-height
MMCS: `Bcs.Mmcs`).

**Transcript (Fiat–Shamir) encoding.**
* `d₀ = WH(INIT, ctx ‖ le8 |cb| ‖ cb)`;
* a prover message with committed roots `ρ` and raw bytes `μ`:
  `d ← WH(ABS, d ‖ u8 |ρ| ‖ ρ ‖ μ)`;
* a challenge: `d ← WH(CHAL, d)`, and the challenge is the **first half**
  `y = H(CHAL ‖ 1 ‖ d)` of the new state;
* query phase: chunk answers `H(QUERY ‖ d_fin ‖ le4 j)`, `j < numChunks`.

Because the challenge *is* (half of) the next state, every later state
depends on it: a challenge is sampled exactly when the transcript prefix
before it is fixed.  (With a separate `H(CHAL ‖ d)` that does not feed the
state, an adversary can fix later rounds before drawing an earlier
challenge, and the round-by-round potential is no longer well defined.)

**Extraction** (`extPT hist d`): invert `d` in the log `hist`; for each step
take the history at the time of the step's first-half query (`lookupHist`):
for a challenge it is the history in which the challenge was drawn, for a
message the oracles committed by its roots are extracted from it.  Then
recurse on the previous state in that history.  Extraction from any later log
gives the same result (histories are canonical).

**Events** (each bounded by a potential): `RoundBad` (a challenge un-dooms a
doomed extracted prefix), `QuerySuccess` of `Good` (the query phase passes on
a doomed extracted transcript), `WideCollision`, `InvBad`.

**Main theorem** `accept_imp_event`: if the final log certifies an accepting
transcript (`AcceptsIn`) for a claim outside the language, one of the four
events occurred.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

/-! ## Transcripts -/

section
variable {cs : CommitScheme}

/-- A transcript entry as seen by the IOP: a prover message (committed
roots, raw bytes, the committed oracles as extracted) or a challenge (32 raw
oracle bytes). -/
inductive Entry (cs : CommitScheme) where
  | msg (roots : List Bytes) (raw : Bytes) (oracles : List (cs.Pos → Option Bytes))
  | chal (y : Bytes)

/-- The verifier's view of an entry. -/
inductive EntryV where
  | msg (roots : List Bytes) (raw : Bytes)
  | chal (y : Bytes)

/-- Partial transcript (entries oldest first). -/
structure PT (cs : CommitScheme) where
  cb : Bytes
  entries : List (Entry cs)

structure View where
  cb : Bytes
  entries : List EntryV

def Entry.view : Entry cs → EntryV
  | .msg roots raw _ => .msg roots raw
  | .chal y => .chal y

def PT.view (τ : PT cs) : View := ⟨τ.cb, τ.entries.map Entry.view⟩
def PT.push (τ : PT cs) (e : Entry cs) : PT cs := ⟨τ.cb, τ.entries ++ [e]⟩
def View.prefix (vt : View) (r : Nat) : View := ⟨vt.cb, vt.entries.take r⟩

def Entry.oracles : Entry cs → List (cs.Pos → Option Bytes)
  | .msg _ _ os => os
  | .chal _ => []

/-- Value of oracle `o` of entry `r` at `pos`. -/
def PT.oracle (τ : PT cs) (r o : Nat) (pos : cs.Pos) : Option Bytes :=
  (τ.entries[r]?).bind fun e => (e.oracles[o]?).bind fun f => f pos

end

/-- Pointwise relation between two lists. -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a b l l'} : R a b → Forall2 R l l' → Forall2 R (a :: l) (b :: l')

theorem Forall2.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 S l l'
  | _, _, .nil => .nil
  | _, _, .cons hab hl => .cons (h _ _ hab) (Forall2.imp h hl)

/-- The verifier side of an IOP: tree shapes of each round, the query phase
(`numChunks` chunk answers, each yielding query points), the openings each
point needs (`(round, tree, position)`), and the local decision. -/
structure IopSpec (cs : CommitScheme) where
  /-- Shapes of the trees committed by a message (given the view before it
  and its raw bytes). -/
  shapes : View → Bytes → List cs.Shape
  numChunks : Nat
  points : View → Nat → Bytes → List Nat
  opens : View → Nat → List (Nat × Nat × cs.Pos)
  decide : View → Nat → List Bytes → Bool

variable {cs : CommitScheme} (iop : IopSpec cs)

/-- A query point passes with the transcript's (extracted) oracle values. -/
def Pass (τ : PT cs) (pt : Nat) : Prop :=
  ∃ vals, Forall2 (fun q v => τ.oracle q.1 q.2.1 q.2.2 = some v) (iop.opens τ.view pt) vals ∧
    iop.decide τ.view pt vals = true

/-! ## Extraction -/

/-- The oracles committed in a round, extracted from `hist`. -/
noncomputable def extOracles (hist : Table) (vb : View) (roots : List Bytes) (raw : Bytes) :
    List (cs.Pos → Option Bytes) :=
  (roots.zip (iop.shapes vb raw)).map fun p => cs.ext hist p.1 p.2

/-- **Transcript extraction from the oracle log.** -/
noncomputable def extPT (ctx : Bytes) (hist : Table) (d : Bytes) : Option (PT cs) :=
  match invert hist d with
  | some (t :: rest) =>
    if t = tagInit then
      if rest.take ctx.length = ctx then some ⟨rest.drop (ctx.length + 8), []⟩ else none
    else if t = tagAbs then
      match h : lookupHist hist (whq (t :: rest) 0) with
      | some (_, hist') =>
        (extPT ctx hist' (parseAbs rest).1).map fun τ =>
          τ.push (.msg (parseAbs rest).2.1 (parseAbs rest).2.2
            (extOracles iop hist' τ.view (parseAbs rest).2.1 (parseAbs rest).2.2))
      | none => none
    else if t = tagChal then
      match h : lookupHist hist (whq (t :: rest) 0) with
      | some (y, hist') => (extPT ctx hist' rest).map fun τ => τ.push (.chal y)
      | none => none
    else none
  | _ => none
termination_by hist.length
decreasing_by all_goals exact lookupHist_length h

/-! ## The verifier's acceptance condition, on the final log -/

/-- The log certifies the transcript chain `d₀ → … → d` with verifier view
`es` (entries oldest first). -/
inductive Chain (tbl : Table) (ctx cb : Bytes) : List EntryV → Bytes → Prop
  | init (d : Bytes) : WHin tbl (initMsg ctx cb) d → Chain tbl ctx cb [] d
  | msg (es : List EntryV) (d : Bytes) (roots : List Bytes) (raw d' : Bytes) :
      Chain tbl ctx cb es d → (∀ r ∈ roots, r.length = 64) → roots.length < 256 →
      WHin tbl (absMsg d roots raw) d' → Chain tbl ctx cb (es ++ [.msg roots raw]) d'
  | chal (es : List EntryV) (d a b : Bytes) :
      Chain tbl ctx cb es d →
      tbl.lookup (whq (chalMsg d) 0) = some a → tbl.lookup (whq (chalMsg d) 1) = some b →
      Chain tbl ctx cb (es ++ [.chal a]) (a ++ b)

/-- Roots of a message entry of the view. -/
def EntryV.roots : EntryV → List Bytes
  | .msg roots _ => roots
  | .chal _ => []

def EntryV.raw : EntryV → Bytes
  | .msg _ raw => raw
  | .chal _ => []

/-- The log certifies opening `q = (entry, tree, pos)` with value `v`. -/
def OpenAt (tbl : Table) (vt : View) (q : Nat × Nat × cs.Pos) (v : Bytes) : Prop :=
  ∃ e root sh, vt.entries[q.1]? = some e ∧ e.roots[q.2.1]? = some root ∧
    (iop.shapes (vt.prefix q.1) e.raw)[q.2.1]? = some sh ∧ cs.OpenIn tbl root sh q.2.2 v

/-- **What an accepting verifier run certifies about its final oracle log.**
A concrete verifier (L4) proves `evalT tbl (V.tree pub cb pb) = some true →
AcceptsIn iop tbl ctx cb`. -/
def AcceptsIn (tbl : Table) (ctx cb : Bytes) : Prop :=
  ∃ es d, Chain tbl ctx cb es d ∧ ∀ j, j < iop.numChunks → ∃ y, tbl.lookup (chunkQ d j) = some y ∧
    ∀ pt ∈ iop.points ⟨cb, es⟩ j y, ∃ vals, Forall2 (OpenAt iop tbl ⟨cb, es⟩) (iop.opens ⟨cb, es⟩ pt) vals ∧
      iop.decide ⟨cb, es⟩ pt vals = true

/-! ## The events -/

variable (Doomed : PT cs → Prop) (ctx : Bytes)

/-- **Commit-phase event**: the challenge `y` (first half of `WH(CHAL, d)`)
un-dooms the doomed transcript prefix extracted from the log at the time it
is drawn. -/
def RoundBad (hist : Table) (x y : Bytes) : Prop :=
  ∃ d τ, x = whq (chalMsg d) 0 ∧ extPT iop ctx hist d = some τ ∧ Doomed τ ∧
    ¬ Doomed (τ.push (.chal y))

/-- **Query-phase goodness** of chunk `j` with answer `y` for final state `p`:
the transcript extracted at that time is doomed and all of the chunk's query
points pass. -/
def Good (hist : Table) (p : Bytes) (j : Nat) (y : Bytes) : Prop :=
  ∃ τ, extPT iop ctx hist p = some τ ∧ Doomed τ ∧ ∀ pt ∈ iop.points τ.view j y, Pass iop τ pt

/-! ## Proof -/

theorem chain_produced {tbl : Table} {cb : Bytes} {es : List EntryV} {d : Bytes}
    (h : Chain tbl ctx cb es d) : ∃ m, WHin tbl m d := by
  cases h with
  | init d hd => exact ⟨_, hd⟩
  | msg es d roots raw d' _ _ _ hd => exact ⟨_, hd⟩
  | chal es d a b _ ha hb => exact ⟨_, a, b, ha, hb, rfl⟩

/-- The extracted oracles agree with every opening the final log certifies. -/
def BoundTo (tbl : Table) (τ : PT cs) : Prop :=
  ∀ q v, OpenAt iop tbl τ.view q v → τ.oracle q.1 q.2.1 q.2.2 = some v

theorem PT.view_push (τ : PT cs) (e : Entry cs) :
    (τ.push e).view = ⟨τ.view.cb, τ.view.entries ++ [e.view]⟩ := by
  simp [PT.push, PT.view]

theorem extPT_init (hist : Table) (d : Bytes) (cb : Bytes) (h : invert hist d = some (initMsg ctx cb)) :
    extPT iop ctx hist d = some ⟨cb, []⟩ := by
  rw [extPT, h]
  have hl := Bytes.leN_length 8 cb.length
  simp only [initMsg, tagInit, if_true, List.append_assoc, List.take_left', ite_true]
  rw [← List.drop_drop, List.drop_left' rfl, List.drop_left' hl]

theorem extPT_abs (hist hist' : Table) (d dprev : Bytes) (roots : List Bytes) (raw y : Bytes)
    (hdl : dprev.length = 64) (hr : ∀ r ∈ roots, r.length = 64) (hn : roots.length < 256)
    (h : invert hist d = some (absMsg dprev roots raw))
    (hl : lookupHist hist (whq (absMsg dprev roots raw) 0) = some (y, hist')) :
    extPT iop ctx hist d = (extPT iop ctx hist' dprev).map fun τ =>
      τ.push (.msg roots raw (extOracles iop hist' τ.view roots raw)) := by
  rw [extPT, h]
  have hp := parseAbs_absMsg dprev roots raw hdl hr hn
  simp only [absMsg] at hl ⊢
  simp only [show (tagAbs = tagInit) = False by decide, if_false, if_true, ite_true, ite_false]
  split
  · rename_i y' hist'' heq
    rw [hl] at heq
    cases heq
    rw [hp]
  · rename_i heq
    rw [hl] at heq; cases heq

theorem extPT_chal (hist hist' : Table) (d dprev y : Bytes)
    (h : invert hist d = some (chalMsg dprev))
    (hl : lookupHist hist (whq (chalMsg dprev) 0) = some (y, hist')) :
    extPT iop ctx hist d = (extPT iop ctx hist' dprev).map fun τ => τ.push (.chal y) := by
  rw [extPT, h]
  simp only [chalMsg] at hl ⊢
  simp only [show (tagChal = tagInit) = False by decide, show (tagChal = tagAbs) = False by decide,
    if_false, if_true, ite_true, ite_false]
  split
  · rename_i y' hist'' heq
    rw [hl] at heq
    cases heq
    rfl
  · rename_i heq
    rw [hl] at heq; cases heq

/-- The entry of a pushed transcript. -/
theorem PT.oracle_push_lt (τ : PT cs) (e : Entry cs) {r : Nat} (hr : r < τ.entries.length) (o : Nat)
    (pos : cs.Pos) : (τ.push e).oracle r o pos = τ.oracle r o pos := by
  unfold PT.oracle PT.push
  simp only
  rw [List.getElem?_append_left hr]

theorem PT.view_length (τ : PT cs) : τ.view.entries.length = τ.entries.length := by
  simp [PT.view]

section
variable {iop Doomed ctx}

/-- Splitting the log at the first-half query of a step whose output is
produced in `hist`. -/
theorem step_split {p hist : Table} (wf : TableWF (p ++ hist)) (hcol : ¬ WideCollision 2 whq (p ++ hist))
    {M u : Bytes} (hM : WHin (p ++ hist) M u) (hp : ∃ m, WHin hist m u) :
    ∃ a hist' mid, (p ++ hist).lookup (whq M 0) = some a ∧ invert hist u = some M ∧
      lookupHist hist (whq M 0) = some (a, hist') ∧ hist = mid ++ (whq M 0, a) :: hist' := by
  have hinv := invert_eq wf hcol hM hp
  have hMh : WHin hist M u := by
    obtain ⟨m', hm'⟩ := hp
    exact (wh_unique wf hcol (WHin.suffix wf.1 hm') hM) ▸ hm'
  obtain ⟨a, b, ha, hb, _⟩ := hMh
  obtain ⟨hist', hlh⟩ := lookupHist_of_lookup ha
  obtain ⟨mid, hmid⟩ := split_of_lookupHist hlh
  exact ⟨a, hist', mid, lookup_suffix wf.1 ha, hinv, hlh, hmid⟩

/-- **Chain extraction.**  Every certified chain state, produced in some
earlier log `hist`, extracts from `hist` to a doomed transcript with the
verifier's view, whose oracles are bound to the final log. -/
theorem chain_extract {pre : Table} {cb : Bytes} (hL : Doomed ⟨cb, []⟩)
    (hmsg : ∀ τ roots raw os, Doomed τ → Doomed (τ.push (.msg roots raw os)))
    (wf : TableWF pre) (hcol : ¬ WideCollision 2 whq pre) (hni : NoInv pre)
    (hrb : ¬ BadHist (RoundBad iop Doomed ctx) pre)
    (hbind : cs.Binding) (hroot : cs.Rooted) {es : List EntryV} {d : Bytes}
    (hch : Chain pre ctx cb es d) :
    ∀ (p hist : Table), pre = p ++ hist → (∃ m, WHin hist m d) →
      ∃ τ, extPT iop ctx hist d = some τ ∧ τ.view = ⟨cb, es⟩ ∧ Doomed τ ∧ BoundTo iop pre τ := by
  induction hch with
  | init d hd =>
    intro p hist hsplit hp
    subst hsplit
    refine ⟨⟨cb, []⟩, extPT_init iop ctx hist d cb (invert_eq wf hcol hd hp), rfl, hL, ?_⟩
    intro q v hq
    obtain ⟨e, _, _, h1, _⟩ := hq
    simp [PT.view] at h1
  | msg es d roots raw d' hch hr hn hd' ih =>
    intro p hist hsplit hp
    subst hsplit
    obtain ⟨a, hist', mid, _, hinv, hlh, hmid⟩ := step_split wf hcol hd' hp
    have hsplit2 : p ++ hist = (p ++ mid) ++ (whq (absMsg d roots raw) 0, a) :: hist' := by
      rw [hmid]; simp
    have hsplit3 : p ++ hist = (p ++ mid ++ [(whq (absMsg d roots raw) 0, a)]) ++ hist' := by
      rw [hsplit2]; simp
    obtain ⟨md, hmd⟩ := chain_produced ctx hch
    have hdl : d.length = 64 := WHin.length wf hmd
    have hsl := slots_absMsg d roots raw hdl hr hn 0 (by omega)
    have hdh' : WHin hist' md d := hni _ _ _ _ hsplit2 d hsl.1 md hmd
    obtain ⟨τ, hτ, hview, hdoom, hbound⟩ := ih _ hist' hsplit3 ⟨md, hdh'⟩
    rw [extPT_abs iop ctx hist hist' d' d roots raw a hdl hr hn hinv hlh, hτ]
    simp only [Option.map_some]
    refine ⟨_, rfl, ?_, hmsg _ _ _ _ hdoom, ?_⟩
    · rw [PT.view_push, hview]; rfl
    · intro q v hq
      obtain ⟨e, root, sh, h1, h2, h3, h4⟩ := hq
      rw [PT.view_push, hview] at h1 h3
      simp only [View.prefix, Entry.view] at h1 h3
      have hlen : τ.entries.length = es.length := by
        have := congrArg (fun vt => vt.entries.length) hview
        simp [PT.view] at this; omega
      by_cases hq1 : q.1 < es.length
      · rw [List.getElem?_append_left hq1] at h1
        rw [List.take_append_of_le_length (Nat.le_of_lt hq1)] at h3
        rw [PT.oracle_push_lt τ _ (hlen ▸ hq1)]
        exact hbound q v ⟨e, root, sh, by rw [hview]; exact h1, h2, by rw [hview]; exact h3, h4⟩
      · have hq1' : q.1 = es.length := by
          have := (List.getElem?_eq_some_iff.mp h1).1
          simp at this; omega
        rw [hq1'] at h1 h3
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
          Option.some.injEq] at h1
        subst h1
        rw [List.take_left' rfl] at h3
        simp only [EntryV.roots, EntryV.raw] at h2 h3
        unfold PT.oracle
        simp only [PT.push]
        rw [hq1', ← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.bind_some, Entry.oracles, extOracles]
        have hz : (roots.zip (iop.shapes τ.view raw))[q.2.1]? = some (root, sh) :=
          List.getElem?_zip_eq_some.mpr ⟨h2, by rw [hview]; exact h3⟩
        rw [List.getElem?_map, hz]
        simp only [Option.map_some, Option.bind_some]
        -- binding: the root was produced before the message was absorbed
        obtain ⟨mr, hmr⟩ := hroot _ _ _ _ _ h4
        have hrh' : WHin hist' mr root :=
          hni _ _ _ _ hsplit2 root (hsl.2 root (List.mem_of_getElem? h2)) mr hmr
        rw [hsplit3] at h4 wf hcol hni
        exact hbind _ _ wf hcol hni root sh q.2.2 v h4 ⟨mr, hrh'⟩
  | chal es d a b hch ha hb ih =>
    intro p hist hsplit hp
    subst hsplit
    obtain ⟨a', hist', mid, ha', hinv, hlh, hmid⟩ := step_split wf hcol ⟨a, b, ha, hb, rfl⟩ hp
    rw [ha] at ha'; cases ha'
    have hsplit2 : p ++ hist = (p ++ mid) ++ (whq (chalMsg d) 0, a) :: hist' := by
      rw [hmid]; simp
    have hsplit3 : p ++ hist = (p ++ mid ++ [(whq (chalMsg d) 0, a)]) ++ hist' := by
      rw [hsplit2]; simp
    obtain ⟨md, hmd⟩ := chain_produced ctx hch
    have hdl : d.length = 64 := WHin.length wf hmd
    have hdh' : WHin hist' md d := hni _ _ _ _ hsplit2 d (slots_chalMsg d hdl 0 (by omega)) md hmd
    obtain ⟨τ, hτ, hview, hdoom, hbound⟩ := ih _ hist' hsplit3 ⟨md, hdh'⟩
    rw [extPT_chal iop ctx hist hist' (a ++ b) d a hinv hlh, hτ]
    simp only [Option.map_some]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [PT.view_push, hview]; rfl
    · refine Classical.byContradiction fun hnd => hrb ?_
      rw [hsplit2]
      exact badHist_of_split _ _ ⟨d, τ, rfl, hτ, hdoom, hnd⟩
    · intro q v hq
      obtain ⟨e, root, sh, h1, h2, h3, h4⟩ := hq
      rw [PT.view_push, hview] at h1 h3
      simp only [View.prefix, Entry.view] at h1 h3
      have hlen : τ.entries.length = es.length := by
        have := congrArg (fun vt => vt.entries.length) hview
        simp [PT.view] at this; omega
      by_cases hq1 : q.1 < es.length
      · rw [List.getElem?_append_left hq1] at h1
        rw [List.take_append_of_le_length (Nat.le_of_lt hq1)] at h3
        rw [PT.oracle_push_lt τ _ (hlen ▸ hq1)]
        exact hbound q v ⟨e, root, sh, by rw [hview]; exact h1, h2, by rw [hview]; exact h3, h4⟩
      · exfalso
        have hq1' : q.1 = es.length := by
          have := (List.getElem?_eq_some_iff.mp h1).1
          simp at this; omega
        rw [hq1'] at h1
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
          Option.some.injEq] at h1
        subst h1
        simp [EntryV.roots] at h2
end

/-- **The deterministic extraction lemma** (DESIGN.md §6.3, `accept_imp_event`,
generic form).  If the final oracle log certifies acceptance of `cb`, the
initial state for `cb` is doomed (e.g. `cb ∉ L`) and prover messages never
un-doom, then one of the four events is in the log. -/
theorem accept_imp_event_log {iop : IopSpec cs} {Doomed : PT cs → Prop} {ctx : Bytes}
    (hbind : cs.Binding) (hroot : cs.Rooted)
    (hmsg : ∀ τ roots raw os, Doomed τ → Doomed (τ.push (.msg roots raw os)))
    {tbl : Table} (wf : TableWF tbl) {cb : Bytes} (hL : Doomed ⟨cb, []⟩)
    (hacc : AcceptsIn iop tbl ctx cb) :
    BadHist (RoundBad iop Doomed ctx) tbl ∨ QuerySuccess iop.numChunks chunkQ (Good iop Doomed ctx) tbl ∨
      WideCollision 2 whq tbl ∨ BadHist InvBad tbl := by
  refine Classical.byContradiction fun hno => ?_
  have hrb : ¬ BadHist (RoundBad iop Doomed ctx) tbl := fun h => hno (Or.inl h)
  have hqs : ¬ QuerySuccess iop.numChunks chunkQ (Good iop Doomed ctx) tbl := fun h => hno (Or.inr (Or.inl h))
  have hcol : ¬ WideCollision 2 whq tbl := fun h => hno (Or.inr (Or.inr (Or.inl h)))
  have hni : NoInv tbl := noInv_of wf fun h => hno (Or.inr (Or.inr (Or.inr h)))
  apply hqs
  obtain ⟨es, d, hch, hq⟩ := hacc
  refine ⟨d, fun j hj => ?_⟩
  obtain ⟨y, hy, hpts⟩ := hq j hj
  obtain ⟨hist, hlh⟩ := lookupHist_of_lookup hy
  obtain ⟨pre, hpre⟩ := split_of_lookupHist hlh
  refine ⟨y, hist, hlh, ?_⟩
  obtain ⟨md, hmd⟩ := chain_produced ctx hch
  have hdh : WHin hist md d := hni _ _ _ _ hpre d (slots_chunkQ d j) md hmd
  have hsplit : tbl = (pre ++ [(chunkQ d j, y)]) ++ hist := by rw [hpre]; simp
  obtain ⟨τ, hτ, hview, hdoom, hbound⟩ :=
    chain_extract hL hmsg wf hcol hni hrb hbind hroot hch _ hist hsplit ⟨md, hdh⟩
  refine ⟨τ, hτ, hdoom, fun pt hpt => ?_⟩
  rw [hview] at hpt
  obtain ⟨vals, hvals, hdec⟩ := hpts pt hpt
  refine ⟨vals, ?_, by rw [hview]; exact hdec⟩
  rw [hview]
  exact Forall2.imp (fun q v hqv => hbound q v (by rw [hview]; exact hqv)) hvals

end ZkFormal.Bcs
