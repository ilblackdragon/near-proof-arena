import ZkFormal.Bcs.Commit

/-!
# ZkFormal.Bcs.Extract — the deterministic BCS extraction lemma

This is DESIGN.md §6.3 ("riskiest single lemma"), for an *abstract*
public-coin IOP whose prover messages are committed with any binding
commitment scheme `cs` (single-height Merkle: `Bcs.Merkle`; mixed-height
MMCS: `Bcs.Mmcs`).

**Transcript (Fiat–Shamir) encoding.**
* `d₀ = WH(INIT ‖ ctx ‖ cb)`;
* round `k`: the prover sends roots `ρ_k` and a clear message `μ_k`;
  `d_{k+1} = WH(ABS ‖ d_k ‖ |ρ_k| ‖ ρ_k ‖ μ_k)`, and the round challenge is the
  **first half** `y_k = H(0x01 ‖ ABS ‖ …)` of `d_{k+1}`;
* query phase: chunk answers `H(0x03 ‖ d_fin ‖ be4 j)`, `j < numChunks`.

Deriving the challenge from the absorb output itself (instead of a separate
`H(CHAL ‖ d_k)` query) makes the challenge of round `k` *sampled at the
moment the round's message is fixed*: every later state depends on it.

**Extraction** (`extPT hist d`): invert `d` in the log `hist`; for an absorb
message, read the challenge *and the history at the time it was sampled*
(`lookupHist`), extract the round's committed oracles from that history, and
recurse on the previous state in that history.  Every object is therefore
extracted from the log as it stood when the following challenge was drawn.

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

/-- A round as seen by the IOP: committed roots, clear message, challenge
(32 raw oracle bytes), and the committed oracles (as extracted). -/
structure Round where
  roots : List Bytes
  clear : Bytes
  chal : Bytes
  oracles : List (Nat → Option Bytes)

/-- The verifier's view of a round. -/
structure RoundV where
  roots : List Bytes
  clear : Bytes
  chal : Bytes

/-- Partial transcript (rounds oldest first). -/
structure PT where
  cb : Bytes
  rounds : List Round

structure View where
  cb : Bytes
  rounds : List RoundV

def Round.view (r : Round) : RoundV := ⟨r.roots, r.clear, r.chal⟩
def PT.view (τ : PT) : View := ⟨τ.cb, τ.rounds.map Round.view⟩
def PT.push (τ : PT) (r : Round) : PT := ⟨τ.cb, τ.rounds ++ [r]⟩
def View.prefix (vt : View) (r : Nat) : View := ⟨vt.cb, vt.rounds.take r⟩

/-- Value of oracle `o` of round `r` at `pos`. -/
def PT.oracle (τ : PT) (r o pos : Nat) : Option Bytes :=
  (τ.rounds[r]?).bind fun rd => (rd.oracles[o]?).bind fun f => f pos

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
  shapes : View → Bytes → List cs.Shape
  numChunks : Nat
  points : View → Nat → Bytes → List Nat
  opens : View → Nat → List (Nat × Nat × Nat)
  decide : View → Nat → List Bytes → Bool

variable {cs : CommitScheme} (iop : IopSpec cs)

/-- A query point passes with the transcript's (extracted) oracle values. -/
def Pass (τ : PT) (pt : Nat) : Prop :=
  ∃ vals, Forall2 (fun q v => τ.oracle q.1 q.2.1 q.2.2 = some v) (iop.opens τ.view pt) vals ∧
    iop.decide τ.view pt vals = true

/-! ## Extraction -/

/-- The oracles committed in a round, extracted from `hist`. -/
noncomputable def extOracles (hist : Table) (vb : View) (roots : List Bytes) (clear : Bytes) :
    List (Nat → Option Bytes) :=
  (roots.zip (iop.shapes vb clear)).map fun p => cs.ext hist p.1 p.2

/-- **Transcript extraction from the oracle log.** -/
noncomputable def extPT (ctx : Bytes) (hist : Table) (d : Bytes) : Option PT :=
  match invert hist d with
  | some (t :: rest) =>
    if t = tagInit then
      if rest.take ctx.length = ctx then some ⟨rest.drop ctx.length, []⟩ else none
    else if t = tagAbs then
      match h : lookupHist hist (whq (t :: rest) 0) with
      | some (y, hist') =>
        (extPT ctx hist' (parseAbs rest).1).map fun τ =>
          τ.push ⟨(parseAbs rest).2.1, (parseAbs rest).2.2, y,
            extOracles iop hist' τ.view (parseAbs rest).2.1 (parseAbs rest).2.2⟩
      | none => none
    else none
  | _ => none
termination_by hist.length
decreasing_by exact lookupHist_length h

/-! ## The verifier's acceptance condition, on the final log -/

/-- The log certifies the transcript chain `d₀ → … → d` with verifier view
`rs` (rounds oldest first). -/
inductive Chain (tbl : Table) (ctx cb : Bytes) : List RoundV → Bytes → Prop
  | init (d : Bytes) : WHin tbl (initMsg ctx cb) d → Chain tbl ctx cb [] d
  | step (rs : List RoundV) (d : Bytes) (roots : List Bytes) (clear a b : Bytes) :
      Chain tbl ctx cb rs d → (∀ r ∈ roots, r.length = 64) → roots.length < 256 →
      tbl.lookup (whq (absMsg d roots clear) 0) = some a →
      tbl.lookup (whq (absMsg d roots clear) 1) = some b →
      Chain tbl ctx cb (rs ++ [⟨roots, clear, a⟩]) (a ++ b)

/-- The log certifies opening `q = (round, tree, pos)` with value `v`. -/
def OpenAt (tbl : Table) (vt : View) (q : Nat × Nat × Nat) (v : Bytes) : Prop :=
  ∃ rd root sh, vt.rounds[q.1]? = some rd ∧ rd.roots[q.2.1]? = some root ∧
    (iop.shapes (vt.prefix q.1) rd.clear)[q.2.1]? = some sh ∧ cs.OpenIn tbl root sh q.2.2 v

/-- **What an accepting verifier run certifies about its final oracle log.**
A concrete verifier (L4) proves `evalT tbl (V.tree pub cb pb) = some true →
AcceptsIn iop tbl ctx cb`; `Bcs.Compile` gives a reference verifier. -/
def AcceptsIn (tbl : Table) (ctx cb : Bytes) : Prop :=
  ∃ rs d, Chain tbl ctx cb rs d ∧ ∀ j, j < iop.numChunks → ∃ y, tbl.lookup (chunkQ d j) = some y ∧
    ∀ pt ∈ iop.points ⟨cb, rs⟩ j y, ∃ vals, Forall2 (OpenAt iop tbl ⟨cb, rs⟩) (iop.opens ⟨cb, rs⟩ pt) vals ∧
      iop.decide ⟨cb, rs⟩ pt vals = true

/-! ## The events -/

variable (Doomed : PT → Prop) (ctx : Bytes)

/-- **Commit-phase event**: the challenge `y` sampled for an absorb query
un-dooms the doomed transcript prefix extracted from the log at that time. -/
def RoundBad (hist : Table) (x y : Bytes) : Prop :=
  ∃ rest τ, x = whq (tagAbs :: rest) 0 ∧ extPT iop ctx hist (parseAbs rest).1 = some τ ∧ Doomed τ ∧
    ¬ Doomed (τ.push ⟨(parseAbs rest).2.1, (parseAbs rest).2.2, y,
      extOracles iop hist τ.view (parseAbs rest).2.1 (parseAbs rest).2.2⟩)

/-- **Query-phase goodness** of chunk `j` with answer `y` for final state `p`:
the transcript extracted at that time is doomed and all of the chunk's query
points pass. -/
def Good (hist : Table) (p : Bytes) (j : Nat) (y : Bytes) : Prop :=
  ∃ τ, extPT iop ctx hist p = some τ ∧ Doomed τ ∧ ∀ pt ∈ iop.points τ.view j y, Pass iop τ pt

/-! ## Proof -/

theorem chain_produced {tbl : Table} {cb : Bytes} {rs : List RoundV} {d : Bytes}
    (h : Chain tbl ctx cb rs d) : ∃ m, WHin tbl m d := by
  cases h with
  | init d hd => exact ⟨_, hd⟩
  | step rs d roots clear a b _ _ _ ha hb => exact ⟨_, a, b, ha, hb, rfl⟩

/-- The extracted oracles agree with every opening the final log certifies. -/
def BoundTo (tbl : Table) (τ : PT) : Prop :=
  ∀ q v, OpenAt iop tbl τ.view q v → τ.oracle q.1 q.2.1 q.2.2 = some v

theorem PT.view_push (τ : PT) (r : Round) :
    (τ.push r).view = ⟨τ.view.cb, τ.view.rounds ++ [r.view]⟩ := by
  simp [PT.push, PT.view]

theorem extPT_init (hist : Table) (d : Bytes) (cb : Bytes) (h : invert hist d = some (initMsg ctx cb)) :
    extPT iop ctx hist d = some ⟨cb, []⟩ := by
  rw [extPT, h]
  simp [initMsg, tagInit, List.take_left', List.drop_left']

theorem extPT_abs (hist hist' : Table) (d dprev : Bytes) (roots : List Bytes) (clear y : Bytes)
    (hdl : dprev.length = 64) (hr : ∀ r ∈ roots, r.length = 64) (hn : roots.length < 256)
    (h : invert hist d = some (absMsg dprev roots clear))
    (hl : lookupHist hist (whq (absMsg dprev roots clear) 0) = some (y, hist')) :
    extPT iop ctx hist d = (extPT iop ctx hist' dprev).map fun τ =>
      τ.push ⟨roots, clear, y, extOracles iop hist' τ.view roots clear⟩ := by
  rw [extPT, h]
  have hp := parseAbs_absMsg dprev roots clear hdl hr hn
  simp only [absMsg] at hl ⊢
  simp only [show (tagAbs = tagInit) = False by decide, if_false, if_true]
  split
  · rename_i y' hist'' heq
    rw [hl] at heq
    cases heq
    rw [hp]
  · rename_i heq
    rw [hl] at heq; cases heq

section
variable {iop Doomed ctx}

/-- **Chain extraction.**  Every certified chain state, produced in some
earlier log `hist`, extracts from `hist` to a doomed transcript with the
verifier's view whose oracles are bound to the final log. -/
theorem chain_extract {pre : Table} {cb : Bytes} (hL : Doomed ⟨cb, []⟩)
    (wf : TableWF pre) (hcol : ¬ WideCollision 2 whq pre) (hni : NoInv pre)
    (hrb : ¬ BadHist (RoundBad iop Doomed ctx) pre)
    (hbind : cs.Binding) (hroot : cs.Rooted) {rs : List RoundV} {d : Bytes}
    (hch : Chain pre ctx cb rs d) :
    ∀ (p hist : Table), pre = p ++ hist → (∃ m, WHin hist m d) →
      ∃ τ, extPT iop ctx hist d = some τ ∧ τ.view = ⟨cb, rs⟩ ∧ Doomed τ ∧ BoundTo iop pre τ := by
  induction hch with
  | init d hd =>
    intro p hist hsplit hp
    subst hsplit
    refine ⟨⟨cb, []⟩, extPT_init iop ctx hist d cb (invert_eq wf hcol hd hp), rfl, hL, ?_⟩
    intro q v hq
    obtain ⟨rd, _, _, h1, _⟩ := hq
    simp [PT.view] at h1
  | step rs d roots clear a b hch hr hn ha hb ih =>
    intro p hist hsplit hp
    subst hsplit
    have hM : WHin (p ++ hist) (absMsg d roots clear) (a ++ b) := ⟨a, b, ha, hb, rfl⟩
    have hinv := invert_eq wf hcol hM hp
    have hMh : WHin hist (absMsg d roots clear) (a ++ b) := by
      obtain ⟨m', hm'⟩ := hp
      exact (wh_unique wf hcol (WHin.suffix wf.1 hm') hM) ▸ hm'
    obtain ⟨a', b', ha', hb', _⟩ := hMh
    have haa : a' = a := by
      have := lookup_suffix wf.1 ha'; rw [ha] at this; cases this; rfl
    subst haa
    obtain ⟨hist', hlh⟩ := lookupHist_of_lookup ha'
    obtain ⟨mid, hmid⟩ := split_of_lookupHist hlh
    have hsplit2 : p ++ hist = (p ++ mid) ++ (whq (absMsg d roots clear) 0, a') :: hist' := by
      rw [hmid]; simp
    have hsplit3 : p ++ hist = (p ++ mid ++ [(whq (absMsg d roots clear) 0, a')]) ++ hist' := by
      rw [hsplit2]; simp
    obtain ⟨md, hmd⟩ := chain_produced ctx hch
    have hdl : d.length = 64 := WHin.length wf hmd
    have hsl := slots_absMsg d roots clear hdl hr hn 0
    have hdh' : WHin hist' md d := hni _ _ _ _ hsplit2 d hsl.1 md hmd
    obtain ⟨τ, hτ, hview, hdoom, hbound⟩ := ih _ hist' hsplit3 ⟨md, hdh'⟩
    rw [extPT_abs iop ctx hist hist' (a' ++ b) d roots clear a' hdl hr hn hinv hlh, hτ]
    simp only [Option.map_some]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [PT.view_push, hview]; rfl
    · refine Classical.byContradiction fun hnd => hrb ?_
      rw [hsplit2]
      apply badHist_of_split
      have hp' := parseAbs_absMsg d roots clear hdl hr hn
      refine ⟨d ++ (roots.length.toUInt8 :: (roots.flatten ++ clear)), τ, rfl, ?_, hdoom, ?_⟩
      · rw [hp']; exact hτ
      · rw [hp']; exact hnd
    · intro q v hq
      obtain ⟨rd, root, sh, h1, h2, h3, h4⟩ := hq
      rw [PT.view_push, hview] at h1 h3
      simp only [View.prefix, Round.view] at h1 h3
      by_cases hq1 : q.1 < rs.length
      · -- an earlier round
        have e1 : (rs ++ [(⟨roots, clear, a'⟩ : RoundV)])[q.1]? = rs[q.1]? := List.getElem?_append_left hq1
        have e2 : (rs ++ [(⟨roots, clear, a'⟩ : RoundV)]).take q.1 = rs.take q.1 :=
          List.take_append_of_le_length (Nat.le_of_lt hq1)
        rw [e1] at h1; rw [e2] at h3
        have := hbound q v ⟨rd, root, sh, by rw [hview]; exact h1, h2, by rw [hview]; exact h3, h4⟩
        unfold PT.oracle at this ⊢
        simp only [PT.push]
        have hlen : q.1 < τ.rounds.length := by
          have := congrArg (fun vt => vt.rounds.length) hview
          simp [PT.view] at this; omega
        rw [List.getElem?_append_left hlen]
        exact this
      · -- the new round
        have hq1' : q.1 = rs.length := by
          have : q.1 < rs.length + 1 := by
            have := List.getElem?_eq_some_iff.mp h1 |>.1
            simpa using this
          omega
        rw [hq1'] at h1 h3
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
          Option.some.injEq] at h1
        subst h1
        rw [List.take_left' rfl] at h3
        simp only at h2 h3
        have hlen : τ.rounds.length = rs.length := by
          have := congrArg (fun vt => vt.rounds.length) hview
          simp [PT.view] at this; omega
        unfold PT.oracle
        simp only [PT.push]
        rw [hq1', ← hlen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.bind_some, extOracles]
        have hz : (roots.zip (iop.shapes τ.view clear))[q.2.1]? = some (root, sh) :=
          List.getElem?_zip_eq_some.mpr ⟨h2, by rw [hview]; exact h3⟩
        rw [List.getElem?_map, hz]
        simp only [Option.map_some, Option.bind_some]
        -- binding: the root was produced before the challenge was drawn
        obtain ⟨mr, hmr⟩ := hroot _ _ _ _ _ h4
        have hrh' : WHin hist' mr root :=
          hni _ _ _ _ hsplit2 root (hsl.2 root (List.mem_of_getElem? h2)) mr hmr
        rw [hsplit3] at h4 wf hcol hni
        exact hbind _ _ wf hcol hni root sh q.2.2 v h4 ⟨mr, hrh'⟩
end

/-- **The deterministic extraction lemma** (DESIGN.md §6.3, `accept_imp_event`,
generic form).  If the final oracle log certifies acceptance of `cb` and the
initial state for `cb` is doomed (e.g. `cb ∉ L`), then one of the four
events is in the log. -/
theorem accept_imp_event_log {iop : IopSpec cs} {Doomed : PT → Prop} {ctx : Bytes}
    (hbind : cs.Binding) (hroot : cs.Rooted)
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
  obtain ⟨rs, d, hch, hq⟩ := hacc
  refine ⟨d, fun j hj => ?_⟩
  obtain ⟨y, hy, hpts⟩ := hq j hj
  obtain ⟨hist, hlh⟩ := lookupHist_of_lookup hy
  obtain ⟨pre, hpre⟩ := split_of_lookupHist hlh
  refine ⟨y, hist, hlh, ?_⟩
  obtain ⟨md, hmd⟩ := chain_produced ctx hch
  have hdl : d.length = 64 := WHin.length wf hmd
  have hdh : WHin hist md d := hni _ _ _ _ hpre d (slots_chunkQ d hdl j) md hmd
  have hsplit : tbl = (pre ++ [(chunkQ d j, y)]) ++ hist := by rw [hpre]; simp
  obtain ⟨τ, hτ, hview, hdoom, hbound⟩ :=
    chain_extract hL wf hcol hni hrb hbind hroot hch _ hist hsplit ⟨md, hdh⟩
  refine ⟨τ, hτ, hdoom, fun pt hpt => ?_⟩
  rw [hview] at hpt
  obtain ⟨vals, hvals, hdec⟩ := hpts pt hpt
  refine ⟨vals, ?_, by rw [hview]; exact hdec⟩
  rw [hview]
  exact Forall2.imp (fun q v hqv => hbound q v (by rw [hview]; exact hqv)) hvals

end ZkFormal.Bcs
