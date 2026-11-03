import WasmBase.Main.SegView

/-!
# WasmBase.Main.SegLinkSpec — the caller chain as a list of activation ids (E2E M4b, S3)

Spec-side facts the CUTO link (`Main/SegLink.lean`) needs about a cut's caller chain.  The
activation ids of the live frames, current frame first, are `chainIds cid sv = cid :: sv.map cid`:

* `Chain.ids_desc` — strictly decreasing (so the frame at list index `i` has depth `|sv| − i`), the
  bottom one is `0` (`Chain.zero_mem`), all `< 2^28` with the current one;
* `DepthOK.at` — a depth map `σ` (`DepthOK`) sends `chainIds[i]` to `|sv| − i`;
* `chainMsgs_rec` / `chainMsgs_rec_exists` — the live call records (space 4) are exactly one per
  non-bottom frame: the record of the frame at index `i` has slot `chainIds[i]` and caller field
  `l2 = chainIds[i+1]`;
* `RelabelOK` — the data `RelW.relabelV` chooses (chain witness, depth map, kept ids `A`), exported
  so that the AIR side can be matched against the *same* `(σ, A)` as `cutView_eq`'s.
-/

namespace WasmBase

open ZkFormal.Algebra
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- The activation ids of the live frames, current frame first. -/
def chainIds (cid : Nat) (sv : List Saved) : List Nat := cid :: sv.map Saved.cid

@[simp] theorem chainIds_length (cid : Nat) (sv : List Saved) : (chainIds cid sv).length = sv.length + 1 := by
  simp [chainIds]

theorem chainIds_cons (cid : Nat) (c : Saved) (sv : List Saved) :
    chainIds cid (c :: sv) = cid :: chainIds c.cid sv := rfl

section
variable {X : Ctx} {t : Nat}

/-- The ids of a chain decrease strictly from the current frame to the bottom. -/
theorem Chain.ids_desc : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → (chainIds cid sv).Pairwise (· > ·)
  | _, _, _, [], [], _ => by simp [chainIds]
  | cid, _, _, _ :: _, c :: sv, h => by
    rw [chainIds_cons, List.pairwise_cons]
    refine ⟨fun y hy => ?_, Chain.ids_desc h.2.2.2.2.2.2.2.2.2.2.2.2⟩
    have h5 := h.2.2.2.2.1
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h5
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hy
      have := h.2.2.2.2.2.2.2.2.2.2.2.2.ids_lt c' hc'; omega
  | _, _, _, [], _ :: _, h => h.elim
  | _, _, _, _ :: _, [], h => h.elim

/-- The bottom frame's id is `0`. -/
theorem Chain.zero_mem : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → 0 ∈ chainIds cid sv
  | _, _, _, [], [], h => by simp [chainIds, h.1]
  | _, _, _, _ :: _, c :: sv, h => by
    rw [chainIds_cons]; exact List.mem_cons_of_mem _ (Chain.zero_mem h.2.2.2.2.2.2.2.2.2.2.2.2)
  | _, _, _, [], _ :: _, h => h.elim
  | _, _, _, _ :: _, [], h => h.elim

/-- Every id of the chain is at most the current one. -/
theorem Chain.ids_le {cid sb k : Nat} {rest : List Frame} {sv : List Saved}
    (h : Chain X t cid sb k rest sv) : ∀ y ∈ chainIds cid sv, y ≤ cid := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact Nat.le_refl _
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    exact Nat.le_of_lt (h.ids_lt c hc)

/-- A depth map sends the id at list index `i` to the depth `|sv| − i`. -/
theorem DepthOK.at {σ : Nat → Nat} : ∀ {cid : Nat} {sv : List Saved}, DepthOK σ cid sv →
    ∀ i (hi : i < (chainIds cid sv).length), σ ((chainIds cid sv)[i]) = sv.length - i
  | _, [], h, 0, _ => by simp only [chainIds, List.map_nil, List.getElem_cons_zero, List.length_nil]; exact h
  | _, [], _, _ + 1, hi => by simp at hi
  | _, c :: sv, h, 0, _ => by simpa [chainIds] using h.1
  | _, c :: sv, h, i + 1, hi => by
    have := DepthOK.at h.2 i (by simp at hi ⊢; omega)
    simp only [chainIds_cons, List.getElem_cons_succ, List.length_cons]
    rw [this]; omega

/-- **A live call record is the record of a non-bottom frame**: its slot is the id at index `i`
and its caller field `l2` the id at index `i + 1`. -/
theorem chainMsgs_rec : ∀ {cid k : Nat} {rest : List Frame} {sv : List Saved} {x : Msg},
    chainMsgs X cid k rest sv x → x.space = 4 →
      ∃ i, ∃ hi : i + 1 < (chainIds cid sv).length,
        x.slot = (chainIds cid sv)[i] ∧ x.l2 = (chainIds cid sv)[i + 1]
  | _, _, [], [], _, h, _ => h.elim
  | cid, _, _ :: _, c :: sv, x, h, h4 => by
    rcases h with rfl | h | h
    · exact ⟨0, by simp, by simp [callMsg, chainIds], by simp [callMsg, chainIds]⟩
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc] at h4; omega
    · obtain ⟨i, hi, e1, e2⟩ := chainMsgs_rec h h4
      refine ⟨i + 1, by simp at hi ⊢; omega, ?_, ?_⟩
      · simpa [chainIds_cons] using e1
      · simpa [chainIds_cons] using e2
  | _, _, [], _ :: _, _, h, _ => h.elim
  | _, _, _ :: _, [], _, h, _ => h.elim

/-- **Every non-bottom frame has its call record among the chain messages.** -/
theorem chainMsgs_rec_exists : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → ∀ i (hi : i + 1 < (chainIds cid sv).length),
      ∃ x, chainMsgs X cid k rest sv x ∧ x.space = 4 ∧ x.slot = (chainIds cid sv)[i]
  | _, _, _, [], [], _, i, hi => by simp at hi
  | cid, _, k, fc :: rest, c :: sv, h, 0, _ =>
    ⟨_, Or.inl rfl, rfl, by simp [callMsg, chainIds]⟩
  | cid, _, k, fc :: rest, c :: sv, h, i + 1, hi => by
    obtain ⟨x, hx, h4, hs⟩ := chainMsgs_rec_exists h.2.2.2.2.2.2.2.2.2.2.2.2 i (by simp at hi ⊢; omega)
    exact ⟨x, Or.inr (Or.inr hx), h4, by simpa [chainIds_cons] using hs⟩
  | _, _, _, [], _ :: _, h, _, _ => h.elim
  | _, _, _, _ :: _, [], h, _, _ => h.elim

end

/-- **What the relabelling chooses**, exported: a chain witness `sv` of `RelW`'s `CallsOK` (its
messages live, every live space-4/`≥ 16` message a chain message or a dead local), a depth map `σ`
on it, and the kept ids `A = chainIds E.cid sv`. -/
def RelabelOK (X : Ctx) (E : Env) (t : Nat) (σ : Nat → Nat) (A : List Nat) : Prop :=
  ∃ sv, Chain X t E.cid E.sb E.k E.rest sv ∧ (∀ x, chainMsgs X E.cid E.k E.rest sv x → E.live x) ∧
    (∀ x, E.live x → (x.space = 4 ∨ 16 ≤ x.space) → chainMsgs X E.cid E.k E.rest sv x ∨ deadSp t E.cid sv x) ∧
    DepthOK σ E.cid sv ∧ A = chainIds E.cid sv

/-- **The id facts the CUTO link uses**, for the final live list `fin`, the kept ids `I` (current
frame first) and the depth map `σ`. -/
structure IdsOK (fin : List Msg) (I : List Nat) (σ : Nat → Nat) : Prop where
  desc : I.Pairwise (· > ·)
  zero : 0 ∈ I
  lt : ∀ y ∈ I, y < 2 ^ 28
  dep : ∀ i (hi : i < I.length), σ I[i] = I.length - 1 - i
  recs : ∀ x ∈ fin, x.space = 4 → ∃ i, ∃ hi : i + 1 < I.length, x.slot = I[i] ∧ x.l2 = I[i + 1]
  recEx : ∀ i (hi : i + 1 < I.length), ∃ x ∈ fin, x.space = 4 ∧ x.slot = I[i]

/-- **`IdsOK` at a related state**, for the relabelling data `RelabelOK`. -/
theorem idsOK_of_relW {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {fin : List Msg} {a b : Nat} {σ : Nat → Nat} {A : List Nat}
    (R : RelW X E s f tps tpl t pc S (· ∈ fin) a b) (hok : RelabelOK X E t σ A) : IdsOK fin A σ := by
  obtain ⟨sv, hc, hin, hout, hd, rfl⟩ := hok
  refine ⟨hc.ids_desc, hc.zero_mem, fun y hy => ?_, fun i hi => ?_, fun x hx h4 => ?_, fun i hi => ?_⟩
  · have := hc.ids_le y hy; have := R.cidLt; omega
  · rw [DepthOK.at hd i hi]; simp
  · rcases (R.live x).mp hx with h | h | h
    · obtain ⟨i, -, rfl⟩ := mem_stackView.mp h; simp [enc] at h4
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc, Env.lsp] at h4; omega
    · rcases hout x h (Or.inl h4) with h' | ⟨d1, -⟩
      · exact chainMsgs_rec h' h4
      · omega
  · obtain ⟨x, hx, h4, hs⟩ := chainMsgs_rec_exists hc i hi
    exact ⟨x, (R.live x).mpr (Or.inr (Or.inr (hin x hx))), h4, hs⟩

/-- `RelW.relabel_view`, also exporting the relabelling data `RelabelOK`. -/
theorem RelW.relabel_viewL {X : Ctx} (hnd : X.M.fns.Nodup) {E : Env} {s : St} {f : Frame}
    {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    (R : RelW X E s f tps tpl t pc S live a b) (hreg : RegC live s) (hsp : SpC live) :
    ∃ (σ : Nat → Nat) (A : List Nat), RelabelOK X E t σ A ∧
      RelW X ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩ s f tps tpl t pc S
        (relabelLive σ A live) a b ∧
      RegC (relabelLive σ A live) s ∧ SpC (relabelLive σ A live) ∧
      ∀ y, (∃ x, relabelLive σ A live x ∧ x.space ≠ 3 ∧ x.space ≠ 7 ∧ fieldsOf x = y) ↔ y ∈ cutView X s := by
  obtain ⟨σ, A, sv, -, R', hc, hout, hin, hok⟩ := R.relabelV
  refine ⟨σ, A, hok, R', hreg.relabel, hsp.relabel, ?_⟩
  exact view_eq_of_depth hnd R' rfl hc (idsDepth_svR sv) hin hout hreg.relabel hsp.relabel

/-- **`cutView_eq` with the relabelling data**: as `cutView_eq`, and the chosen `(σ, A)` are those of
a `RelW` of the boundary (`RelabelOK`), so `IdsOK` holds for the live list (`idsOK_of_relW`). -/
theorem cutView_eqL {X : Ctx} (hnd : X.M.fns.Nodup) {sg : Nat → Nat × Nat} {s : St} {t S : Nat}
    {m : List F} {L : List Msg} (h : BndC X sg s t S m L) :
    ∃ (σ : Nat → Nat) (A : List Nat), IdsOK L A σ ∧
      BndC X sg s t S (m.set 5 ((s.frames.length - 1 : Nat) : F))
        ((L.filter (fun x => decide (keepA A x))).map (rlMsg σ)) ∧
      ∀ y, (∃ x ∈ (L.filter (fun x => decide (keepA A x))).map (rlMsg σ),
        x.space ≠ 3 ∧ x.space ≠ 7 ∧ fieldsOf x = y) ↔ y ∈ cutView X s := by
  obtain ⟨⟨k, pc, sb, cid, rfl, E, f, tps, tpl, rfl, rfl, rfl, R⟩, hreg, hsp⟩ := h
  obtain ⟨σ, A, hok, R', hreg', hsp', hv⟩ := R.relabel_viewL hnd hreg hsp
  have hfr : s.frames.length - 1 = E.rest.length := by rw [R.frames]; simp
  have e : (fun y => y ∈ (L.filter (fun x => decide (keepA A x))).map (rlMsg σ)) = relabelLive σ A (· ∈ L) :=
    funext fun y => propext mem_relabelList
  refine ⟨σ, A, idsOK_of_relW R hok, ⟨⟨E.k, pc, E.sb, E.rest.length, ?_,
    ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩, f, tps, tpl, rfl, rfl, rfl, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hfr]; rfl
  · rw [e]; exact R'
  · rw [e]; exact hreg'
  · rw [e]; exact hsp'
  · intro y
    rw [← hv y]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, mem_relabelList.mp hx, h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, mem_relabelList.mpr hx, h⟩

#print axioms Chain.ids_desc
#print axioms DepthOK.at
#print axioms chainMsgs_rec
#print axioms chainMsgs_rec_exists
#print axioms idsOK_of_relW
#print axioms cutView_eqL

end WasmBase
