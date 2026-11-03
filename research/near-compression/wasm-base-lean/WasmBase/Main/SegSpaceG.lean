import WasmBase.Main.SegLinkSpec
import WasmBase.Main.SegGrowStep
/-!
# WasmBase.Main.SegSpaceG — the boundary space clause with the live size message (E2E M6, GROW2)

The space clause `SpC` (`Main/SegView.lean`: every live message in space 0, 2–7 or `≥ 16`) excludes
space 8, but on `wasmBaseSegAirG` the memory-size message `szMsg pages tz` (space 8, SEGG's
production at the in-cut and consumption at the out-cut, `Main/SegGrowStep.lean`) is live across the
whole segment.  Here the variant that admits it:

* `SpaceOKG x := SpaceOK x ∨ x.space = 8`, `SpCG`, `BndCG := Bnd ∧ RegC ∧ SpCG`, with the inclusions
  `SpC.toG`, `BndC.toG`, relabelling (`SpCG.relabel`, space 8 is fixed by `rlMsg`), and the row
  lemma `rowQ_spaceG` (`rowQ_space` for `SpCG`);
* **the view theorem with the size message**: `view_eq_of_depthG`, `RelW.relabel_viewLG`,
  **`cutView_eqLG`** — as `view_eq_of_depth` / `RelW.relabel_viewL` / `cutView_eqL`, with
  `SpCG` in place of `SpC` and the part of the live set outside spaces 3, 7 **and 8** equal (up to
  producer times) to `cutView X s`.  The size message is not in `cutView`: across the cut it is
  carried by SEGG and the public block counts (`segg_size_track`, `Main/SegExecQ.lean`).
* `spCG_of_off8`: `SpaceOK` off space 8 gives `SpCG`.
-/
namespace WasmBase

open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-- An allowed space, or the memory-size space 8. -/
def SpaceOKG (x : Msg) : Prop := SpaceOK x ∨ x.space = 8

/-- **Space clause with the size message**: every live message in an allowed space or space 8. -/
def SpCG (live : Msg → Prop) : Prop := ∀ x, live x → SpaceOKG x

/-- **The boundary relation of a grow segment**: `Bnd` plus the register clause and `SpCG`. -/
def BndCG (X : Ctx) (sg : Nat → Nat × Nat) (s : St) (t S : Nat) (m : List F) (L : List Msg) : Prop :=
  Bnd X sg s t S m L ∧ RegC (· ∈ L) s ∧ SpCG (· ∈ L)

theorem SpaceOK.toG {x : Msg} (h : SpaceOK x) : SpaceOKG x := Or.inl h
theorem SpC.toG {live : Msg → Prop} (h : SpC live) : SpCG live := fun x hx => (h x hx).toG
theorem BndC.toG {X : Ctx} {sg : Nat → Nat × Nat} {s : St} {t S : Nat} {m : List F} {L : List Msg}
    (h : BndC X sg s t S m L) : BndCG X sg s t S m L := ⟨h.1, h.2.1, h.2.2.toG⟩

/-- Away from space 8, `SpaceOKG` is `SpaceOK`. -/
theorem SpaceOKG.ok {x : Msg} (h : SpaceOKG x) (h8 : x.space ≠ 8) : SpaceOK x := h.resolve_right h8

theorem SpaceOKG.rlMsg {σ : Nat → Nat} {x : Msg} (h : SpaceOKG x) : SpaceOKG (rlMsg σ x) := by
  rcases h with h | h
  · exact Or.inl h.rlMsg
  · right
    have hs := rlMsg_space σ x
    rw [if_neg (by omega), if_neg (by omega)] at hs
    rw [hs, h]

theorem SpCG.relabel {σ : Nat → Nat} {A : List Nat} {live : Msg → Prop} (h : SpCG live) :
    SpCG (relabelLive σ A live) := by
  rintro y ⟨x, hx, -, rfl⟩
  exact (h x hx).rlMsg

/-- **The space clause off space 8 gives `SpCG`.** -/
theorem spCG_of_off8 {live : Msg → Prop} (hsp : ∀ x, live x → x.space ≠ 8 → SpaceOK x) : SpCG live :=
  fun x hx => by
    by_cases h8 : x.space = 8
    · exact Or.inr h8
    · exact Or.inl (hsp x hx h8)

/-- **`rowQ_space` for `SpCG`**: a row whose produced messages are in allowed spaces or space 8
keeps `SpCG`. -/
theorem rowQ_spaceG {X : Ctx} {inS : List F} {cons prod : List Msg}
    (h : ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat),
      RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
      ∀ x ∈ prod, SpaceOKG x) :
    RowQ X (fun _ live => SpCG live) inS cons prod := by
  intro E s f tps tpl t pc S live a b s' R hin _ _ hQ x hx
  rcases hx with ⟨hx, -⟩ | hx
  · exact hQ x hx
  · exact h E s f tps tpl t pc S live a b R hin x hx

/-- **A row that keeps `SpC` by `rowQ_space`'s argument keeps `SpCG`.** -/
theorem rowQ_spaceG_of {X : Ctx} {inS : List F} {cons prod : List Msg}
    (h : ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat),
      RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
      ∀ x ∈ prod, SpaceOK x) :
    RowQ X (fun _ live => SpCG live) inS cons prod :=
  rowQ_spaceG fun E s f tps tpl t pc S live a b R hin x hx => (h E s f tps tpl t pc S live a b R hin x hx).toG

/-- **The view theorem with the size message** (`view_eq_of_depth` with `SpCG`): the live messages
outside memory (3), the gas register (7) and the size message (8) have, up to producer times,
exactly the fields of `cutView X s`. -/
theorem view_eq_of_depthG {X : Ctx} (hnd : X.M.fns.Nodup) {E : Env} {s : St} {f : Frame}
    {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat} {sv : List Saved}
    (R : RelW X E s f tps tpl t pc S live a b) (hD : E.cid = E.rest.length)
    (hc : Chain X t E.cid E.sb E.k E.rest sv) (hids : IdsDepth sv)
    (hin : ∀ y, chainMsgs X E.cid E.k E.rest sv y → E.live y)
    (hout : ∀ y, E.live y → (y.space = 4 ∨ 16 ≤ y.space) → chainMsgs X E.cid E.k E.rest sv y)
    (hreg : RegC live s) (hsp : SpCG live) :
    ∀ y, (∃ x, live x ∧ x.space ≠ 3 ∧ x.space ≠ 7 ∧ x.space ≠ 8 ∧ fieldsOf x = y) ↔ y ∈ cutView X s := by
  obtain ⟨tpr, hr⟩ := hreg
  obtain ⟨tpg, -, hg⟩ := R.heap.glob
  obtain ⟨tpb, -, hb⟩ := R.calls.budget
  have CI := chain_img (t := t) hnd hc hids hD s.frames.reverse f R.fn (fun d _ => by rw [R.frames]; simp)
  intro y
  rw [mem_cutView]
  simp only [cutMsgs, List.mem_append, List.mem_singleton, mem_cutMsgs_frames R.frames]
  constructor
  · rintro ⟨x, hx, h3, h7, h8, rfl⟩
    rcases (R.live x).mp hx with h | h | h
    · obtain ⟨x', hx', e⟩ := img_stackView (tps' := fun _ => 0) ⟨x, h, rfl⟩
      exact ⟨x', Or.inl (Or.inl (Or.inl (Or.inl hx'))), e⟩
    · simp only [Env.lsp, hD] at h
      obtain ⟨x', hx', e⟩ := img_localView (tpl' := fun _ => 0) ⟨x, h, rfl⟩
      exact ⟨x', Or.inl (Or.inl (Or.inl (Or.inr (Or.inr hx')))), e⟩
    · have sep := R.envSep x h
      have chainCase : x.space = 4 ∨ 16 ≤ x.space →
          ∃ x' ∈ chainView X s.frames.reverse E.rest.length, fieldsOf x' = fieldsOf x := by
        intro hs
        obtain ⟨x', hx', e⟩ := (CI (fieldsOf x)).mp ⟨x, hout x h hs, rfl⟩
        exact ⟨x', hx', e⟩
      rcases (hsp x hx).ok h8 with s0 | s2 | s3 | s4 | s5 | s6 | s7 | s16
      · exact absurd s0 sep.1
      · obtain ⟨x', hx', e⟩ := img_globView (tpg' := fun _ => 0) ⟨x, (hg x s2).mp h, rfl⟩
        exact ⟨x', Or.inl (Or.inl (Or.inr hx')), e⟩
      · exact absurd s3 h3
      · obtain ⟨x', hx', e⟩ := chainCase (Or.inl s4)
        exact ⟨x', Or.inl (Or.inl (Or.inl (Or.inr (Or.inl hx')))), e⟩
      · rw [(hb x s5).mp h]
        exact ⟨_, Or.inl (Or.inr rfl), rfl⟩
      · obtain ⟨x', hx', e⟩ := img_regView (tpr' := fun _ => 0) ⟨x, (hr x s6).mp hx, rfl⟩
        exact ⟨x', Or.inr hx', e⟩
      · exact absurd s7 h7
      · obtain ⟨x', hx', e⟩ := chainCase (Or.inr s16)
        exact ⟨x', Or.inl (Or.inl (Or.inl (Or.inr (Or.inl hx')))), e⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ((((h | h | h) | h) | h) | h)
    · obtain ⟨x', hx', e⟩ := img_stackView (tps' := tps) ⟨x, h, rfl⟩
      obtain ⟨i, -, rfl⟩ := mem_stackView.mp hx'
      exact ⟨_, (R.live _).mpr (Or.inl hx'), by simp, by simp, by simp, e⟩
    · obtain ⟨x', hx', e⟩ := (CI (fieldsOf x)).mpr ⟨x, h, rfl⟩
      have hs := chainMsgs_space_ids hx'
      refine ⟨x', (R.live x').mpr (Or.inr (Or.inr (hin x' hx'))), ?_, ?_, ?_, e⟩ <;> omega
    · obtain ⟨x', hx', e⟩ := img_localView (tpl' := tpl) ⟨x, h, rfl⟩
      obtain ⟨j, -, rfl⟩ := mem_localView.mp hx'
      refine ⟨_, (R.live _).mpr (Or.inr (Or.inl ?_)), by simp; omega, by simp; omega, by simp; omega, e⟩
      simpa only [Env.lsp, hD] using hx'
    · obtain ⟨x', hx', e⟩ := img_globView (tpg' := tpg) ⟨x, h, rfl⟩
      obtain ⟨g, -, rfl⟩ := mem_globView.mp hx'
      exact ⟨_, (R.live _).mpr (Or.inr (Or.inr ((hg _ rfl).mpr hx'))), by simp, by simp, by simp, e⟩
    · subst h
      exact ⟨budMsg s.stackRem tpb, (R.live _).mpr (Or.inr (Or.inr ((hb _ rfl).mpr rfl))),
        by simp [budMsg], by simp [budMsg], by simp [budMsg], rfl⟩
    · obtain ⟨x', hx', e⟩ := img_regView (tpr' := tpr) ⟨x, h, rfl⟩
      have h6 : x'.space = 6 := by
        obtain ⟨rid, d, -, hx''⟩ := Register.mem_view.mp hx'
        rcases Register.mem_regMsgs.mp hx'' with rfl | ⟨i, -, rfl⟩ <;> rfl
      exact ⟨x', (hr x' h6).mpr hx', by omega, by omega, by omega, e⟩

/-- `RelW.relabel_viewL` with `SpCG`. -/
theorem RelW.relabel_viewLG {X : Ctx} (hnd : X.M.fns.Nodup) {E : Env} {s : St} {f : Frame}
    {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    (R : RelW X E s f tps tpl t pc S live a b) (hreg : RegC live s) (hsp : SpCG live) :
    ∃ (σ : Nat → Nat) (A : List Nat), RelabelOK X E t σ A ∧
      RelW X ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩ s f tps tpl t pc S
        (relabelLive σ A live) a b ∧
      RegC (relabelLive σ A live) s ∧ SpCG (relabelLive σ A live) ∧
      ∀ y, (∃ x, relabelLive σ A live x ∧ x.space ≠ 3 ∧ x.space ≠ 7 ∧ x.space ≠ 8 ∧ fieldsOf x = y) ↔
        y ∈ cutView X s := by
  obtain ⟨σ, A, sv, -, R', hc, hout, hin, hok⟩ := R.relabelV
  refine ⟨σ, A, hok, R', hreg.relabel, hsp.relabel, ?_⟩
  exact view_eq_of_depthG hnd R' rfl hc (idsDepth_svR sv) hin hout hreg.relabel hsp.relabel

/-- **`cutView_eqL` for a grow boundary** (`BndCG`): the relabelled live list satisfies `BndCG`
again, and its part outside spaces 3, 7 and 8 has, up to producer times, exactly the members of
`cutView X s`. -/
theorem cutView_eqLG {X : Ctx} (hnd : X.M.fns.Nodup) {sg : Nat → Nat × Nat} {s : St} {t S : Nat}
    {m : List F} {L : List Msg} (h : BndCG X sg s t S m L) :
    ∃ (σ : Nat → Nat) (A : List Nat), IdsOK L A σ ∧
      BndCG X sg s t S (m.set 5 ((s.frames.length - 1 : Nat) : F))
        ((L.filter (fun x => decide (keepA A x))).map (rlMsg σ)) ∧
      ∀ y, (∃ x ∈ (L.filter (fun x => decide (keepA A x))).map (rlMsg σ),
        x.space ≠ 3 ∧ x.space ≠ 7 ∧ x.space ≠ 8 ∧ fieldsOf x = y) ↔ y ∈ cutView X s := by
  obtain ⟨⟨k, pc, sb, cid, rfl, E, f, tps, tpl, rfl, rfl, rfl, R⟩, hreg, hsp⟩ := h
  obtain ⟨σ, A, hok, R', hreg', hsp', hv⟩ := R.relabel_viewLG hnd hreg hsp
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

#print axioms SpCG.relabel
#print axioms spCG_of_off8
#print axioms rowQ_spaceG
#print axioms rowQ_spaceG_of
#print axioms view_eq_of_depthG
#print axioms RelW.relabel_viewLG
#print axioms cutView_eqLG

end WasmBase
