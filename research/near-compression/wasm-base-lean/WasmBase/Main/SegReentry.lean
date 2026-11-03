import WasmBase.Main.SegCuti

/-!
# WasmBase.Main.SegReentry — re-entering a segment at the previous segment's out-cut (E2E M4c, CUTI)

`seg_sound` (`Main/SegSoundX.lean`) assumes the in-boundary relation
`h0 : BndC X sg s0 t_in S_in (segM0 tr pub) (initS tr pub)`.  Here it is **derived** for the next
segment of a chain from the previous segment's out-boundary relation (any `BndC X sg s t S m L`, as
`seg_sound` concludes), when the next trace's CUTI part is the view of `s` at `t_in = t` (`cuti_view`),
MEMB's in-side productions are the bytes of `s` (`MembIn`, the memory interface of sub-lane MEM) and
the public STATE fields match.

* **`RelW.ofView`** (the new construction): a `RelW` at a depth-labelled state (`cid = rest.length`,
  caller ids = depths, as `RelW.relabelV` produces) yields a `RelW` at the **same state** for a
  **different live set** `L` — the view `cutView X s` at one producer time `tp`, memory = the bytes of a
  touched set `T` at `tp`, anything in space 7 — with fresh producer times (all `tp`): the operand
  stack, locals, globals, budget, registers and caller chain are re-read from the view (`mem_viewAt`:
  the view at `tp`, split by part; `chain_img` for the caller chain), the memory part from `T`.
* **`bnd_reentry`** / **`bndC_reentry`**: the next segment's `h0` (the register and space clauses by
  `bndC_of_view`).
* **`seg_cid_out`**: the public `cid_out` is the depth `frames.length − 1` of the out-state (SEGB's
  CIDMAP query `[cidf, cid_out]` is answered by SEGB's `0 ↦ 0` — the entry frame — or by the CUTO
  record row of the current activation, whose `dep` is `σ cidf = depth`, `cuto_k4_dep`).  This is what
  makes the next segment's `cid_in` the depth its CUTI view uses.
-/

namespace WasmBase
namespace Cuti

open ZkFormal.Algebra Chips Seg
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## 1. Retimed caller chains -/

/-- The saved callers with every producer time set to `tp`. -/
def svT (tp : Nat) : List Saved → List Saved
  | [] => []
  | c :: sv => { c with tpl := fun _ => tp, tpc := tp } :: svT tp sv

@[simp] theorem svT_length (tp : Nat) : ∀ sv : List Saved, (svT tp sv).length = sv.length
  | [] => rfl
  | _ :: sv => by simp [svT, svT_length tp sv]

theorem chain_retime {X : Ctx} {t tp : Nat} (htp : tp < t) : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved},
    Chain X t cid sb k rest sv → Chain X t cid sb k rest (svT tp sv)
  | _, _, _, [], [], h => h
  | _, _, _, _ :: _, _ :: _, h => by
    obtain ⟨a1, a2, a3, a4, a5, -, a7, a8, a9, a10, a11, a12, a13⟩ := h
    exact ⟨a1, a2, a3, a4, a5, htp, a7, a8, a9, a10, fun j hj => ⟨(a11 j hj).1, htp⟩, a12, chain_retime htp a13⟩
  | _, _, _, [], _ :: _, h => h.elim
  | _, _, _, _ :: _, [], h => h.elim

theorem idsDepth_svT (tp : Nat) : ∀ sv : List Saved, IdsDepth sv → IdsDepth (svT tp sv)
  | [], _ => trivial
  | _ :: sv, h => ⟨by simpa [svT] using h.1, idsDepth_svT tp sv h.2⟩

theorem chainCharge_svT (X : Ctx) (tp : Nat) : ∀ (k : Nat) (sv : List Saved),
    chainCharge X k (svT tp sv) = chainCharge X k sv
  | _, [] => rfl
  | k, c :: sv => by simp only [svT, chainCharge]; rw [chainCharge_svT X tp c.k sv]

theorem chainMsgs_svT_tp {X : Ctx} {tp : Nat} : ∀ {cid k : Nat} {rest : List Frame} {sv : List Saved} {x : Msg},
    chainMsgs X cid k rest (svT tp sv) x → x.tp = tp
  | _, _, [], [], _, h => h.elim
  | _, _, _ :: _, c :: sv, x, h => by
    rcases h with rfl | h | h
    · rfl
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; rfl
    · exact chainMsgs_svT_tp h
  | _, _, [], _ :: _, _, h => h.elim
  | _, _, _ :: _, [], _, h => h.elim

/-! ## 2. The view at one producer time, split by part -/

/-- The view of `s` as messages produced at `tp`. -/
def viewAt (X : Ctx) (s : St) (tp : Nat) (x : Msg) : Prop := ∃ y ∈ cutView X s, x = ofFields y tp

theorem msg_eq_of_fields {a b : Msg} (h : fieldsOf a = fieldsOf b) (ht : a.tp = b.tp) : a = b := by
  cases a; cases b
  simp only [fieldsOf, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only at ht
  subst h1 h2 h3 h4 h5 h6 h7 ht; rfl

theorem viewAt_iff (X : Ctx) (s : St) (tp : Nat) (x : Msg) :
    viewAt X s tp x ↔ ∃ x' ∈ cutMsgs X s, x = { x' with tp := tp } := by
  unfold viewAt
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x', hx', rfl⟩ := mem_cutView.mp hy
    exact ⟨x', hx', ofFields_fieldsOf x' tp⟩
  · rintro ⟨x', hx', rfl⟩
    exact ⟨fieldsOf x', mem_cutView.mpr ⟨x', hx', rfl⟩, (ofFields_fieldsOf x' tp).symm⟩

/-- Retiming a view family whose members carry the given time. -/
theorem retime_iff {P : Nat → List Msg} (hP : ∀ c x, x ∈ P c → x.tp = c)
    (hR : ∀ c c' x, x ∈ P c → { x with tp := c' } ∈ P c') (tp : Nat) (x : Msg) :
    (∃ x' ∈ P 0, x = { x' with tp := tp }) ↔ x ∈ P tp := by
  constructor
  · rintro ⟨x', hx', rfl⟩; exact hR 0 tp x' hx'
  · intro hx
    refine ⟨{ x with tp := 0 }, hR tp 0 x hx, ?_⟩
    have := hP tp x hx
    cases x; simp only at this ⊢; rw [this]

theorem stack_retime (stk : Array Val) : ∀ c c' x, x ∈ stackView stk (fun _ => c) →
    { x with tp := c' } ∈ stackView stk (fun _ => c') := by
  intro c c' x hx; obtain ⟨i, hi, rfl⟩ := mem_stackView.mp hx; exact mem_stackView.mpr ⟨i, hi, rfl⟩

theorem stack_tp (stk : Array Val) : ∀ c x, x ∈ stackView stk (fun _ => c) → x.tp = c := by
  intro c x hx; obtain ⟨i, -, rfl⟩ := mem_stackView.mp hx; rfl

theorem local_retime (sp : Nat) (locs : Array Val) : ∀ c c' x, x ∈ localView sp locs (fun _ => c) →
    { x with tp := c' } ∈ localView sp locs (fun _ => c') := by
  intro c c' x hx; obtain ⟨i, hi, rfl⟩ := mem_localView.mp hx; exact mem_localView.mpr ⟨i, hi, rfl⟩

theorem local_tp (sp : Nat) (locs : Array Val) : ∀ c x, x ∈ localView sp locs (fun _ => c) → x.tp = c := by
  intro c x hx; obtain ⟨i, -, rfl⟩ := mem_localView.mp hx; rfl

theorem glob_retime (gs : Array Val) : ∀ c c' x, x ∈ globView gs (fun _ => c) →
    { x with tp := c' } ∈ globView gs (fun _ => c') := by
  intro c c' x hx; obtain ⟨i, hi, rfl⟩ := mem_globView.mp hx; exact mem_globView.mpr ⟨i, hi, rfl⟩

theorem glob_tp (gs : Array Val) : ∀ c x, x ∈ globView gs (fun _ => c) → x.tp = c := by
  intro c x hx; obtain ⟨i, -, rfl⟩ := mem_globView.mp hx; rfl

theorem reg_retime (regs : Array (Nat × ByteArray)) : ∀ c c' x, x ∈ Register.view regs (fun _ => c) →
    { x with tp := c' } ∈ Register.view regs (fun _ => c') := fun _ c' _ hx => regView_retime c' hx

theorem reg_tp (regs : Array (Nat × ByteArray)) : ∀ c x, x ∈ Register.view regs (fun _ => c) → x.tp = c :=
  fun _ _ hx => regView_tp hx

theorem bud_retime (rem : Nat) : ∀ c c' x, x ∈ [budMsg rem c] → { x with tp := c' } ∈ [budMsg rem c'] := by
  intro c c' x hx; rw [List.mem_singleton] at hx ⊢; subst hx; rfl

theorem bud_tp (rem : Nat) : ∀ c x, x ∈ [budMsg rem c] → x.tp = c := by
  intro c x hx; rw [List.mem_singleton] at hx; subst hx; rfl

/-- **The view at `tp`, part by part**, at a depth-labelled related state: operand stack, caller chain
(retimed), current locals (space `16 + depth`), globals, budget, registers — all at `tp`. -/
theorem mem_viewAt {X : Ctx} (hnd : X.M.fns.Nodup) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat}
    {t pc S : Nat} {live : Msg → Prop} {a b : Nat} {sv : List Saved}
    (R : RelW X E s f tps tpl t pc S live a b) (hD : E.cid = E.rest.length)
    (hc : Chain X t E.cid E.sb E.k E.rest sv) (hids : IdsDepth sv) {tp : Nat} (htp : tp < t) (x : Msg) :
    viewAt X s tp x ↔ x ∈ stackView s.stack (fun _ => tp) ∨ chainMsgs X E.cid E.k E.rest (svT tp sv) x ∨
      x ∈ localView (16 + E.cid) f.locals (fun _ => tp) ∨ x ∈ globView s.globals (fun _ => tp) ∨
      x = budMsg s.stackRem tp ∨ x ∈ Register.view s.registers (fun _ => tp) := by
  have CI := chain_img (t := t) hnd (chain_retime htp hc) (idsDepth_svT tp sv hids) hD s.frames.reverse f R.fn
    (fun d _ => by rw [R.frames]; simp)
  have rS := retime_iff (stack_tp s.stack) (stack_retime s.stack) tp x
  have rL := retime_iff (local_tp (16 + E.cid) f.locals) (local_retime (16 + E.cid) f.locals) tp x
  have rG := retime_iff (glob_tp s.globals) (glob_retime s.globals) tp x
  have rR := retime_iff (reg_tp s.registers) (reg_retime s.registers) tp x
  have rB := retime_iff (bud_tp s.stackRem) (bud_retime s.stackRem) tp x
  rw [List.mem_singleton] at rB
  rw [viewAt_iff]
  constructor
  · rintro ⟨x', hx', rfl⟩
    simp only [cutMsgs, List.mem_append, List.mem_singleton, mem_cutMsgs_frames R.frames] at hx'
    rcases hx' with (((h | h | h) | h) | h) | h
    · exact Or.inl (rS.mp ⟨x', h, rfl⟩)
    · right; left
      obtain ⟨x'', hx'', e⟩ := (CI (fieldsOf x')).mpr ⟨x', h, rfl⟩
      rw [msg_eq_of_fields (a := x'') (b := { x' with tp := tp }) e (chainMsgs_svT_tp hx'')] at hx''
      exact hx''
    · right; right; left; rw [← hD] at h; exact rL.mp ⟨x', h, rfl⟩
    · right; right; right; left; exact rG.mp ⟨x', h, rfl⟩
    · right; right; right; right; left; exact rB.mp ⟨x', List.mem_singleton.mpr h, rfl⟩
    · right; right; right; right; right; exact rR.mp ⟨x', h, rfl⟩
  · intro h
    have mk : ∀ {x' : Msg}, x' ∈ cutMsgs X s → x = { x' with tp := tp } → ∃ x' ∈ cutMsgs X s, x = { x' with tp := tp } :=
      fun h1 h2 => ⟨_, h1, h2⟩
    have FR := fun {y : Msg} => (mem_cutMsgs_frames (X := X) R.frames (x := y))
    have inF : ∀ {y : Msg}, y ∈ (List.range s.frames.length).flatMap (frameMsgs X s.frames.reverse) → y ∈ cutMsgs X s :=
      fun h => by unfold cutMsgs; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ h)))
    rcases h with h | h | h | h | h | h
    · obtain ⟨x', hx', e⟩ := rS.mpr h
      exact mk (by unfold cutMsgs; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ hx')))) e
    · obtain ⟨x', hx', e⟩ := (CI (fieldsOf x)).mp ⟨x, h, rfl⟩
      exact mk (x' := x') (inF (FR.mpr (Or.inl hx'))) (msg_eq_of_fields e.symm (chainMsgs_svT_tp h))
    · obtain ⟨x', hx', e⟩ := rL.mpr h
      rw [hD] at hx'
      exact mk (x' := x') (inF (FR.mpr (Or.inr hx'))) e
    · obtain ⟨x', hx', e⟩ := rG.mpr h
      exact mk (by unfold cutMsgs; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx'))) e
    · obtain ⟨x', hx', e⟩ := rB.mpr h
      exact mk (by unfold cutMsgs; exact List.mem_append_left _ (List.mem_append_right _ hx')) e
    · obtain ⟨x', hx', e⟩ := rR.mpr h
      exact mk (by unfold cutMsgs; exact List.mem_append_right _ hx') e

/-! ## 3. A relation at the same state, re-read from the view -/

theorem stackView_space {stk : Array Val} {tps : Nat → Nat} {x : Msg} (h : x ∈ stackView stk tps) : x.space = 0 := by
  obtain ⟨i, -, rfl⟩ := mem_stackView.mp h; rfl

theorem localView_space {sp : Nat} {locs : Array Val} {tpl : Nat → Nat} {x : Msg} (h : x ∈ localView sp locs tpl) :
    x.space = sp := by
  obtain ⟨i, -, rfl⟩ := mem_localView.mp h; rfl

theorem globView_space {gs : Array Val} {tpg : Nat → Nat} {x : Msg} (h : x ∈ globView gs tpg) : x.space = 2 := by
  obtain ⟨i, -, rfl⟩ := mem_globView.mp h; rfl

theorem regView_space {regs : Array (Nat × ByteArray)} {tpr : Nat → Nat} {x : Msg} (h : x ∈ Register.view regs tpr) :
    x.space = 6 := by
  obtain ⟨rid, d, -, hx⟩ := Register.mem_view.mp h
  rcases Register.mem_regMsgs.mp hx with rfl | ⟨i, -, rfl⟩ <;> rfl

/-- Two chains under the same frames have the same checked-function indices (`fns.Nodup`). -/
theorem chain_ks {X : Ctx} (hnd : X.M.fns.Nodup) : ∀ {t t' cid cid' sb sb' k : Nat} {rest : List Frame}
    {sv sv' : List Saved}, Chain X t cid sb k rest sv → Chain X t' cid' sb' k rest sv' →
    sv.map Saved.k = sv'.map Saved.k
  | _, _, _, _, _, _, _, [], [], [], _, _ => rfl
  | _, _, _, _, _, _, _, fc :: rest, c :: sv, c' :: sv', h, h' => by
    obtain ⟨a1, a2, -, -, -, -, -, -, -, -, -, -, a13⟩ := h
    obtain ⟨b1, b2, -, -, -, -, -, -, -, -, -, -, b13⟩ := h'
    have e : c.k = c'.k := by
      rw [← kOf_fnOf hnd a1, ← kOf_fnOf hnd b1, ← a2, ← b2]
    simp only [List.map_cons, e]
    rw [← e] at b13
    rw [chain_ks hnd a13 b13]
  | _, _, _, _, _, _, _, [], _ :: _, _, h, _ => h.elim
  | _, _, _, _, _, _, _, _ :: _, [], _, h, _ => h.elim
  | _, _, _, _, _, _, _, [], [], _ :: _, _, h' => h'.elim
  | _, _, _, _, _, _, _, _ :: _, _ :: _, [], _, h' => h'.elim

theorem chainCharge_congr (X : Ctx) : ∀ (k : Nat) (sv sv' : List Saved), sv.map Saved.k = sv'.map Saved.k →
    chainCharge X k sv = chainCharge X k sv'
  | _, [], [], _ => rfl
  | k, c :: sv, c' :: sv', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [chainCharge, h.1, chainCharge_congr X c'.k sv sv' h.2]
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-- **A related state, re-read from its view.**  At a depth-labelled related state (`cid = rest.length`,
a caller chain with depth ids), any live set `L` whose part outside memory and the gas register is
exactly the view `cutView X s` at one producer time `tp < t`, and whose memory part is the bytes of `s`
at a duplicate-free in-bounds touched set `T` (at `tp`), is related again: same frame data, all
producer times `tp`, outer live set `L` minus the operand stack and the current locals. -/
theorem RelW.ofView {X : Ctx} (hnd : X.M.fns.Nodup) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat}
    {t pc S : Nat} {live : Msg → Prop} {a b : Nat} {sv : List Saved}
    (R : RelW X E s f tps tpl t pc S live a b) (hD : E.cid = E.rest.length)
    (hc : Chain X t E.cid E.sb E.k E.rest sv) (hids : IdsDepth sv) {tp : Nat} (htp : tp < t)
    {L : Msg → Prop} (hV : ∀ x, x.space ≠ 3 → x.space ≠ 7 → (L x ↔ viewAt X s tp x))
    {T : List Nat} (hT : T.Nodup) (hTb : ∀ a ∈ T, a < memBytes s)
    (hM : ∀ x, x.space = 3 → (L x ↔ x ∈ memView T s (fun _ => tp))) :
    RelW X ⟨E.sb, E.cid, E.rest, fun x => L x ∧ x.space ≠ 0 ∧ x.space ≠ 16 + E.cid, E.k⟩ s f
      (fun _ => tp) (fun _ => tp) t pc S L a b := by
  have MV := mem_viewAt hnd R hD hc hids htp
  have hc' := chain_retime htp hc
  have spc : ∀ x, chainMsgs X E.cid E.k E.rest (svT tp sv) x → x.space = 4 ∨ (16 ≤ x.space ∧ x.space ≠ 16 + E.cid) := by
    intro x hx
    rcases chainMsgs_space_ids hx with h | ⟨h1, h2⟩
    · exact Or.inl h
    · right; refine ⟨h1, fun e => ?_⟩
      obtain ⟨c, hc'', hcc⟩ := List.mem_map.mp h2
      have := hc'.ids_lt c hc''
      omega
  obtain ⟨tpg, hg, -⟩ := R.heap.glob
  obtain ⟨sv1, hc1, -, -, hrl⟩ := R.calls.chain
  -- the view part of `L`, by space
  have L0 : ∀ x, x.space = 0 → (L x ↔ x ∈ stackView s.stack (fun _ => tp)) := by
    intro x h0
    rw [hV x (by omega) (by omega), MV]
    constructor
    · rintro (h | h | h | h | h | h)
      · exact h
      · rcases spc x h with h' | ⟨h', -⟩ <;> omega
      · have := localView_space h; omega
      · have := globView_space h; omega
      · subst h; have : (budMsg s.stackRem tp).space = 5 := rfl; omega
      · have := regView_space h; omega
    · exact Or.inl
  have LL : ∀ x, x.space = 16 + E.cid → (L x ↔ x ∈ localView (16 + E.cid) f.locals (fun _ => tp)) := by
    intro x hl
    rw [hV x (by omega) (by omega), MV]
    constructor
    · rintro (h | h | h | h | h | h)
      · have := stackView_space h; omega
      · rcases spc x h with h' | ⟨-, h'⟩ <;> omega
      · exact h
      · have := globView_space h; omega
      · subst h; have : (budMsg s.stackRem tp).space = 5 := rfl; omega
      · have := regView_space h; omega
    · exact fun h => Or.inr (Or.inr (Or.inl h))
  have L2 : ∀ x, x.space = 2 → (L x ↔ x ∈ globView s.globals (fun _ => tp)) := by
    intro x h2
    rw [hV x (by omega) (by omega), MV]
    constructor
    · rintro (h | h | h | h | h | h)
      · have := stackView_space h; omega
      · rcases spc x h with h' | ⟨h', -⟩ <;> omega
      · have := localView_space h; omega
      · exact h
      · subst h; have : (budMsg s.stackRem tp).space = 5 := rfl; omega
      · have := regView_space h; omega
    · exact fun h => Or.inr (Or.inr (Or.inr (Or.inl h)))
  have L5 : ∀ x, x.space = 5 → (L x ↔ x = budMsg s.stackRem tp) := by
    intro x h5
    rw [hV x (by omega) (by omega), MV]
    constructor
    · rintro (h | h | h | h | h | h)
      · have := stackView_space h; omega
      · rcases spc x h with h' | ⟨h', -⟩ <;> omega
      · have := localView_space h; omega
      · have := globView_space h; omega
      · exact h
      · have := regView_space h; omega
    · exact fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have LC : ∀ x, x.space ≠ 16 + E.cid → (x.space = 4 ∨ 16 ≤ x.space) →
      (L x ↔ chainMsgs X E.cid E.k E.rest (svT tp sv) x) := by
    intro x hl hs
    rw [hV x (by omega) (by omega), MV]
    constructor
    · rintro (h | h | h | h | h | h)
      · have := stackView_space h; omega
      · exact h
      · have := localView_space h; omega
      · have := globView_space h; omega
      · subst h; have : (budMsg s.stackRem tp).space = 5 := rfl; omega
      · have := regView_space h; omega
    · exact fun h => Or.inr (Or.inl h)
  refine {
    frames := R.frames, kLt := R.kLt, fn := R.fn, pcEq := R.pcEq, pcLt := R.pcLt, labels := R.labels,
    base := R.base, sbLe := R.sbLe, height := R.height, nloc := R.nloc, gas := R.gas, segLt := R.segLt,
    segbLt := R.segbLt, numS := R.numS, numL := R.numL,
    tpsLt := fun _ _ => htp, tplLt := fun _ _ => htp,
    envSep := fun x h => ⟨h.2.1, h.2.2⟩,
    entry := R.entry, sbLt := R.sbLt, cidLt := R.cidLt,
    heap := {
      pages := R.heap.pages
      mem := ⟨T, fun _ => tp, hT, hTb, fun _ _ => htp, fun x h3 => by
        show (L x ∧ x.space ≠ 0 ∧ x.space ≠ 16 + E.cid) ↔ _
        rw [← hM x h3]
        exact ⟨fun h => h.1, fun h => ⟨h, by omega, by omega⟩⟩⟩
      glob := ⟨fun _ => tp, fun g hgl => ⟨htp, (hg g hgl).2⟩, fun x h2 => by
        show (L x ∧ x.space ≠ 0 ∧ x.space ≠ 16 + E.cid) ↔ _
        rw [← L2 x h2]
        exact ⟨fun h => h.1, fun h => ⟨h, by omega, by omega⟩⟩⟩ },
    calls := {
      cidLtT := R.calls.cidLtT
      chain := ⟨svT tp sv, hc', fun x hx => ?_, fun x hx hs => ?_, ?_⟩
      budget := ⟨tp, htp, fun x h5 => by
        show (L x ∧ x.space ≠ 0 ∧ x.space ≠ 16 + E.cid) ↔ _
        rw [← L5 x h5]
        exact ⟨fun h => h.1, fun h => ⟨h, by omega, by omega⟩⟩⟩ },
    live := fun x => ?_ }
  · -- chain messages are live
    rcases spc x hx with h4 | ⟨h16, hne⟩
    · exact ⟨(LC x (by omega) (Or.inl h4)).mpr hx, by omega, by omega⟩
    · exact ⟨(LC x hne (Or.inr h16)).mpr hx, by omega, hne⟩
  · -- live space-4/≥16 messages are chain messages
    exact Or.inl ((LC x hx.2.2 hs).mp hx.1)
  · rw [chainCharge_svT, chainCharge_congr X E.k sv sv1 (chain_ks hnd hc hc1)]; exact hrl
  · -- the live set
    show L x ↔ x ∈ stackView s.stack (fun _ => tp) ∨ x ∈ localView (16 + E.cid) f.locals (fun _ => tp) ∨
      (L x ∧ x.space ≠ 0 ∧ x.space ≠ 16 + E.cid)
    by_cases h0 : x.space = 0
    · rw [L0 x h0]
      exact ⟨Or.inl, fun h => by
        rcases h with h | h | h
        · exact h
        · have := localView_space h; omega
        · exact absurd h0 h.2.1⟩
    by_cases hl : x.space = 16 + E.cid
    · rw [LL x hl]
      exact ⟨fun h => Or.inr (Or.inl h), fun h => by
        rcases h with h | h | h
        · have := stackView_space h; omega
        · exact h
        · exact absurd hl h.2.2⟩
    · constructor
      · exact fun h => Or.inr (Or.inr ⟨h, h0, hl⟩)
      · rintro (h | h | h)
        · exact absurd (stackView_space h) h0
        · exact absurd (localView_space h) hl
        · exact h.1

/-! ## 4. The next segment's in-boundary relation -/

/-- **Re-entry, abstract form.**  From any boundary relation `BndC` of `s` (the previous segment's
out-cut), a live list `L` that is the view of `s` at `t` outside memory and the gas register, with the
bytes of `s` at a duplicate-free in-bounds `T` as its memory part, is related to `s` at the same time
and gas units, under the STATE message with `cid` replaced by the depth. -/
theorem bndC_reentry {X : Ctx} (hnd : X.M.fns.Nodup) {sg : Nat → Nat × Nat} {s : St} {t S : Nat} {m : List F}
    {L0 : List Msg} (hB : BndC X sg s t S m L0) {L : List Msg}
    (hV : ∀ x, x.space ≠ 3 → x.space ≠ 7 → (x ∈ L ↔ viewAt X s t x))
    {T : List Nat} (hT : T.Nodup) (hTb : ∀ a ∈ T, a < memBytes s)
    (hM : ∀ x, x.space = 3 → (x ∈ L ↔ x ∈ memView T s (fun _ => t))) :
    BndC X sg s t S (m.set 5 ((s.frames.length - 1 : Nat) : F)) L := by
  obtain ⟨⟨k, pc, sb, cid, hm, E, f, tps, tpl, rfl, rfl, rfl, R⟩, -, -⟩ := hB
  obtain ⟨σ, A, sv, -, R', hc, -, -, -⟩ := R.relabelV
  have R'' := RelW.ofView hnd R' rfl hc (idsDepth_svR sv) (tp := t) (by omega) (L := (· ∈ L)) hV hT hTb hM
  have hfr : s.frames.length - 1 = E.rest.length := by rw [R.frames]; simp
  have hb : Bnd X sg s t S (m.set 5 ((s.frames.length - 1 : Nat) : F)) L := by
    refine ⟨E.k, pc, E.sb, E.rest.length, ?_,
      ⟨E.sb, E.rest.length, E.rest, fun x => x ∈ L ∧ x.space ≠ 0 ∧ x.space ≠ 16 + E.rest.length, E.k⟩, f,
      fun _ => t, fun _ => t, rfl, rfl, rfl, R''⟩
    rw [hm, hfr]; rfl
  refine bndC_of_view (tp := t) hb (fun x hx => ?_) (fun y hy => ?_)
  · by_cases h3 : x.space = 3
    · exact Or.inl h3
    by_cases h7 : x.space = 7
    · exact Or.inr (Or.inl h7)
    exact Or.inr (Or.inr ((hV x h3 h7).mp hx))
  · have hs : (ofFields y t).space = y.getD 0 0 := rfl
    have := cutView_sp hy
    exact (hV _ (by rw [hs]; exact this.1) (by rw [hs]; exact this.2)).mpr ⟨y, hy, rfl⟩

theorem memb_mem_space {tr : Trace} {pub : List F} {x : Msg}
    (hx : x ∈ (part Memb.table tr pub 19 busStk true).map decMsg) : x.space = 3 := by
  rw [memb_part, List.map_flatMap] at hx
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hx
  split at hr
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp (by simpa only [List.map_map] using hr)
    exact membMsg_space tr pub r i
  · simp at hr

theorem segb_mem_space {nloc ngl : Nat} {tr : Trace} {pub : List F} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {x : Msg} (hx : x ∈ (part Segb.table tr pub 0 busStk true).map decMsg) : x.space = 7 := by
  rw [segb_part tr pub (seg_h0 H), List.mem_singleton] at hx
  rw [hx]; exact segb_gas_space tr pub

/-- **Re-entry for a segment trace (item 4).**  The previous out-boundary `BndC X sg s t S m L0`; the
next trace's CUTI part is the view of `s` at `t_in` (`cuti_view`), MEMB's in-side productions are
bytes of `s` (`MembIn`, sub-lane MEM), `t_in = t`, `S_in = S`, and SEGB's first STATE message is `m`
with `cid` the depth.  Then the next segment's `h0` holds. -/
theorem seg_reentry {X : Ctx} (hnd : X.M.fns.Nodup) {sg : Nat → Nat × Nat} {s : St} {t S : Nat} {m : List F}
    {L0 : List Msg} (hB : BndC X sg s t S m L0)
    {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hcuti : (part Cut.In.table tr pub 30 busStk true).map decMsg =
      (cutView X s).map (fun y => ofFields y (pub.getD pubTIn 0).toNat))
    (hmemb : MembIn tr pub s) (ht : (pub.getD pubTIn 0).toNat = t) (hS : (pub.getD pubSIn 0).toNat = S)
    (hm : segM0 tr pub = m.set 5 ((s.frames.length - 1 : Nat) : F)) :
    BndC X sg s (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub) (initS tr pub) := by
  rw [ht, hS, hm]
  let MB := (part Memb.table tr pub 19 busStk true).map decMsg
  have hTn : (MB.map Msg.slot).Nodup := nodup_map_of_inj _ MB (memb_part_nodup H) (fun a ha b hb e => by
    rw [(hmemb a ha).2, (hmemb b hb).2, ht, e])
  have hcv : ∀ x, x ∈ (part Cut.In.table tr pub 30 busStk true).map decMsg ↔ viewAt X s t x := by
    intro x; rw [hcuti, ht, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  have cuti_sp : ∀ x, x ∈ (part Cut.In.table tr pub 30 busStk true).map decMsg → x.space ≠ 3 ∧ x.space ≠ 7 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hcv x).mp hx
    exact cutView_sp hy
  refine bndC_reentry hnd hB (fun x h3 h7 => ?_) hTn (fun a ha => ?_) (fun x h3 => ?_)
  · rw [← hcv x]
    unfold initS
    simp only [List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact h
      · exact absurd (memb_mem_space h) h3
      · exact absurd (segb_mem_space H h) h7
    · exact Or.inl
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact (hmemb x hx).1
  · unfold initS
    simp only [List.mem_append]
    have hmv : x ∈ MB ↔ x ∈ memView (MB.map Msg.slot) s (fun _ => t) := by
      rw [mem_memView]
      constructor
      · intro hx
        refine ⟨x.slot, List.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
        have := (hmemb x hx).2; rw [ht] at this; exact this
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        have := (hmemb y hy).2; rw [ht] at this; rw [← this]; exact hy
    rw [← hmv]
    constructor
    · rintro (h | h | h)
      · exact absurd h3 (cuti_sp x h).1
      · exact h
      · have := segb_mem_space H h; omega
    · exact fun h => Or.inr (Or.inl h)

/-- The next segment's first STATE message from the previous one's last, with the publics linked and
the previous `cid_out` the depth. -/
theorem segM0_link {tr tr' : Trace} {pub pub' : List F} {d : Nat}
    (hpc : pub'.getD pubPcIn 0 = pub.getD pubPcOut 0) (ht : pub'.getD pubTIn 0 = pub.getD pubTOut 0)
    (hS : pub'.getD pubSIn 0 = pub.getD pubSOut 0) (hsb : pub'.getD pubSbIn 0 = pub.getD pubSbOut 0)
    (hcid : pub'.getD pubCidIn 0 = ((d : Nat) : F)) :
    segM0 tr' pub' = (segFinM tr pub).set 5 ((d : Nat) : F) := by
  rw [segM0_eq, hpc, ht, hS, hsb, hcid]; rfl

/-! ## 5. The public `cid_out` is the depth -/

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- **SEGB's CIDMAP query `[cidf, cid_out]` is answered**: by SEGB's own `0 ↦ 0`, or by an active
CUTO record row's `slot ↦ F1`. -/
theorem segb_cidm_answer :
    (tr.cell 0 0 (ix Segb.cols "cidf") = 0 ∧ pub.getD pubCidOut 0 = 0) ∨
      ∃ r', r' < tr.height 31 ∧ rowNat tr 31 r' 53 = 1 ∧ rowNat tr 31 r' 0 = 1 ∧
        tr.cell 0 0 (ix Segb.cols "cidf") = ((rowNat tr 31 r' 48 : Nat) : F) ∧
        pub.getD pubCidOut 0 = ((cutoF tr r' 1 : Nat) : F) := by
  have ht0 : 0 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hi : (⟨busCidm, false, .first, [Segb.c "cidf", pv pubCidOut]⟩ : Inter) ∈ Segb.table.inters := by
    simp [Segb.table, Segb.inters]
  have hocc := (mem_occs (A := wasmBaseSegAir nloc ngl) (tr := tr) (pub := pub)).mpr
    ⟨0, ht0, 0, seg_h0 H, _, by rw [seg_t0]; exact hi, rfl⟩
  have hc : ((Expr.first).eval (tr.row pub 0 0)).toNat = 1 := by simp [Expr.eval, Trace.row]; rfl
  obtain ⟨o', ho', hb', hs', hm', hc'⟩ := recv_has_send H 14 (cidm_recv_bits H) hocc rfl rfl hc
  obtain ⟨t', ht', r', hr', i', hi', rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' hm' hc'
  have hmsg : ([Segb.c "cidf", pv pubCidOut] : List Expr).map (·.eval (tr.row pub 0 0)) =
      [tr.cell 0 0 (ix Segb.cols "cidf"), pub.getD pubCidOut 0] := by
    simp [Segb.c, v, pv, Expr.eval, Trace.row]
  rw [hmsg] at hm'
  by_cases h0 : t' = 0
  · subst h0
    have hm := mem_filter14 hi' hb'
    rw [seg_t0, segb_cidm] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl
    · simp at hs'
    · left
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm'
      exact ⟨hm'.1.symm, hm'.2.symm⟩
  by_cases h31 : t' = 31
  · subst h31
    have hm := mem_filter14 hi' hb'
    rw [seg_t31', cuto_cidm] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · simp at hs'
    · simp at hs'
    · right
      obtain ⟨-, i48, -, -, -, -, -, -, -, -, -, -, -, i60, -⟩ := cuto_ix2
      have hmm : rowNat tr 31 r' 60 ≠ 0 := by
        intro h0; simp only [cuto_evalc tr pub r' i60, h0] at hc'; exact hc' rfl
      have h53 := cuto_mm H hr' hmm
      have ha : rowNat tr 31 r' 0 = 1 := by
        have := (cuto_kinds H hr').2.2.2.2.2.2; have := (cuto_bits H hr').1; omega
      refine ⟨r', hr', h53, ha, ?_⟩
      simp only [List.map_cons, List.map_nil, cuto_evalc tr pub r' i48,
        cuto_evalF tr pub r' (show 1 < 7 by omega), List.cons.injEq, and_true] at hm'
      exact ⟨hm'.1.symm, hm'.2.symm⟩
  · exact absurd hb' (seg_cidm_tables nloc ngl t' ht' h0 h31 i' hi')

/-- **The public `cid_out` is the depth of the out-state** (cut case): from the out-boundary
relation `BndC` of `seg_sound`, with `CutoHiLimbs` and `TombDead` (as `seg_sound`). -/
theorem seg_cid_out {X : Ctx} (hnd : X.M.fns.Nodup) (hl : CutoHiLimbs tr) (hT : TombDead tr pub (finS tr pub))
    {sg : Nat → Nat × Nat} {sN : St} {t S : Nat} (hB : BndC X sg sN t S (segFinM tr pub) (finS tr pub)) :
    pub.getD pubCidOut 0 = ((sN.frames.length - 1 : Nat) : F) := by
  have hP := P_val
  obtain ⟨⟨k, pc, sb, cid, hm, E, f, tps, tpl, rfl, rfl, rfl, R⟩, hreg, hsp⟩ := hB
  have hcidf : tr.cell 0 0 (ix Segb.cols "cidf") = ((E.cid : Nat) : F) := by
    have := congrArg (fun l => l.getD 5 0) hm
    simpa [segFinM, stMsg] using this
  have hfr : sN.frames.length - 1 = E.rest.length := by rw [R.frames]; simp
  rw [hfr]
  have hcl := R.cidLt
  obtain ⟨σ, A, hok, -, -, -, -⟩ := R.relabel_viewL hnd hreg hsp
  have hI := idsOK_of_relW R hok
  obtain ⟨sv, hc, -, -, hd, rfl⟩ := hok
  have hF := cutoFin_of H (seg_cuto_in_fin (tr := tr) (pub := pub)) (seg_finSplit H) hT
  rcases segb_cidm_answer H with ⟨h0, hc0⟩ | ⟨r', hr', h53, ha, hsl, hco⟩
  · rw [hcidf] at h0
    have e0 : E.cid = 0 := natEq (R := 0) h0 (by omega) (by omega)
    rw [(R.entry e0).1, hc0]; rfl
  · rw [hcidf] at hsl
    have es : E.cid = rowNat tr 31 r' 48 := natEq hsl (by omega) (rowNat_lt _ _ _ _)
    obtain ⟨hdep, -⟩ := cuto_k4_dep H hl hI hF hr' h53
    have hF1 := (cuto_fieldfacts H hl hr' ha).2.2.2.1 h53
    rw [hco, hF1, hdep, ← es, hd.top, hc.len]

end

end Cuti
end WasmBase

#print axioms WasmBase.Cuti.RelW.ofView
#print axioms WasmBase.Cuti.bndC_reentry
#print axioms WasmBase.Cuti.seg_reentry
#print axioms WasmBase.Cuti.seg_cid_out
