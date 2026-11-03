import WasmBase.Main.SegRows

/-!
# WasmBase.Main.SegView — the AIR's boundary view is the spec view (E2E M4b, sub-lane S1)

(module documentation: see the end of the file)
-/

namespace WasmBase

open ZkFormal.Algebra
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## 1. The boundary facts `RelW` does not carry -/

/-- The channel spaces a live message may be in: operand stack 0, globals 2, memory 3, call records
4, stack budget 5, registers 6, gas register 7, locals `≥ 16`. -/
def SpaceOK (x : Msg) : Prop :=
  x.space = 0 ∨ x.space = 2 ∨ x.space = 3 ∨ x.space = 4 ∨ x.space = 5 ∨ x.space = 6 ∨ x.space = 7 ∨
    16 ≤ x.space

/-- **Register clause** (item 1): the space-6 live messages are exactly the register file's view,
for some producer times (`Register.RegBusSound`, the statement M1 left as an obligation). -/
def RegC (live : Msg → Prop) (s : St) : Prop :=
  ∃ tpr : Nat → Nat, Register.RegBusSound live s.registers tpr

/-- **Space clause** (item 2): every live message is in an allowed space. -/
def SpC (live : Msg → Prop) : Prop := ∀ x, live x → SpaceOK x

/-- **The extended boundary relation**: `Bnd` plus the register and space clauses. -/
def BndC (X : Ctx) (sg : Nat → Nat × Nat) (s : St) (t S : Nat) (m : List F) (L : List Msg) : Prop :=
  Bnd X sg s t S m L ∧ RegC (· ∈ L) s ∧ SpC (· ∈ L)

/-! ## 2. Producer times do not matter to `fieldsOf` -/

theorem img_stackView {stk : Array Val} {tps tps' : Nat → Nat} {y : List Nat} :
    (∃ x ∈ stackView stk tps, fieldsOf x = y) → (∃ x ∈ stackView stk tps', fieldsOf x = y) := by
  rintro ⟨x, hx, rfl⟩
  obtain ⟨i, hi, rfl⟩ := mem_stackView.mp hx
  exact ⟨_, mem_stackView.mpr ⟨i, hi, rfl⟩, rfl⟩

theorem img_localView {sp : Nat} {locs : Array Val} {tpl tpl' : Nat → Nat} {y : List Nat} :
    (∃ x ∈ localView sp locs tpl, fieldsOf x = y) → (∃ x ∈ localView sp locs tpl', fieldsOf x = y) := by
  rintro ⟨x, hx, rfl⟩
  obtain ⟨i, hi, rfl⟩ := mem_localView.mp hx
  exact ⟨_, mem_localView.mpr ⟨i, hi, rfl⟩, rfl⟩

theorem img_globView {gs : Array Val} {tpg tpg' : Nat → Nat} {y : List Nat} :
    (∃ x ∈ globView gs tpg, fieldsOf x = y) → (∃ x ∈ globView gs tpg', fieldsOf x = y) := by
  rintro ⟨x, hx, rfl⟩
  obtain ⟨i, hi, rfl⟩ := mem_globView.mp hx
  exact ⟨_, mem_globView.mpr ⟨i, hi, rfl⟩, rfl⟩

theorem img_regView {regs : Array (Nat × ByteArray)} {tpr tpr' : Nat → Nat} {y : List Nat} :
    (∃ x ∈ Register.view regs tpr, fieldsOf x = y) → (∃ x ∈ Register.view regs tpr', fieldsOf x = y) := by
  rintro ⟨x, hx, rfl⟩
  obtain ⟨rid, d, hrd, hx⟩ := Register.mem_view.mp hx
  rcases Register.mem_regMsgs.mp hx with rfl | ⟨i, hi, rfl⟩
  · exact ⟨_, Register.view_len_mem (tp := tpr') hrd, rfl⟩
  · exact ⟨_, Register.view_byte (tp := tpr') hrd hi, rfl⟩

/-! ## 3. The caller chain, against the frames by depth -/

/-- The call-record part of `frameMsgs` (the record of the activation at depth `d ≥ 1`). -/
def recOf (X : Ctx) (fr : List Frame) (d : Nat) : List Msg :=
  if d = 0 then [] else
    [callMsg d (X.offOf (X.kOf (fr.getD (d - 1) default).fn) + (fr.getD (d - 1) default).pc)
      (fr.getD (d - 1) default).base (d - 1) ((X.p.funcs[(fr.getD d default).fn]?).getD default).stackCharge 0]

theorem frameMsgs_eq (X : Ctx) (fr : List Frame) (d : Nat) :
    frameMsgs X fr d = localView (16 + d) (fr.getD d default).locals (fun _ => 0) ++ recOf X fr d := rfl

/-- The frames' messages below depth `D`, plus the record of depth `D`: what the caller chain of the
frame at depth `D` covers. -/
def chainView (X : Ctx) (G : List Frame) (D : Nat) : List Msg :=
  (List.range D).flatMap (frameMsgs X G) ++ recOf X G D

/-- Saved-caller ids are depths (the bottom caller 0). -/
def IdsDepth : List Saved → Prop
  | [] => True
  | c :: sv => c.cid = sv.length ∧ IdsDepth sv

theorem idsDepth_svR : ∀ sv : List Saved, IdsDepth (svR sv)
  | [] => trivial
  | c :: sv => ⟨by simp [svR], idsDepth_svR sv⟩

/-- With a duplicate-free function list, the checked index of `fnOf k` is `k`. -/
theorem kOf_fnOf {X : Ctx} (hnd : X.M.fns.Nodup) {k : Nat} (hk : k < X.nf) : X.kOf (X.fnOf k) = k := by
  unfold Ctx.kOf Ctx.fnOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.Nodup.idxOf_getElem hnd k hk

theorem getD_append_left {α : Type} (l l' : List α) (d : α) {n : Nat} (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem mem_chainView_succ {X : Ctx} {G : List Frame} {n : Nat} {x : Msg} :
    x ∈ chainView X G (n + 1) ↔
      x ∈ chainView X G n ∨ x ∈ localView (16 + n) (G.getD n default).locals (fun _ => 0) ∨
        x ∈ recOf X G (n + 1) := by
  simp only [chainView, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_append, frameMsgs_eq]
  constructor
  · rintro ((h | h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
  · rintro ((h | h) | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr h

theorem chainView_zero (X : Ctx) (G : List Frame) : chainView X G 0 = [] := by
  simp [chainView, recOf]

section Chain
variable {X : Ctx} {t : Nat}

/-- **The caller chain is the frames below, by depth.**  For a chain whose ids are depths, the
chain messages (call records of depths `1 … D`, locals of depths `0 … D−1`) have, up to producer
times, the fields of `chainView` of the frame list `G` (entry frame first, `G[D] = f` the current
frame).  Needs `X.M.fns.Nodup` to recompute a caller's checked index from its function. -/
theorem chain_img (hnd : X.M.fns.Nodup) :
    ∀ {D sb k : Nat} {rest : List Frame} {sv : List Saved},
      Chain X t D sb k rest sv → IdsDepth sv → D = rest.length →
      ∀ (G : List Frame) (f : Frame), f.fn = X.fnOf k →
      (∀ d, d ≤ rest.length → G.getD d default = (rest.reverse ++ [f]).getD d default) →
      ∀ y, (∃ x, chainMsgs X D k rest sv x ∧ fieldsOf x = y) ↔ (∃ x ∈ chainView X G rest.length, fieldsOf x = y)
  | _, _, _, [], [], _, _, _, G, f, _, _, y => by
    constructor
    · rintro ⟨x, hx, -⟩; exact hx.elim
    · rintro ⟨x, hx, -⟩; simp [chainView_zero] at hx
  | D, sb, k, fc :: rest, c :: sv, hc, hids, hD, G, f, hf, hG, y => by
    obtain ⟨a1, a2, a3, -, -, -, -, -, -, -, -, -, a13⟩ := hc
    have hlen := a13.len
    have hcid : c.cid = rest.length := by rw [hids.1, hlen]
    have hD' : D = rest.length + 1 := by simpa using hD
    have hG' : ∀ d, d ≤ rest.length → G.getD d default = (rest.reverse ++ [fc]).getD d default := by
      intro d hd
      rw [hG d (by simp; omega)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [show [fc, f] = [fc] ++ [f] from rfl, ← List.append_assoc, getD_append_left _ _ _ (by simp; omega)]
    have IH := chain_img hnd a13 hids.2 hcid G fc a2 hG'
    have gn : G.getD rest.length default = fc := by
      rw [hG' _ (Nat.le_refl _)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    have gn1 : G.getD (rest.length + 1) default = f := by
      rw [hG _ (by simp)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    have hrec : recOf X G (rest.length + 1) =
        [callMsg (rest.length + 1) (X.offOf c.k + fc.pc) c.sb rest.length (X.pfOf k).stackCharge 0] := by
      simp only [recOf, Nat.add_sub_cancel, show rest.length + 1 ≠ 0 by omega, ite_false, gn, gn1, hf,
        a2, kOf_fnOf hnd a1, a3]
      rfl
    simp only [List.length_cons]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | hx | hx
      · refine ⟨_, mem_chainView_succ.mpr (Or.inr (Or.inr (by rw [hrec]; exact List.mem_singleton_self _))), ?_⟩
        simp [fieldsOf, callMsg, hD', hcid]
      · rw [hcid] at hx
        obtain ⟨x', hx', e⟩ := img_localView (tpl' := fun _ => 0) ⟨x, hx, rfl⟩
        exact ⟨x', mem_chainView_succ.mpr (Or.inr (Or.inl (by rw [gn]; exact hx'))), e⟩
      · obtain ⟨x', hx', e⟩ := (IH (fieldsOf x)).mp ⟨x, hx, rfl⟩
        exact ⟨x', mem_chainView_succ.mpr (Or.inl hx'), e⟩
    · rintro ⟨x, hx, rfl⟩
      rcases mem_chainView_succ.mp hx with hx | hx | hx
      · obtain ⟨x', hx', e⟩ := (IH (fieldsOf x)).mpr ⟨x, hx, rfl⟩
        exact ⟨x', Or.inr (Or.inr hx'), e⟩
      · rw [gn] at hx
        obtain ⟨x', hx', e⟩ := img_localView (tpl' := c.tpl) ⟨x, hx, rfl⟩
        exact ⟨x', Or.inr (Or.inl (by rw [hcid]; exact hx')), e⟩
      · rw [hrec, List.mem_singleton] at hx
        subst hx
        refine ⟨_, Or.inl rfl, ?_⟩
        simp [fieldsOf, callMsg, hD', hcid]
  | _, _, _, [], _ :: _, hc, _, _, _, _, _, _, _ => hc.elim
  | _, _, _, _ :: _, [], hc, _, _, _, _, _, _, _ => hc.elim

end Chain

/-! ## 4. Relabelling, with the chain in both directions -/

/-- `RelW.relabel` (`Main/SegCut.lean`), re-proved with one more conclusion: every message of the
relabelled caller chain is live (the converse of `RelW.relabel`'s last conjunct).  `RelW.relabel`
proves it internally but does not export it; the proof below is that proof with the extra
conjunct (copied so `SegCut.lean`, which other sub-lanes edit, is untouched). -/
theorem RelW.relabelV {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) :
    ∃ (σ : Nat → Nat) (A : List Nat) (sv : List Saved), σ E.cid = E.rest.length ∧
      RelW X ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩ s f tps tpl t pc S (relabelLive σ A live) a b ∧
      Chain X t E.rest.length E.sb E.k E.rest (svR sv) ∧
      (∀ y, relabelLive σ A E.live y → (y.space = 4 ∨ 16 ≤ y.space) →
        chainMsgs X E.rest.length E.k E.rest (svR sv) y) ∧
      (∀ y, chainMsgs X E.rest.length E.k E.rest (svR sv) y → relabelLive σ A E.live y) := by
  obtain ⟨sv, hc, hin, hout, hrl⟩ := R.calls.chain
  obtain ⟨tpb, htpb, hbud⟩ := R.calls.budget
  obtain ⟨σ, hd⟩ := DepthOK.exists hc
  have hlen := hc.len
  have htop : σ E.cid = E.rest.length := by rw [hd.top, hlen]
  let A := E.cid :: sv.map Saved.cid
  have keepChain : ∀ x, chainMsgs X E.cid E.k E.rest sv x → keepA A x := by
    intro x hx h16
    rcases chainMsgs_space_ids hx with h | ⟨-, h⟩
    · omega
    · exact List.mem_cons_of_mem _ h
  -- low spaces are untouched
  have lowE : ∀ y, y.space ≠ 4 → y.space < 16 → (relabelLive σ A E.live y ↔ E.live y) :=
    fun y h4 h16 => relabel_low h4 h16
  -- the relabelled outer messages in space 4 or `≥ 16` are exactly the relabelled chain
  have outR : ∀ y, relabelLive σ A E.live y → (y.space = 4 ∨ 16 ≤ y.space) →
      chainMsgs X E.rest.length E.k E.rest (svR sv) y := by
    rintro y ⟨x, hx, hk, rfl⟩ hs
    have hxs : x.space = 4 ∨ 16 ≤ x.space := by
      have := rlMsg_space σ x
      by_cases a4 : x.space = 4
      · exact Or.inl a4
      by_cases a16 : 16 ≤ x.space
      · exact Or.inr a16
      rw [if_neg a4, if_neg a16] at this; rw [this] at hs; omega
    rcases hout x hx hxs with h | ⟨d1, -, d3, d4⟩
    · rw [hlen]; exact chainMsgs_rl hc hd x h
    · exfalso
      rcases List.mem_cons.mp (hk d1) with h | h
      · exact d3 (by omega)
      · obtain ⟨c, hcm, hce⟩ := List.mem_map.mp h
        exact d4 c hcm (by omega)
  have inR : ∀ y, chainMsgs X E.rest.length E.k E.rest (svR sv) y → relabelLive σ A E.live y := by
    intro y hy
    have hy' : chainMsgs X sv.length E.k E.rest (svR sv) y := by rw [← hlen]; exact hy
    obtain ⟨x, hx, rfl⟩ := chainMsgs_rl_inv hc hd y hy'
    exact ⟨x, hin x hx, keepChain x hx, rfl⟩
  refine ⟨σ, A, sv, htop, ?_, by rw [hlen]; exact hc.svR, outR, inR⟩
  have hsepR : ∀ x, relabelLive σ A E.live x → x.space ≠ 0 ∧ x.space ≠ 16 + E.rest.length := by
    rintro y ⟨x, hx, hk, rfl⟩
    have hsep := R.envSep x hx
    have hs := rlMsg_space σ x
    by_cases a4 : x.space = 4
    · rw [if_pos a4] at hs; rw [hs]; omega
    by_cases a16 : 16 ≤ x.space
    · rw [if_neg a4, if_pos a16] at hs; rw [hs]
      refine ⟨by omega, ?_⟩
      rcases List.mem_cons.mp (hk a16) with h | h
      · exact absurd (show x.space = E.lsp by simp only [Env.lsp]; omega) hsep.2
      · obtain ⟨c, hcm, hce⟩ := List.mem_map.mp h
        have := DepthOK.below hc hd c hcm
        rw [hce] at this; omega
    · rw [if_neg a4, if_neg a16] at hs; rw [hs]; omega
  have hheap : HeapOK ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩ s t := by
    obtain ⟨T, tpm, h1, h2, h3, h4⟩ := R.heap.mem
    obtain ⟨tpg, g1, g2⟩ := R.heap.glob
    exact ⟨R.heap.pages, ⟨T, tpm, h1, h2, h3, fun x hx => (lowE x (by omega) (by omega)).trans (h4 x hx)⟩,
      ⟨tpg, g1, fun x hx => (lowE x (by omega) (by omega)).trans (g2 x hx)⟩⟩
  have hcalls : CallsOK X ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩ s t := by
    refine ⟨?_, ⟨svR sv, ?_, ?_, ?_, ?_⟩, ⟨tpb, htpb, fun x hx => (lowE x (by omega) (by omega)).trans (hbud x hx)⟩⟩
    · have := hc.len_le; have := R.calls.cidLtT; show E.rest.length < t; omega
    · show Chain X t E.rest.length E.sb E.k E.rest (svR sv); rw [hlen]; exact hc.svR
    · intro y hy
      have hy' : chainMsgs X sv.length E.k E.rest (svR sv) y := by rw [← hlen]; exact hy
      obtain ⟨x, hx, rfl⟩ := chainMsgs_rl_inv hc hd y hy'
      exact ⟨x, hin x hx, keepChain x hx, rfl⟩
    · intro y hy hs; exact Or.inl (outR y hy hs)
    · show s.stackRem + chainCharge X E.k (svR sv) < 2 ^ 30; rw [chainCharge_svR]; exact hrl
  refine ⟨R.frames, R.kLt, R.fn, R.pcEq, R.pcLt, R.labels, R.base, R.sbLe, R.height, R.nloc, R.gas, R.segLt,
    R.segbLt, R.numS, R.numL, R.tpsLt, R.tplLt, hsepR, ?_, R.sbLt, ?_, hheap, hcalls, ?_⟩
  · intro h0
    have h0' : E.rest.length = 0 := h0
    have hr : E.rest = [] := List.length_eq_zero_iff.mp h0'
    have hsv : sv = [] := List.length_eq_zero_iff.mp (by rw [← hlen, h0'])
    refine ⟨hr, ?_⟩
    have hc0 := hc; rw [hr, hsv] at hc0; exact hc0.2
  · have := hc.len_le; have := R.cidLt; show E.rest.length < 2 ^ 28; omega
  · intro y
    constructor
    · rintro ⟨x, hx, hk, rfl⟩
      rcases (R.live x).mp hx with h | h | h
      · obtain ⟨i, hi, rfl⟩ := mem_stackView.mp h
        left; rw [rlMsg_low (by simp) (by simp)]; exact mem_stackView.mpr ⟨i, hi, rfl⟩
      · right; left
        have := localView_rl (σ := σ) h
        simp only [Env.lsp] at this ⊢; rwa [htop] at this
      · right; right; exact ⟨x, h, hk, rfl⟩
    · rintro (h | h | h)
      · obtain ⟨i, hi, rfl⟩ := mem_stackView.mp h
        refine ⟨_, (R.live _).mpr (Or.inl h), fun h' => absurd h' (by simp), (rlMsg_low (by simp) (by simp)).symm⟩
      · simp only [Env.lsp] at h
        obtain ⟨x, hx, rfl⟩ := localView_rl_inv htop h
        refine ⟨x, (R.live x).mpr (Or.inr (Or.inl hx)), ?_, rfl⟩
        intro _; obtain ⟨j, -, rfl⟩ := mem_localView.mp hx; simp [A]
      · obtain ⟨x, hx, hk, rfl⟩ := h
        exact ⟨x, (R.live x).mpr (Or.inr (Or.inr hx)), hk, rfl⟩

/-! ## 5. The view theorem: the kept live set is `cutView` -/

theorem mem_cutMsgs_frames {X : Ctx} {s : St} {f : Frame} {rest : List Frame} (hfr : s.frames = f :: rest)
    {x : Msg} :
    x ∈ (List.range s.frames.length).flatMap (frameMsgs X s.frames.reverse) ↔
      x ∈ chainView X s.frames.reverse rest.length ∨ x ∈ localView (16 + rest.length) f.locals (fun _ => 0) := by
  have hl : s.frames.length = rest.length + 1 := by rw [hfr]; simp
  have hg : s.frames.reverse.getD rest.length default = f := by
    rw [hfr]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  rw [hl]
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, frameMsgs_eq, hg, chainView]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- **The view theorem, at a depth-labelled state.**  If the activation ids are depths (`E.cid =
E.rest.length`, the caller chain's ids are depths), the outer space-4/`≥ 16` messages are exactly
the chain's, the register clause and the space clause hold, and the module's function list has no
duplicates, then the live messages outside memory (3) and the gas register (7) have, up to producer
times, exactly the fields of `cutView X s`. -/
theorem view_eq_of_depth {X : Ctx} (hnd : X.M.fns.Nodup) {E : Env} {s : St} {f : Frame}
    {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat} {sv : List Saved}
    (R : RelW X E s f tps tpl t pc S live a b) (hD : E.cid = E.rest.length)
    (hc : Chain X t E.cid E.sb E.k E.rest sv) (hids : IdsDepth sv)
    (hin : ∀ y, chainMsgs X E.cid E.k E.rest sv y → E.live y)
    (hout : ∀ y, E.live y → (y.space = 4 ∨ 16 ≤ y.space) → chainMsgs X E.cid E.k E.rest sv y)
    (hreg : RegC live s) (hsp : SpC live) :
    ∀ y, (∃ x, live x ∧ x.space ≠ 3 ∧ x.space ≠ 7 ∧ fieldsOf x = y) ↔ y ∈ cutView X s := by
  obtain ⟨tpr, hr⟩ := hreg
  obtain ⟨tpg, -, hg⟩ := R.heap.glob
  obtain ⟨tpb, -, hb⟩ := R.calls.budget
  have CI := chain_img (t := t) hnd hc hids hD s.frames.reverse f R.fn (fun d _ => by rw [R.frames]; simp)
  intro y
  rw [mem_cutView]
  simp only [cutMsgs, List.mem_append, List.mem_singleton, mem_cutMsgs_frames R.frames]
  constructor
  · rintro ⟨x, hx, h3, h7, rfl⟩
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
      rcases hsp x hx with s0 | s2 | s3 | s4 | s5 | s6 | s7 | s16
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
      exact ⟨_, (R.live _).mpr (Or.inl hx'), by simp, by simp, e⟩
    · obtain ⟨x', hx', e⟩ := (CI (fieldsOf x)).mpr ⟨x, h, rfl⟩
      have hs := chainMsgs_space_ids hx'
      refine ⟨x', (R.live x').mpr (Or.inr (Or.inr (hin x' hx'))), ?_, ?_, e⟩ <;> omega
    · obtain ⟨x', hx', e⟩ := img_localView (tpl' := tpl) ⟨x, h, rfl⟩
      obtain ⟨j, -, rfl⟩ := mem_localView.mp hx'
      refine ⟨_, (R.live _).mpr (Or.inr (Or.inl ?_)), by simp; omega, by simp; omega, e⟩
      simpa only [Env.lsp, hD] using hx'
    · obtain ⟨x', hx', e⟩ := img_globView (tpg' := tpg) ⟨x, h, rfl⟩
      obtain ⟨g, -, rfl⟩ := mem_globView.mp hx'
      exact ⟨_, (R.live _).mpr (Or.inr (Or.inr ((hg _ rfl).mpr hx'))), by simp, by simp, e⟩
    · subst h
      exact ⟨budMsg s.stackRem tpb, (R.live _).mpr (Or.inr (Or.inr ((hb _ rfl).mpr rfl))),
        by simp [budMsg], by simp [budMsg], rfl⟩
    · obtain ⟨x', hx', e⟩ := img_regView (tpr' := tpr) ⟨x, h, rfl⟩
      have h6 : x'.space = 6 := by
        obtain ⟨rid, d, -, hx''⟩ := Register.mem_view.mp hx'
        rcases Register.mem_regMsgs.mp hx'' with rfl | ⟨i, -, rfl⟩ <;> rfl
      exact ⟨x', (hr x' h6).mpr hx', by omega, by omega, e⟩

/-! ## 6. Relabelling keeps the clauses; the view theorem at a cut -/

theorem RegC.relabel {σ : Nat → Nat} {A : List Nat} {live : Msg → Prop} {s : St} (h : RegC live s) :
    RegC (relabelLive σ A live) s := by
  obtain ⟨tpr, hr⟩ := h
  refine ⟨tpr, fun x hx => ?_⟩
  have h6 : x.space = 6 := hx
  exact (relabel_low (by omega) (by omega)).trans (hr x hx)

theorem SpaceOK.rlMsg {σ : Nat → Nat} {x : Msg} (h : SpaceOK x) : SpaceOK (rlMsg σ x) := by
  have hs := rlMsg_space σ x
  unfold SpaceOK at h ⊢
  by_cases a4 : x.space = 4
  · rw [if_pos a4] at hs; omega
  by_cases a16 : 16 ≤ x.space
  · rw [if_neg a4, if_pos a16] at hs; omega
  · rw [if_neg a4, if_neg a16] at hs; omega

theorem SpC.relabel {σ : Nat → Nat} {A : List Nat} {live : Msg → Prop} (h : SpC live) :
    SpC (relabelLive σ A live) := by
  rintro y ⟨x, hx, -, rfl⟩
  exact (h x hx).rlMsg

/-- **Relabelling to depths, with the view.**  `RelW.relabel`, plus: the relabelled live set keeps
the register and space clauses, and (with `X.M.fns.Nodup`) its part outside spaces 3 and 7 is,
up to producer times, exactly `cutView X s`. -/
theorem RelW.relabel_view {X : Ctx} (hnd : X.M.fns.Nodup) {E : Env} {s : St} {f : Frame}
    {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop} {a b : Nat}
    (R : RelW X E s f tps tpl t pc S live a b) (hreg : RegC live s) (hsp : SpC live) :
    ∃ (σ : Nat → Nat) (A : List Nat),
      RelW X ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩ s f tps tpl t pc S
        (relabelLive σ A live) a b ∧
      RegC (relabelLive σ A live) s ∧ SpC (relabelLive σ A live) ∧
      ∀ y, (∃ x, relabelLive σ A live x ∧ x.space ≠ 3 ∧ x.space ≠ 7 ∧ fieldsOf x = y) ↔ y ∈ cutView X s := by
  obtain ⟨σ, A, sv, -, R', hc, hout, hin⟩ := R.relabelV
  refine ⟨σ, A, R', hreg.relabel, hsp.relabel, ?_⟩
  exact view_eq_of_depth hnd R' rfl hc (idsDepth_svR sv) hin hout hreg.relabel hsp.relabel

theorem mem_relabelList {σ : Nat → Nat} {A : List Nat} {L : List Msg} {y : Msg} :
    y ∈ (L.filter (fun x => decide (keepA A x))).map (rlMsg σ) ↔ relabelLive σ A (· ∈ L) y := by
  simp only [relabelLive, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hx, hk⟩, rfl⟩; exact ⟨x, hx, hk, rfl⟩
  · rintro ⟨x, hx, hk, rfl⟩; exact ⟨x, ⟨hx, hk⟩, rfl⟩

/-- **`cutView_eq`: the boundary view at a cut.**  From the extended boundary relation `BndC` (and a
duplicate-free function list), the relabelled live list `L'` of `Bnd.relabel` satisfies `BndC` again
(STATE's `cid` replaced by the depth), and its part outside memory (space 3) and the gas register
(space 7) has, up to producer times, exactly the members of `cutView X s`. -/
theorem cutView_eq {X : Ctx} (hnd : X.M.fns.Nodup) {sg : Nat → Nat × Nat} {s : St} {t S : Nat}
    {m : List F} {L : List Msg} (h : BndC X sg s t S m L) :
    ∃ (σ : Nat → Nat) (A : List Nat),
      BndC X sg s t S (m.set 5 ((s.frames.length - 1 : Nat) : F))
        ((L.filter (fun x => decide (keepA A x))).map (rlMsg σ)) ∧
      ∀ y, (∃ x ∈ (L.filter (fun x => decide (keepA A x))).map (rlMsg σ),
        x.space ≠ 3 ∧ x.space ≠ 7 ∧ fieldsOf x = y) ↔ y ∈ cutView X s := by
  obtain ⟨⟨k, pc, sb, cid, rfl, E, f, tps, tpl, rfl, rfl, rfl, R⟩, hreg, hsp⟩ := h
  obtain ⟨σ, A, R', hreg', hsp', hv⟩ := R.relabel_view hnd hreg hsp
  have hfr : s.frames.length - 1 = E.rest.length := by rw [R.frames]; simp
  have e : (fun y => y ∈ (L.filter (fun x => decide (keepA A x))).map (rlMsg σ)) = relabelLive σ A (· ∈ L) :=
    funext fun y => propext mem_relabelList
  refine ⟨σ, A, ⟨⟨E.k, pc, E.sb, E.rest.length, ?_, ⟨E.sb, E.rest.length, E.rest, relabelLive σ A E.live, E.k⟩,
    f, tps, tpl, rfl, rfl, rfl, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hfr]; rfl
  · rw [e]; exact R'
  · rw [e]; exact hreg'
  · rw [e]; exact hsp'
  · intro y
    rw [← hv y]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, mem_relabelList.mp hx, h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, mem_relabelList.mpr hx, h⟩

/-! ## 7. An invariant carried through a segment

`exec_of_rows_cut` (`Main/SegCut.lean`) re-run with an extra predicate `Q` on (state, live set),
preserved by every row (`RowQ`).  The proof is `exec_of_rows_cut`'s (cut case only), with `Q` added
to the induction hypothesis; it is copied rather than generalised in place so that `SegCut.lean`,
which other sub-lanes edit, is untouched. -/

/-- **A row preserves `Q`**: from a related pre-state whose live set satisfies `Q`, a continuing
step (the row's `cons` live) lands in a state whose live set `stepLive live cons prod` satisfies
`Q`. -/
def RowQ (X : Ctx) (Q : St → (Msg → Prop) → Prop) (inS : List F) (cons prod : List Msg) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat)
    (s' : St), RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    (∀ x ∈ cons, live x) → step X.cfg X.p s = .cont s' → Q s live → Q s' (stepLive live cons prod)

section
variable (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
  (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)

/-- **`exec_of_rows_cut` with an invariant.**  The hypotheses of `exec_of_rows_cut`, plus `Q`
preserved by every row and true at the start; at a cut, `Q` holds of the final state and live set. -/
theorem exec_of_rows_cutQ (sg : Nat → Nat × Nat) (st : Nat) (hst2 : st ≤ 2)
    (hrows : ∀ r ∈ act, RowFactsSegMap X (inS r) (outS r) (cons r) (prod r) sg)
    (t0 S0 : Nat) (m0 : List F) (sbf cidf : F)
    (hst : (m0 :: act.map outS).Perm ([pcf, N, Sf, (st : F), sbf, cidf] :: act.map inS))
    (hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp ≤ t0)
    (ht : t0 + act.length + 1 + (2 ^ 30 + 2 ^ 16) < ZkFormal.Algebra.P)
    (hfee : S0 + (act.length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} (h0 : Bnd X sg s0 t0 S0 m0 init)
    (Q : St → (Msg → Prop) → Prop) (hQ : ∀ r ∈ act, RowQ X Q (inS r) (cons r) (prod r))
    (hQ0 : Q s0 (· ∈ init)) :
    N.toNat = t0 + act.length + 1 ∧
    (st = 0 → ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .cont sN ∧
      (∀ m, run X.cfg X.p (act.length + m) s0 = run X.cfg X.p m sN) ∧
      Bnd X sg sN (t0 + act.length) Sf.toNat [pcf, N, Sf, ((0 : Nat) : F), sbf, cidf] fin ∧
      Q sN (· ∈ fin)) := by
  have hP' := P_val
  obtain ⟨k0, pc0, sb0, cid0, rfl, R0⟩ := h0
  have hS0 : S0 < ZkFormal.Algebra.P := by
    have : 1 * 1 ≤ (act.length + 1) * (X.maxFee + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  -- (A) the chain
  let g : ρ → List F × List F := fun r => (inS r, outS r)
  have hE1 : (act.map g).map Prod.snd = act.map outS := by simp [g, List.map_map]
  have hE2 : (act.map g).map Prod.fst = act.map inS := by simp [g, List.map_map]
  have hstepE : ∀ e ∈ act.map g, lvl e.2 = lvl e.1 + 1 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact (hrows r hr).tsOut
  obtain ⟨es, hes, hpath⟩ := chain (act.map g) (stMsg (X.offOf k0 + pc0) (t0 + 1) S0 0 sb0 cid0)
    [pcf, N, Sf, (st : F), sbf, cidf] lvl (by rw [hE1, hE2]; exact hst) hstepE (by simp; omega)
  obtain ⟨rs, hrs, rfl⟩ := perm_map_lift g es act hes
  have hlenrs : rs.length = act.length := hrs.length_eq
  have hmem : ∀ k (hk : k < rs.length), rs[k] ∈ act := fun k hk => hrs.subset (List.getElem_mem hk)
  obtain ⟨lk, lfin⟩ := path_levels lvl (rs.map g) _ _ hpath (fun e he => hstepE e (hes.subset he))
  obtain ⟨link, ends, enil⟩ := path_link (rs.map g) _ _ hpath
  simp only [List.length_map, List.getElem_map] at lk lfin link ends enil
  have l0 : lvl (stMsg (X.offOf k0 + pc0) (t0 + 1) S0 0 sb0 cid0) = ((t0 + 1 : Nat) : F) := rfl
  have lvlk : ∀ k (hk : k < rs.length), lvl (inS rs[k]) = ((t0 + k + 1 : Nat) : F) := by
    intro k hk; rw [lk k hk, l0, ← Lean.Grind.Semiring.natCast_add, show t0 + 1 + k = t0 + k + 1 by omega]
  have RFS : ∀ k (hk : k < rs.length),
      RowFactsSeg X (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k])
        (sg (t0 + k + 1)) (sg (t0 + k + 1 + 1)) :=
    fun k hk => by
      have e : lvl (inS rs[k]) = ((t0 + k + 1 : Nat) : F) := lvlk k hk
      have h := hrows rs[k] (hmem k hk)
      unfold RowFactsSegMap at h
      rwa [e, Fp.toNat_cast_of_lt (by omega)] at h
  have RF : ∀ k (hk : k < rs.length), RowFactsFlat X (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k]) :=
    fun k hk => (RFS k hk).toFlat
  have hN : N.toNat = t0 + act.length + 1 := by
    have : N = ((t0 + rs.length + 1 : Nat) : F) := by
      have e : lvl [pcf, N, Sf, (st : F), sbf, cidf] = N := rfl
      rw [← e, lfin, l0, ← Lean.Grind.Semiring.natCast_add, show t0 + 1 + rs.length = t0 + rs.length + 1 by omega]
    rw [this, Fp.toNat_cast_of_lt (by omega), hlenrs]
  -- position messages: `pos k` is the STATE message entering step `k` (the final one at `k = n`)
  let pos : Nat → List F := fun k => if h : k < rs.length then inS rs[k] else [pcf, N, Sf, (st : F), sbf, cidf]
  have pos_in : ∀ k (hk : k < rs.length), pos k = inS rs[k] := fun k hk => by simp [pos, hk]
  have pos_out : ∀ k (hk : k < rs.length), pos (k + 1) = outS rs[k] := by
    intro k hk
    by_cases h1 : k + 1 < rs.length
    · simp only [pos, h1, dite_true]; exact link k h1
    · have : k = rs.length - 1 := by omega
      subst this
      simp only [pos, h1, dite_false]; exact (ends (by omega)).2.symm
  have posN : pos rs.length = [pcf, N, Sf, (st : F), sbf, cidf] := by simp [pos]
  have pos0 : pos 0 = stMsg (X.offOf k0 + pc0) (t0 + 1) S0 0 sb0 cid0 := by
    by_cases h : 0 < rs.length
    · rw [pos_in 0 h]; exact (ends h).1
    · have h' : rs.length = 0 := by omega
      have := posN; rw [h'] at this; rw [this]; exact (enil h').symm
  -- gas units along the path: no wrap-around
  have step1 : ∀ k (hk : k < rs.length), (gasF (pos k)).toNat ≤ S0 + k * X.maxFee →
      ∃ fee, fee ≤ X.maxFee ∧ (gasF (pos (k + 1))).toNat = (gasF (pos k)).toNat + fee := by
    intro k hk hb
    obtain ⟨fee, hfl, hfe⟩ := (RF k hk).gasOut
    refine ⟨fee, hfl, ?_⟩
    rw [pos_out k hk, hfe, ← pos_in k hk]
    conv => lhs; rw [← Fp.cast_toNat (gasF (pos k))]
    rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt]
    have : (k + 1) * (X.maxFee + 1) ≤ (act.length + 1) * (X.maxFee + 1) := Nat.mul_le_mul_right _ (by omega)
    have : k * X.maxFee + X.maxFee ≤ (k + 1) * (X.maxFee + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    omega
  have gasB : ∀ k, k ≤ rs.length → (gasF (pos k)).toNat ≤ S0 + k * X.maxFee := by
    intro k
    induction k with
    | zero =>
      intro _; rw [pos0]
      show (((S0 : Nat) : F)).toNat ≤ _
      rw [Fp.toNat_cast_of_lt hS0]; omega
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      obtain ⟨fee, hfl, he⟩ := step1 k (by omega) ih'
      rw [he, Nat.succ_mul]
      omega
  have gas0 : (gasF (pos 0)).toNat = S0 := by
    rw [pos0]; show (((S0 : Nat) : F)).toNat = _; exact Fp.toNat_cast_of_lt hS0
  have gasN : (gasF (pos rs.length)).toNat = Sf.toNat := by rw [posN]; rfl
  -- (B) the channel, with producer times shifted by `t0`
  let prodL := rs.map prod
  let consL := rs.map cons
  have hpTp : ∀ k (hk : k < rs.length), ∀ x ∈ prod rs[k], x.tp = t0 + k + 1 := by
    intro k hk x hx
    obtain ⟨h1, h2⟩ := (RF k hk).prodT x hx
    rw [lvlk k hk] at h2
    exact natEq h2 h1 (by omega)
  have hpermC : (init ++ prodL.flatten).Perm (fin ++ consL.flatten) := by
    have e1 : prodL.flatten = rs.flatMap prod := by simp [prodL, List.flatMap]
    have e2 : consL.flatten = rs.flatMap cons := by simp [consL, List.flatMap]
    rw [e1, e2]
    exact ((hrs.flatMap_right prod).append_left init).trans (hch.trans
      ((hrs.flatMap_right cons).symm.append_left fin))
  have tpBound : ∀ x ∈ fin ++ consL.flatten, x.tp ≤ t0 + rs.length := by
    intro x hx
    rcases List.mem_append.mp (hpermC.symm.subset hx) with h | h
    · have := hinitTp x h; omega
    · obtain ⟨j, hj, hxj⟩ := mem_flatten_iff.mp h
      simp only [prodL, List.length_map, List.getElem_map] at hj hxj
      rw [hpTp j hj x hxj]; omega
  have C : ChanOK init fin prodL consL (fun x => x.tp - t0) := by
    refine ⟨by simp [prodL, consL], hpermC, ?_, fun x hx => by have := hinitTp x hx; show x.tp - t0 = 0; omega, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hinit, nodup_flatten_of _ (fun j hj => by simpa [prodL] using (RF j (by simpa [prodL] using hj)).prodNd) ?_, ?_⟩
      · intro i j hi hj hij x hx hx'
        simp only [prodL, List.length_map, List.getElem_map] at hi hj hx hx'
        have := hpTp i hi x hx; have := hpTp j hj x hx'; omega
      · intro x hx y hy hxy
        subst hxy
        obtain ⟨j, hj, hxj⟩ := mem_flatten_iff.mp hy
        simp only [prodL, List.length_map, List.getElem_map] at hj hxj
        have := hpTp j hj x hxj; have := hinitTp x hx; omega
    · intro k hk x hx
      simp only [prodL, List.length_map, List.getElem_map] at hk hx
      have := hpTp k hk x hx; show x.tp - t0 = k + 1; omega
    · intro k hk x hx
      simp only [consL, List.length_map, List.getElem_map] at hk hx
      obtain ⟨m, hm, he⟩ := (RF k hk).consT x hx
      rw [lvlk k hk] at he
      have hb := tpBound x (List.mem_append_right _ (mem_flatten_iff.mpr ⟨k, by simpa [consL] using hk, by simpa [consL] using hx⟩))
      have := natEq he (by omega) (by omega)
      show x.tp - t0 < k + 1; omega
  -- (C) induction along the path; the state after `k` rows is related as long as it is not halted
  have IH : ∀ k (hk : k ≤ rs.length), (k < rs.length ∨ st = 0) →
      ∃ s q pc sb cid, NearSpecV3.Wasm.seg X.cfg X.p k s0 = .cont s ∧
      pos k = stMsg (X.offOf q + pc) (t0 + k + 1) (gasF (pos k)).toNat 0 sb cid ∧
      Rel X s (t0 + k + 1) q pc (gasF (pos k)).toNat sb cid (live init prodL consL k)
        (sg (t0 + k + 1)).1 (sg (t0 + k + 1)).2 ∧ Q s (live init prodL consL k) := by
    intro k
    induction k with
    | zero =>
      intro _ _
      have e0 : (· ∈ init) = live init prodL consL 0 := by funext x; simp [live, prodBefore, consBefore]
      refine ⟨s0, k0, pc0, sb0, cid0, rfl, ?_, ?_, ?_⟩
      · rw [gas0, pos0]
      · rw [gas0]
        exact R0.congr_live e0
      · rw [← e0]; exact hQ0
    | succ k ih =>
      intro hk hcase
      obtain ⟨s, q, pc, sb, cid, hrun, hin, ⟨E, f, tps, tpl, rfl, rfl, rfl, R⟩, hQk⟩ := ih (by omega) (Or.inl (by omega))
      have gb := gasB k (by omega)
      have hm : (k + 1) * (X.maxFee + 1) ≤ (act.length + 1) * (X.maxFee + 1) := Nat.mul_le_mul_right _ (by omega)
      have hS : (gasF (pos k)).toNat + X.maxFee < ZkFormal.Algebra.P := by
        have : k * X.maxFee + X.maxFee ≤ (k + 1) * (X.maxFee + 1) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
        omega
      have hlive : ∀ x ∈ cons rs[k], live init prodL consL k x := fun x hx =>
        C.consumed_live (k := k) (by simp [consL]; omega) (by simpa [consL] using hx)
      obtain ⟨k', pc', fee, hb, sb', cid', hfl, hbl, hout, hspec⟩ :=
        (RFS k (by omega)).spec E s f tps tpl (t0 + k + 1) pc _
          (live init prodL consL k) R (by rw [← pos_in k (by omega)]; exact hin) hlive (by omega) hS hg64
      have hout' : pos (k + 1) = stMsg (X.offOf k' + pc') (t0 + k + 1 + 1) ((gasF (pos k)).toNat + fee) hb sb' cid' := by
        rw [pos_out k (by omega), hout]
      have hg1 : (gasF (pos (k + 1))).toNat = (gasF (pos k)).toNat + fee := by
        rw [hout']; simp only [gasF, stMsg, List.getD_cons_succ, List.getD_cons_zero]
        exact Fp.toNat_cast_of_lt (by simp only [gasF] at hS; omega)
      have hgas' : X.R * ((gasF (pos k)).toNat + fee - (sg (t0 + k + 1)).1) ≤ (sg (t0 + k + 1)).2 := by
        have hm := hstepgas (t0 + k + 1) ((gasF (pos k)).toNat) s.gas.g R.gas
        have hle : (gasF (pos k)).toNat + fee - (sg (t0 + k + 1)).1 ≤
            (gasF (pos k)).toNat + X.maxFee - (sg (t0 + k + 1)).1 := by
          have := hfl; omega
        exact Nat.le_trans (Nat.mul_le_mul_left _ hle) hm
      have hb0 : hb = 0 := by
        have h3 : (pos (k + 1)).getD 3 0 = 0 := by
          by_cases hc : k + 1 < rs.length
          · rw [pos_in (k + 1) hc]; exact (RF (k + 1) hc).halt0
          · have : k + 1 = rs.length := by omega
            have hc' : st = 0 := hcase.resolve_left hc
            rw [this, posN, hc']; rfl
        rw [hout'] at h3
        simp only [stMsg, List.getD_cons_succ, List.getD_cons_zero] at h3
        exact natEq (h3.trans rfl) (by omega) (by decide)
      obtain ⟨s', hs', E', f', tps', tpl', hsb', hcid', hk', R'⟩ := (hspec hgas').1 hb0
      have eS : stepLive (live init prodL consL k) (cons rs[k]) (prod rs[k]) = live init prodL consL (k + 1) := by
        funext x
        have := (C.live_succ (k := k) (by simp [consL]; omega) x).symm
        simp only [consL, prodL, List.getElem_map] at this
        exact propext this
      refine ⟨s', k', pc', sb', cid', seg_succ_cont hrun hs', ?_, ?_, ?_⟩
      · rw [hg1, hout', hb0, show t0 + (k + 1) + 1 = t0 + k + 1 + 1 by omega]
      · rw [hg1, show t0 + (k + 1) + 1 = t0 + k + 1 + 1 by omega, ← hsb', ← hcid', ← hk']
        exact Rel_of_RelW_congr R' eS
      · rw [← eS]
        exact hQ rs[k] (hmem k (by omega)) E s f tps tpl (t0 + k + 1) pc _ (live init prodL consL k) _ _ s' R
          (by rw [← pos_in k (by omega)]; exact hin) hlive hs' hQk
  refine ⟨hN, fun h0 => ?_⟩
  -- (D0) a cut: the state after the last row is related to the final boundary
  · obtain ⟨s, q, pc, sb, cid, hrun, hin, R, hQs⟩ := IH rs.length (Nat.le_refl _) (Or.inr h0)
    rw [hlenrs] at hrun
    have eF : live init prodL consL rs.length = (· ∈ fin) := by
      funext x
      have := C.live_final x
      simp only [consL, List.length_map] at this
      exact propext this
    refine ⟨s, hrun, run_of_seg_cont hrun, ⟨q, pc, sb, cid, ?_, ?_⟩, by rw [← eF]; exact hQs⟩
    · subst h0; rw [← posN, hin, gasN, hlenrs]
    · rw [← gasN, ← hlenrs]
      refine R.congr_live ?_
      funext x
      have := C.live_final x
      simp only [consL, List.length_map] at this
      exact propext this
end

/-! ## 8. The register and space clauses through a segment -/

/-- A row that, from any related state, leaves the register file unchanged (the spec fact for
every non-host instruction: `step_registers`). -/
def RegKeep (X : Ctx) (inS : List F) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat)
    (s' : St), RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    step X.cfg X.p s = .cont s' → s'.registers = s.registers

/-- **The host row's register contract (named rely, M6).**  The host function is opaque (its effect
on the register file is the host chip's business): a HOST row's consumed/produced space-6
messages track the host function's register effect.  This is exactly `RowQ` for the register
clause, stated per HOST row; it is a hypothesis of the segment theorem, to be discharged by the
host-chip contract (as `HostStepRely` is for the stack and heap). -/
def HostRegRely (X : Ctx) (inS : List F) (cons prod : List Msg) : Prop :=
  RowQ X (fun s live => RegC live s) inS cons prod

/-- **A non-host row keeps the register clause**: it neither consumes nor produces a space-6
message and the step leaves the register file unchanged. -/
theorem rowQ_reg_keep {X : Ctx} {inS : List F} {cons prod : List Msg}
    (hc : ∀ x ∈ cons, x.space ≠ 6) (hp : ∀ x ∈ prod, x.space ≠ 6) (hk : RegKeep X inS) :
    RowQ X (fun s live => RegC live s) inS cons prod := by
  intro E s f tps tpl t pc S live a b s' R hin _ hs ⟨tpr, hr⟩
  refine ⟨tpr, fun x hx => ?_⟩
  have h6 : x.space = 6 := hx
  rw [hk E s f tps tpl t pc S live a b s' R hin hs, ← hr x hx]
  simp only [stepLive]
  constructor
  · rintro (⟨h, -⟩ | h)
    · exact h
    · exact absurd h6 (hp x h)
  · intro h; exact Or.inl ⟨h, fun h' => hc x h' h6⟩

/-- **The space clause** is kept by a row whose produced messages are in allowed spaces (from any
related state: a locals row's space `16 + cid` is in range because `RelW` bounds `cid`). -/
theorem rowQ_space {X : Ctx} {inS : List F} {cons prod : List Msg}
    (h : ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat),
      RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
      ∀ x ∈ prod, SpaceOK x) :
    RowQ X (fun _ live => SpC live) inS cons prod := by
  intro E s f tps tpl t pc S live a b s' R hin _ _ hQ x hx
  rcases hx with ⟨hx, -⟩ | hx
  · exact hQ x hx
  · exact h E s f tps tpl t pc S live a b R hin x hx

theorem rowQ_and {X : Ctx} {Q1 Q2 : St → (Msg → Prop) → Prop} {inS : List F} {cons prod : List Msg}
    (h1 : RowQ X Q1 inS cons prod) (h2 : RowQ X Q2 inS cons prod) :
    RowQ X (fun s live => Q1 s live ∧ Q2 s live) inS cons prod := by
  intro E s f tps tpl t pc S live a b s' R hin hl hs ⟨q1, q2⟩
  exact ⟨h1 E s f tps tpl t pc S live a b s' R hin hl hs q1, h2 E s f tps tpl t pc S live a b s' R hin hl hs q2⟩

/-- **The extended boundary relation through a cut segment.**  `exec_of_rows_cut`'s hypotheses,
the extended relation `BndC` at the start, and per row: the space clause (`rowQ_space`) and the
register clause (`rowQ_reg_keep` for a non-host row, `HostRegRely` for a HOST row).  At a cut the
final state is related by `BndC` to the final live list. -/
theorem exec_of_rows_cutC (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
    (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)
    (sg : Nat → Nat × Nat) (st : Nat) (hst2 : st ≤ 2)
    (hrows : ∀ r ∈ act, RowFactsSegMap X (inS r) (outS r) (cons r) (prod r) sg)
    (t0 S0 : Nat) (m0 : List F) (sbf cidf : F)
    (hst : (m0 :: act.map outS).Perm ([pcf, N, Sf, (st : F), sbf, cidf] :: act.map inS))
    (hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp ≤ t0)
    (ht : t0 + act.length + 1 + (2 ^ 30 + 2 ^ 16) < ZkFormal.Algebra.P)
    (hfee : S0 + (act.length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    (hreg : ∀ r ∈ act, RowQ X (fun s live => RegC live s) (inS r) (cons r) (prod r))
    (hsp : ∀ r ∈ act, RowQ X (fun _ live => SpC live) (inS r) (cons r) (prod r))
    {s0 : St} (h0 : BndC X sg s0 t0 S0 m0 init) (hcut : st = 0) :
    ∃ sN, NearSpecV3.Wasm.seg X.cfg X.p act.length s0 = .cont sN ∧
      (∀ m, run X.cfg X.p (act.length + m) s0 = run X.cfg X.p m sN) ∧
      BndC X sg sN (t0 + act.length) Sf.toNat [pcf, N, Sf, ((0 : Nat) : F), sbf, cidf] fin := by
  obtain ⟨h0b, h0r, h0s⟩ := h0
  obtain ⟨-, hc⟩ := exec_of_rows_cutQ X act inS outS cons prod init fin pcf N Sf sg st hst2 hrows t0 S0 m0
    sbf cidf hst hch hinit hinitTp ht hfee hstepgas hg64 h0b (fun s live => RegC live s ∧ SpC live)
    (fun r hr => rowQ_and (hreg r hr) (hsp r hr)) ⟨h0r, h0s⟩
  obtain ⟨sN, h1, h2, h3, h4, h5⟩ := hc hcut
  exact ⟨sN, h1, h2, h3, h4, h5⟩

end WasmBase
