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

end WasmBase
