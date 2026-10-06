import ZkFormal.NearV3.Render.Node.Layout
import ZkFormal.Near.Link.NodeSer

/-!
# ZkFormal.NearV3.Render.Node.Seq — consecutive rows of the honest `nodeV3` table

As v1 `Near/Render/Proof/NodeSeq.lean`: the field successions (`SuccOk`,
`chain_fields`), layout adjacency (`lay_adj`), first/last positions, and the
row decomposition (`off`, `row_node`, `next_row`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra NearSpec
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
open ZkFormal.Near.Render.NodeSeq (Ch ch_tail nef layout_cons layout_head layout_adj ch_mid)

namespace NodeGen3

/-! ## Field successions -/

def nxt (v : NodeV3) : F → F → Prop
  | .tag, g => g.state = (match v with
      | .leaf .. => 15 | .ext .. => 15
      | .branch none .. => 20 | .branch (some _) .. => 18)
  | .hpl, g => g.state = 16
  | .hpf, g => g.state = (if nokeyOf v = 1 then (if isLeaf v then 18 else 21) else 17)
  | .key, g => g.state = (if isLeaf v then 18 else 21)
  | .vlen, g => g.state = 19
  | .vh _, g => g.state = (if isLeaf v then 22 else 20)
  | .bm, g => g.state = (if nochildOf v = 1 then 22 else 21)
  | .ch w, g => (g.state = 22 ∧ w.lastw = true) ∨
      (g.state = 21 ∧ w.lastw = false ∧ ∀ w', g.chw = some w' → w'.w = w.w + 1)
  | .mem, _ => False

def SuccOk (v : NodeV3) (f g : F) : Prop :=
  g.state ≠ 14 ∧ (f.state ≠ 21 → ∀ w', g.chw = some w' → w'.w = 0) ∧ nxt v f g

/-- Number of present children. -/
def popK (kids : List NKid) : Nat := (kids.filter (· ≠ .none)).length

def winsOf (L : Nat) (P : List (NKid × Nat)) (w0 : Nat) : List F :=
  (P.zip (List.range' w0 P.length)).map fun ((k, j), w) => .ch (kidWin k w (w + 1 = L) (some j))

theorem winsOf_cons (L : Nat) (x : NKid × Nat) (P : List (NKid × Nat)) (w0 : Nat) :
    winsOf L (x :: P) w0 = .ch (kidWin x.1 w0 (w0 + 1 = L) (some x.2)) :: winsOf L P (w0 + 1) := by
  simp [winsOf, List.range'_succ]

def presentOf (kids : List NKid) : List (NKid × Nat) :=
  (kids.zip (List.range kids.length)).filter fun (k, _) => k ≠ .none

theorem branchWins_eq (kids : List NKid) : branchWins kids = winsOf (presentOf kids).length (presentOf kids) 0 := by
  unfold branchWins winsOf presentOf; simp only [List.range_eq_range']

theorem popK_eq (kids : List NKid) : (presentOf kids).length = popK kids := by
  unfold presentOf
  have : ∀ (Q : List NKid) (s : Nat), ((Q.zip (List.range' s Q.length)).filter fun (k, _) => k ≠ .none).length =
      (Q.filter (· ≠ .none)).length := by
    intro Q; induction Q with
    | nil => intro s; rfl
    | cons q Q ih =>
      intro s
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filter_cons]
      split <;> simp_all
  rw [List.range_eq_range']; exact this kids 0

theorem wins_chain (v : NodeV3) (L : Nat) : ∀ (P : List (NKid × Nat)) (w0 : Nat),
    w0 + P.length = L → P ≠ [] → Ch (SuccOk v) (winsOf L P w0 ++ [.mem])
  | [], _, _, h => absurd rfl h
  | [x], w0, hL, _ => by
    simp only [List.length_singleton] at hL
    rw [winsOf_cons]
    simp only [winsOf, List.zip_nil_left, List.map_nil, List.cons_append, List.nil_append, Ch, and_true]
    refine ⟨by decide, fun _ w' h => (by cases h), ?_⟩
    simp only [nxt]
    left; cases x.1 <;> simp [kidWin, F.state, Node.sMEM] <;> omega
  | x :: y :: Q, w0, hL, _ => by
    have ih := wins_chain v L (y :: Q) (w0 + 1) (by simp at hL ⊢; omega) (by simp)
    rw [winsOf_cons, winsOf_cons] at *
    simp only [List.cons_append] at ih ⊢
    refine ⟨?_, ih⟩
    simp only [List.length_cons] at hL
    refine ⟨by simp [F.state, Node.sCH], fun h => absurd (by cases x.1 <;> rfl) h, ?_⟩
    simp only [nxt]
    right
    refine ⟨rfl, ?_, ?_⟩
    · cases x.1 <;> simp [kidWin] <;> omega
    · intro w' hw'; simp only [NodeGen.F.chw, Option.some.injEq] at hw'; subst hw'
      cases x.1 <;> cases y.1 <;> rfl

/-! ### Bitmaps -/

def kbit (k : NKid) : Nat := if k ≠ .none then 1 else 0

theorem kidBit_toRec (k : NKid) : kidBit k.toRec = kbit k := by cases k <;> rfl

theorem bitOf_kidBitmap (kids : List NKid) (j : Nat) : bitOf (kidBitmap kids) j = kbit (kids.getD j .none) := by
  rw [Link.kidBitmap_eq, NodeSeq.bitOf_bitmap]
  rw [show (kids.map NKid.toRec).getD j .none = (kids.getD j .none).toRec by
    simp [List.getD_eq_getElem?_getD]; cases kids[j]? <;> rfl]
  exact kidBit_toRec _

theorem sum_kbit : ∀ (l : List NKid) (m : Nat), l.length ≤ m →
    ((List.range m).map fun i => kbit (l.getD i .none)).sum = popK l
  | [], m, _ => by
    simp only [List.getD_nil, popK, List.filter_nil, List.length_nil]
    induction m with
    | zero => rfl
    | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih (by simp)]; rfl
  | k :: l, m + 1, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have := sum_kbit l m (by simp at h; omega)
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, this, popK, List.filter_cons]
    unfold kbit; split <;> simp_all <;> omega
  | _ :: _, 0, h => by simp at h

theorem popOf_branch (sv : Option NSlot3) (kids : List NKid) (m : List Nat) (h : kids.length = 16) :
    popOf (.branch sv kids m) = popK kids := by
  show (List.range 16).foldl (fun a i => a + bitOf (bmvOf (.branch sv kids m)) i) 0 = _
  rw [NodeSeq.foldl_sum (fun i => bitOf (bmvOf (.branch sv kids m)) i), Nat.zero_add]
  simp only [bmvOf, isLE, kidsOf, if_false, Bool.false_eq_true, bitOf_kidBitmap]
  exact sum_kbit kids 16 (by omega)

/-! ### The fields chain -/

theorem chain_wins (v : NodeV3) (kids : List NKid) (hpop : nochildOf v = b2n (popK kids = 0)) :
    ∀ (l1 : List F), Ch (SuccOk v) (l1 ++ [F.bm]) → Ch (SuccOk v) (l1 ++ F.bm :: (branchWins kids ++ [F.mem])) := by
  intro l1 h1
  rw [branchWins_eq]
  rw [← popK_eq] at hpop
  generalize presentOf kids = P at hpop ⊢
  cases P with
  | nil =>
    simp only [winsOf, List.zip_nil_left, List.map_nil, List.nil_append]
    refine ch_mid l1 _ _ [] h1 ?_ trivial
    refine ⟨by decide, fun _ w' h => (by cases h), ?_⟩
    simp only [nxt, hpop, List.length_nil, b2n]; rfl
  | cons x P =>
    rw [winsOf_cons, List.cons_append]
    refine ch_mid l1 _ _ _ h1 ?_ ?_
    · refine ⟨by simp [F.state, Node.sCH], fun _ w' h => ?_, ?_⟩
      · simp only [NodeGen.F.chw, Option.some.injEq] at h; subst h; cases x.1 <;> rfl
      · simp only [nxt, hpop, List.length_cons, b2n, Nat.add_one_ne_zero, decide_false, ite_false]
        rfl
    · have := wins_chain v (x :: P).length (x :: P) 0 (by simp) (by simp)
      rw [winsOf_cons, List.cons_append] at this
      exact this

theorem ok_of {v : NodeV3} {f g : F} (h1 : g.state ≠ 14) (h2 : f.state ≠ 21) (h3 : g.chw = none)
    (h4 : nxt v f g) : SuccOk v f g :=
  ⟨h1, fun _ w' h => (by rw [h3] at h; cases h), h4⟩

macro "st_ne" : tactic => `(tactic| simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN,
  Node.sVH, Node.sBM, Node.sCH, Node.sMEM])

/-- **The non-empty fields of a record chain by `SuccOk`.** -/
theorem chain_fields (v : NodeV3) (hw : v.wf) : Ch (SuccOk v) (nef (hplenOf v) (fieldsOf v)) := by
  cases v with
  | leaf k sv m =>
    have e : nef (hplenOf (.leaf k sv m)) (fieldsOf (.leaf k sv m)) =
        [F.tag, .hpl, .hpf] ++ (if k.length / 2 = 0 then [] else [.key]) ++ [.vlen, .vh (valWin sv), .mem] := by
      by_cases hk : k.length / 2 = 0 <;>
        simp [nef, fieldsOf, List.filter_cons, hk, F.len, hplenOf, isLE, keyOf] <;> omega
    have hnk : nokeyOf (.leaf k sv m) = b2n (k.length / 2 = 0) := by
      simp only [nokeyOf, isLE, hplenOf, keyOf, b2n, Bool.true_and, if_true]
      by_cases h : k.length / 2 = 0 <;> simp [h]
    rw [e]
    split
    · rename_i hk
      exact ⟨ok_of (by st_ne) (by st_ne) rfl rfl, ok_of (by st_ne) (by st_ne) rfl rfl,
        ok_of (by st_ne) (by st_ne) rfl (by simp [nxt, hnk, hk, b2n, isLeaf]; rfl),
        ok_of (by st_ne) (by st_ne) rfl rfl, ok_of (by st_ne) (by st_ne) rfl rfl, trivial⟩
    · rename_i hk
      exact ⟨ok_of (by st_ne) (by st_ne) rfl rfl, ok_of (by st_ne) (by st_ne) rfl rfl,
        ok_of (by st_ne) (by st_ne) rfl (by simp [nxt, hnk, hk, b2n]; rfl),
        ok_of (by st_ne) (by st_ne) rfl (by simp [nxt, isLeaf]; rfl),
        ok_of (by st_ne) (by st_ne) rfl rfl, ok_of (by st_ne) (by st_ne) rfl rfl, trivial⟩
  | ext k kid m =>
    have e : nef (hplenOf (.ext k kid m)) (fieldsOf (.ext k kid m)) =
        [F.tag, .hpl, .hpf] ++ (if k.length / 2 = 0 then [] else [.key]) ++ [.ch (kidWin kid 0 true none), .mem] := by
      by_cases hk : k.length / 2 = 0 <;>
        simp [nef, fieldsOf, List.filter_cons, hk, F.len, hplenOf, isLE, keyOf] <;> omega
    have hnk : nokeyOf (.ext k kid m) = b2n (k.length / 2 = 0) := by
      simp only [nokeyOf, isLE, hplenOf, keyOf, b2n, Bool.true_and, if_true]
      by_cases h : k.length / 2 = 0 <;> simp [h]
    have hch : ∀ f, f.state ≠ 21 → nxt (.ext k kid m) f (.ch (kidWin kid 0 true none)) →
        SuccOk (.ext k kid m) f (.ch (kidWin kid 0 true none)) := by
      intro f hf h
      refine ⟨by simp [F.state, Node.sCH], fun _ w' hw => ?_, h⟩
      simp only [NodeGen.F.chw, Option.some.injEq] at hw; subst hw; cases kid <;> rfl
    have hlast : SuccOk (.ext k kid m) (.ch (kidWin kid 0 true none)) .mem :=
      ⟨by decide, fun _ w' h => (by cases h), .inl ⟨rfl, by cases kid <;> rfl⟩⟩
    rw [e]
    split
    · rename_i hk
      exact ⟨ok_of (by st_ne) (by st_ne) rfl rfl, ok_of (by st_ne) (by st_ne) rfl rfl,
        hch _ (by decide) (by simp [nxt, hnk, hk, b2n, isLeaf]; rfl), hlast, trivial⟩
    · rename_i hk
      exact ⟨ok_of (by st_ne) (by st_ne) rfl rfl, ok_of (by st_ne) (by st_ne) rfl rfl,
        ok_of (by st_ne) (by st_ne) rfl (by simp [nxt, hnk, hk, b2n]; rfl),
        hch _ (by decide) (by simp [nxt, isLeaf]; rfl), hlast, trivial⟩
  | branch sv kids m =>
    have hl : kids.length = 16 := hw.1
    have hpop : nochildOf (.branch sv kids m) = b2n (popK kids = 0) := by
      simp only [nochildOf, isLE, popOf_branch sv kids m hl]; simp [b2n]
    have hnef : nef (hplenOf (.branch sv kids m)) (branchWins kids ++ [F.mem]) = branchWins kids ++ [F.mem] := by
      rw [List.filter_eq_self]; intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_branchWins hf; simp [F.len]
      · simp at hf; subst hf; simp [F.len]
    cases sv with
    | none =>
      have e : fieldsOf (.branch none kids m) = [F.tag, F.bm] ++ (branchWins kids ++ [F.mem]) := by
        simp [fieldsOf]
      rw [e, nef, List.filter_append, show List.filter (fun f => F.len _ f != 0) (branchWins kids ++ [F.mem]) = _ from hnef]
      exact chain_wins _ kids hpop [F.tag] ⟨⟨by decide, fun _ w' h => (by cases h), rfl⟩, trivial⟩
    | some s =>
      have e : fieldsOf (.branch (some s) kids m) =
          [F.tag, F.vlen, F.vh (valWin s), F.bm] ++ (branchWins kids ++ [F.mem]) := by
        simp [fieldsOf]
      rw [e, nef, List.filter_append, show List.filter (fun f => F.len _ f != 0) (branchWins kids ++ [F.mem]) = _ from hnef]
      exact chain_wins _ kids hpop [F.tag, F.vlen, F.vh (valWin s)]
        ⟨⟨by decide, fun _ w' h => (by cases h), rfl⟩,
          ⟨⟨by simp [F.state, Node.sVH], fun _ w' h => (by cases h), rfl⟩,
          ⟨⟨by decide, fun _ w' h => (by cases h), by simp [nxt, isLeaf]; rfl⟩, trivial⟩⟩⟩

/-! ## Positions of one record -/

theorem fields_last (v : NodeV3) : ∃ X, fieldsOf v = X ++ [F.mem] := by
  cases v with
  | leaf k sv m => exact ⟨[F.tag, .hpl, .hpf, .key, .vlen, .vh (valWin sv)], rfl⟩
  | ext k kid m => exact ⟨[F.tag, .hpl, .hpf, .key, .ch (kidWin kid 0 true none)], rfl⟩
  | branch sv kids m => cases sv with
    | none => exact ⟨[F.tag, F.bm] ++ branchWins kids, by simp [fieldsOf]⟩
    | some s => exact ⟨[F.tag, F.vlen, F.vh (valWin s), F.bm] ++ branchWins kids, by simp [fieldsOf]⟩

theorem fields_first (v : NodeV3) : ∃ X, fieldsOf v = F.tag :: X ∧ ∀ f ∈ X, f.isTag = false := by
  have hb : ∀ f ∈ branchWins (kidsOf v), f.isTag = false := by
    intro f hf; obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_branchWins hf; rfl
  cases v with
  | leaf k sv m =>
    refine ⟨_, rfl, fun f hf => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  | ext k kid m =>
    refine ⟨_, rfl, fun f hf => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> rfl
  | branch sv kids m =>
    cases sv with
    | none =>
      refine ⟨F.bm :: (branchWins kids ++ [F.mem]), by simp [fieldsOf], ?_⟩
      intro f hf
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | hf | rfl
      · rfl
      · exact hb f hf
      · rfl
    | some s =>
      refine ⟨F.vlen :: F.vh (valWin s) :: F.bm :: (branchWins kids ++ [F.mem]), by simp [fieldsOf], ?_⟩
      intro f hf
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | hf | rfl
      · rfl
      · rfl
      · rfl
      · exact hb f hf
      · rfl

theorem lay_mem (v : NodeV3) : ∀ x ∈ layout (fieldsOf v) (hplenOf v), x.1 ∈ fieldsOf v := by
  intro x hx
  simp only [layout, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨f, hf, i, _, rfl⟩ := hx
  exact hf

theorem lay_idx (v : NodeV3) {p : Nat} (hp : p < (layout (fieldsOf v) (hplenOf v)).length) :
    ((layout (fieldsOf v) (hplenOf v)).getD p default).2 < ((layout (fieldsOf v) (hplenOf v)).getD p default).1.len (hplenOf v) := by
  have hm : (layout (fieldsOf v) (hplenOf v)).getD p default ∈ layout (fieldsOf v) (hplenOf v) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]; exact List.getElem_mem _
  generalize (layout (fieldsOf v) (hplenOf v)).getD p default = x at hm
  simp only [layout, List.mem_flatMap, List.mem_map, List.mem_range] at hm
  obtain ⟨f, _, i, hi, rfl⟩ := hm
  exact hi

theorem lay_pos (v : NodeV3) : 0 < (layout (fieldsOf v) (hplenOf v)).length := by
  obtain ⟨X, hX⟩ := fields_first v
  rw [hX.1, layout_cons]; simp [F.len]

theorem lay_tag (v : NodeV3) (p : Nat) (hp : p < (layout (fieldsOf v) (hplenOf v)).length) :
    ((layout (fieldsOf v) (hplenOf v)).getD p default).1.isTag = true ↔ p = 0 := by
  obtain ⟨X, hX, hX2⟩ := fields_first v
  rw [hX] at hp ⊢
  rw [layout_cons] at hp ⊢
  simp only [F.len, List.range_one, List.map_cons, List.map_nil, List.singleton_append, List.length_cons] at hp ⊢
  cases p with
  | zero => simp [NodeGen.F.isTag]
  | succ p =>
    simp only [List.getD_cons_succ, Nat.add_one_ne_zero, iff_false, Bool.not_eq_true]
    have hm : (layout X (hplenOf v)).getD p default ∈ layout X (hplenOf v) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
    generalize (layout X (hplenOf v)).getD p default = x at hm
    simp only [layout, List.mem_flatMap, List.mem_map, List.mem_range] at hm
    obtain ⟨f, hf, i, _, rfl⟩ := hm
    exact hX2 f hf

theorem lay_last (v : NodeV3) :
    ((layout (fieldsOf v) (hplenOf v)).getD ((layout (fieldsOf v) (hplenOf v)).length - 1) default) = (F.mem, 7) := by
  obtain ⟨X, hX⟩ := fields_last v
  have : layout (fieldsOf v) (hplenOf v) = layout X (hplenOf v) ++ (List.range 8).map (F.mem, ·) := by
    simp only [hX, layout, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, F.len]
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

section
variable {v : NodeV3} (hw : v.wf)
include hw

theorem lay_adj {p : Nat} (hp : p + 1 < (layout (fieldsOf v) (hplenOf v)).length) :
    let a := (layout (fieldsOf v) (hplenOf v)).getD p default
    let b := (layout (fieldsOf v) (hplenOf v)).getD (p + 1) default
    (b.1 = a.1 ∧ b.2 = a.2 + 1 ∧ a.2 + 1 < a.1.len (hplenOf v)) ∨
      (a.2 + 1 = a.1.len (hplenOf v) ∧ b.2 = 0 ∧ SuccOk v a.1 b.1) :=
  layout_adj _ _ _ (chain_fields v hw) p hp

theorem lay_last_iff {p : Nat} (hp : p < (layout (fieldsOf v) (hplenOf v)).length) :
    p + 1 = (layout (fieldsOf v) (hplenOf v)).length ↔
      (((layout (fieldsOf v) (hplenOf v)).getD p default).1.state = 22 ∧
        ((layout (fieldsOf v) (hplenOf v)).getD p default).2 = 7) := by
  constructor
  · intro h; rw [show p = (layout (fieldsOf v) (hplenOf v)).length - 1 by omega, lay_last]; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩
    apply Classical.byContradiction; intro hne
    have hadj := lay_adj hw (p := p) (by omega)
    have hm : ((layout (fieldsOf v) (hplenOf v)).getD p default).1 = .mem := by
      revert h1; generalize ((layout (fieldsOf v) (hplenOf v)).getD p default).1 = f
      cases f <;> simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM,
        Node.sCH, Node.sMEM]
    simp only [hm, h2] at hadj
    rcases hadj with ⟨_, _, h3⟩ | ⟨_, _, h3⟩
    · simp [F.len] at h3
    · exact h3.2.2

end

/-! ## Rows of the table -/

/-- First row of record `n`. -/
def off (vs : List NodeS3) : Nat → Nat
  | 0 => 0
  | n + 1 => off vs n + (layN vs n).length

theorem off_mono (vs : List NodeS3) {a b : Nat} (h : a ≤ b) : off vs a ≤ off vs b := by
  induction b with
  | zero => rw [show a = 0 by omega]; exact Nat.le_refl _
  | succ b ih =>
    by_cases h' : a = b + 1
    · rw [h']; exact Nat.le_refl _
    · have := ih (by omega); simp only [off]; omega

theorem nodeRecs_len (vs : List NodeS3) (n : Nat) : (nodeRecs vs n).length = (layN vs n).length := by
  simp [nodeRecs]

theorem recs_len' (vs : List NodeS3) (N : Nat) : ((List.range N).flatMap (nodeRecs vs)).length = off vs N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [off, nodeRecs_len]

theorem recs_get' (vs : List NodeS3) (N : Nat) {n p : Nat} (hn : n < N) (hp : p < (layN vs n).length) :
    ((List.range N).flatMap (nodeRecs vs)).getD (off vs n + p) default = mkR vs n p := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.getD_eq_getElem?_getD]
    by_cases h : n < N
    · have hl : off vs n + p < ((List.range N).flatMap (nodeRecs vs)).length := by
        rw [recs_len']
        have := off_mono vs (show n + 1 ≤ N by omega)
        simp only [off] at this; omega
      rw [List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD, ih h]
    · have hnN : n = N := by omega
      subst hnN
      rw [List.getElem?_append_right (by rw [recs_len']; omega), recs_len']
      simp [List.getD_eq_getElem?_getD, nodeRecs, hp]

theorem recs_cover' (vs : List NodeS3) (N : Nat) {q : Nat} (hq : q < off vs N) :
    ∃ n p, n < N ∧ p < (layN vs n).length ∧ q = off vs n + p := by
  induction N with
  | zero => simp [off] at hq
  | succ N ih =>
    by_cases h : q < off vs N
    · obtain ⟨n, p, h1, h2, h3⟩ := ih h; exact ⟨n, p, by omega, h2, h3⟩
    · simp only [off] at hq; exact ⟨N, q - off vs N, by omega, by omega, by omega⟩

theorem R_off (vs : List NodeS3) : R vs = off vs vs.length := by
  simp only [R, recsOf, recs_len']

theorem off_pos {vs : List NodeS3} {n : Nat} (h : 0 < n) : 0 < off vs n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := lay_pos (rec vs m).v
  simp only [off, layN]; omega

theorem recs_getD (vs : List NodeS3) {n p : Nat} (hn : n < vs.length) (hp : p < (layN vs n).length) :
    (recsOf vs).getD (off vs n + p) default = mkR vs n p := by
  rw [recsOf, recs_get' _ _ hn hp]

/-- A node row: record `n`, position `p`. -/
theorem row_node {vs : List NodeS3} {q : Nat} (hq : q < R vs) :
    ∃ n p, n < vs.length ∧ p < (layN vs n).length ∧
      (recsOf vs).getD q default = mkR vs n p ∧ q = off vs n + p := by
  rw [R_off] at hq
  obtain ⟨n, p, h1, h2, h3⟩ := recs_cover' _ _ hq
  exact ⟨n, p, h1, h2, by rw [h3, recs_getD vs h1 h2], h3⟩

theorem first_row {vs : List NodeS3} {n p : Nat} : off vs n + p = 0 ↔ n = 0 ∧ p = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · subst hn; simp [off] at h; exact ⟨rfl, h⟩
    · have := off_pos (vs := vs) (Nat.pos_of_ne_zero hn); omega
  · rintro ⟨rfl, rfl⟩; rfl

/-- The row after node row `(n, p)`. -/
theorem next_row {vs : List NodeS3} {n p : Nat} (hn : n < vs.length) (hp : p < (layN vs n).length) :
    (p + 1 < (layN vs n).length ∧ off vs n + p + 1 < R vs ∧
      (recsOf vs).getD (off vs n + p + 1) default = mkR vs n (p + 1)) ∨
    (p + 1 = (layN vs n).length ∧ n + 1 < vs.length ∧ off vs n + p + 1 < R vs ∧
      (recsOf vs).getD (off vs n + p + 1) default = mkR vs (n + 1) 0) ∨
    (p + 1 = (layN vs n).length ∧ n + 1 = vs.length ∧ off vs n + p + 1 = R vs) := by
  have hoff : off vs (n + 1) = off vs n + (layN vs n).length := rfl
  have hmono := off_mono vs (show n + 1 ≤ vs.length by omega)
  rw [R_off]
  by_cases h1 : p + 1 < (layN vs n).length
  · left
    refine ⟨h1, by omega, ?_⟩
    rw [Nat.add_assoc, recs_getD vs hn h1]
  · right
    by_cases h2 : n + 1 < vs.length
    · left
      have hl1 := lay_pos (rec vs (n + 1)).v
      have hmono2 := off_mono vs (show n + 2 ≤ vs.length by omega)
      have hoff2 : off vs (n + 2) = off vs (n + 1) + (layN vs (n + 1)).length := rfl
      simp only [layN] at hoff2 hl1
      refine ⟨by omega, h2, by simp only [layN] at *; omega, ?_⟩
      rw [show off vs n + p + 1 = off vs (n + 1) + 0 by omega, recs_getD vs h2 (by simp only [layN]; omega)]
    · right
      refine ⟨by omega, by omega, ?_⟩
      rw [show vs.length = n + 1 by omega, hoff]; omega

end NodeGen3

end ZkFormal.NearV3.Render
