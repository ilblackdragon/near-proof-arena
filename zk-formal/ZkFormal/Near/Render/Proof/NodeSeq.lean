import ZkFormal.Near.Render.Proof.NodeLocal0

/-!
# ZkFormal.Near.Render.Proof.NodeSeq — consecutive rows of the honest node table

* `layout_adj`: two consecutive positions of a layout are in the same field
  (index `+1`) or the first ends a field and the second starts the next
  non-empty field, related by any relation the non-empty fields chain by;
* `SuccOk nr f g`: the field successions the table enforces (next state, window
  index); `chain_fields`: the non-empty fields of every record chain by it;
* rows: positions `0` (`TAG`) and `len − 1` (last `MEM` byte);
* `recs_at`, `recs_next`: row `q` of the table is `mkR I n p` (`q = off n + p`),
  and row `q + 1` is the next position of the same node or the first row of
  node `n + 1`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeSeq
open NodeGen NodeCells NodeTr

/-! ## Layout adjacency -/

/-- `R` holds between consecutive elements. -/
def Ch {α : Type} (R : α → α → Prop) : List α → Prop
  | a :: b :: l => R a b ∧ Ch R (b :: l)
  | _ => True

theorem ch_tail {α : Type} {R : α → α → Prop} {a : α} {l : List α} (h : Ch R (a :: l)) : Ch R l := by
  cases l with
  | nil => trivial
  | cons b l => exact h.2

/-- The non-empty fields. -/
abbrev nef (h : Nat) (fs : List F) : List F := fs.filter fun f => f.len h != 0

theorem layout_cons (h : Nat) (f : F) (fs : List F) :
    layout (f :: fs) h = (List.range (f.len h)).map (f, ·) ++ layout fs h := by
  simp [layout]

theorem layout_head (h : Nat) : ∀ fs : List F, 0 < (layout fs h).length →
    ∃ g, (nef h fs).head? = some g ∧ (layout fs h).getD 0 default = (g, 0)
  | [], hl => by simp [layout] at hl
  | f :: fs, hl => by
    rw [layout_cons] at hl ⊢
    by_cases h0 : f.len h = 0
    · simp only [h0, List.range_zero, List.map_nil, List.nil_append] at hl ⊢
      obtain ⟨g, h1, h2⟩ := layout_head h fs (by simpa using hl)
      refine ⟨g, ?_, h2⟩
      simp [nef, List.filter_cons, h0] at h1 ⊢; exact h1
    · refine ⟨f, by simp [nef, List.filter_cons, h0], ?_⟩
      have hp : 0 < f.len h := Nat.pos_of_ne_zero h0
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hp)]
      simp [hp]

theorem layout_adj (h : Nat) (R : F → F → Prop) : ∀ (fs : List F), Ch R (nef h fs) →
    ∀ p, p + 1 < (layout fs h).length →
      (((layout fs h).getD (p + 1) default).1 = ((layout fs h).getD p default).1 ∧
        ((layout fs h).getD (p + 1) default).2 = ((layout fs h).getD p default).2 + 1 ∧
        ((layout fs h).getD p default).2 + 1 < ((layout fs h).getD p default).1.len h) ∨
      (((layout fs h).getD p default).2 + 1 = ((layout fs h).getD p default).1.len h ∧
        ((layout fs h).getD (p + 1) default).2 = 0 ∧
        R ((layout fs h).getD p default).1 ((layout fs h).getD (p + 1) default).1)
  | [], _, p, hp => by simp [layout] at hp
  | f :: fs, hc, p, hp => by
    rw [layout_cons] at hp ⊢
    by_cases h0 : f.len h = 0
    · simp only [h0, List.range_zero, List.map_nil, List.nil_append] at hp ⊢
      exact layout_adj h R fs (by simpa [nef, List.filter_cons, h0] using hc) p hp
    · have hc' : Ch R (f :: nef h fs) := by simpa [nef, List.filter_cons, h0] using hc
      have hL : ((List.range (f.len h)).map (f, ·)).length = f.len h := by simp
      simp only [List.length_append, hL] at hp
      have gA : ∀ i, i < f.len h → (((List.range (f.len h)).map (f, ·)) ++ layout fs h).getD i default = (f, i) := by
        intro i hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hL]; exact hi)]; simp [hi]
      have gB : ∀ i, (((List.range (f.len h)).map (f, ·)) ++ layout fs h).getD (f.len h + i) default =
          (layout fs h).getD i default := by
        intro i
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hL]; omega), hL,
          Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
      by_cases h1 : p + 1 < f.len h
      · left; rw [gA p (by omega), gA (p + 1) h1]; simp; omega
      by_cases h2 : p + 1 = f.len h
      · right
        obtain ⟨g, hg1, hg2⟩ := layout_head h fs (by omega)
        rw [gA p (by omega), show p + 1 = f.len h + 0 by omega, gB, hg2]
        refine ⟨by simp only; omega, rfl, ?_⟩
        cases hn : nef h fs with
        | nil => rw [hn] at hg1; cases hg1
        | cons g' l =>
          rw [hn] at hg1 hc'; cases hg1
          exact hc'.1
      · obtain ⟨i, rfl⟩ : ∃ i, p = f.len h + i := ⟨p - f.len h, by omega⟩
        rw [gB, show f.len h + i + 1 = f.len h + (i + 1) by omega, gB]
        exact layout_adj h R fs (ch_tail hc') i (by omega)

/-! ## Field successions -/

/-- The successor states of the fields (what `cFields`/`cWindows` enforce). -/
def nxt (nr : NodeRec) : F → F → Prop
  | .tag, g => g.state = (match nr with
      | .leaf .. => Node.sHPL | .ext .. => Node.sHPL
      | .branch none .. => Node.sBM | .branch (some _) .. => Node.sVLEN)
  | .hpl, g => g.state = Node.sHPF
  | .hpf, g => g.state = (if nokeyOf nr = 1 then (if NodeLay.leafB nr then Node.sVLEN else Node.sCH) else Node.sKEY)
  | .key, g => g.state = (if NodeLay.leafB nr then Node.sVLEN else Node.sCH)
  | .vlen, g => g.state = Node.sVH
  | .vh _, g => g.state = (if NodeLay.leafB nr then Node.sMEM else Node.sBM)
  | .bm, g => g.state = (if nochildOf nr = 1 then Node.sMEM else Node.sCH)
  | .ch w, g => (g.state = Node.sMEM ∧ w.lastw = true) ∨
      (g.state = Node.sCH ∧ w.lastw = false ∧ ∀ w', g.chw = some w' → w'.w = w.w + 1)
  | .mem, _ => False

def SuccOk (nr : NodeRec) (f g : F) : Prop :=
  g.state ≠ Node.sTAG ∧ (f.state ≠ Node.sCH → ∀ w', g.chw = some w' → w'.w = 0) ∧ nxt nr f g

/-! ### Branch windows -/

/-- Number of present children. -/
def popK (kids : List Kid) : Nat := (kids.filter (· ≠ .none)).length

/-- The windows of `P` (children with their slots), numbered from `w0`. -/
def winsOf (I : Info) (L : Nat) (P : List (Kid × Nat)) (w0 : Nat) : List F :=
  (P.zip (List.range' w0 P.length)).map fun ((k, j), w) => .ch (kidWin I k w (w + 1 = L) (some j))

theorem winsOf_cons (I : Info) (L : Nat) (x : Kid × Nat) (P : List (Kid × Nat)) (w0 : Nat) :
    winsOf I L (x :: P) w0 = .ch (kidWin I x.1 w0 (w0 + 1 = L) (some x.2)) :: winsOf I L P (w0 + 1) := by
  simp [winsOf, List.range'_succ]

/-- The present children with their slots. -/
def presentOf (kids : List Kid) : List (Kid × Nat) := (kids.zip (List.range kids.length)).filter fun (k, _) => k ≠ .none

theorem branchWins_eq (I : Info) (kids : List Kid) :
    branchWins I kids = winsOf I (presentOf kids).length (presentOf kids) 0 := by
  unfold branchWins winsOf presentOf; simp only [List.range_eq_range']

theorem popK_eq (kids : List Kid) : (presentOf kids).length = popK kids := by
  unfold presentOf
  have : ∀ (Q : List Kid) (s : Nat), ((Q.zip (List.range' s Q.length)).filter fun (k, _) => k ≠ .none).length =
      (Q.filter (· ≠ .none)).length := by
    intro Q; induction Q with
    | nil => intro s; rfl
    | cons q Q ih =>
      intro s
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filter_cons]
      split <;> simp_all
  rw [List.range_eq_range']; exact this kids 0

/-- The windows chain, and the last one is followed by `MEM`. -/
theorem wins_chain (I : Info) (nr : NodeRec) (L : Nat) : ∀ (P : List (Kid × Nat)) (w0 : Nat),
    w0 + P.length = L → P ≠ [] → Ch (SuccOk nr) (winsOf I L P w0 ++ [.mem])
  | [], _, _, h => absurd rfl h
  | [x], w0, hL, _ => by
    simp only [List.length_singleton] at hL
    rw [winsOf_cons]
    simp only [winsOf, List.zip_nil_left, List.map_nil, List.cons_append, List.nil_append, Ch, and_true]
    refine ⟨by decide, fun _ w' h => (by cases h), ?_⟩
    simp only [nxt]
    left; cases x.1 <;> simp [kidWin, F.state, Node.sMEM] <;> omega
  | x :: y :: P, w0, hL, _ => by
    have ih := wins_chain I nr L (y :: P) (w0 + 1) (by simp at hL ⊢; omega) (by simp)
    rw [winsOf_cons, winsOf_cons] at *
    simp only [List.cons_append] at ih ⊢
    refine ⟨?_, ih⟩
    simp only [List.length_cons] at hL
    refine ⟨by simp [F.state, Node.sTAG, Node.sCH], fun h => absurd (by cases x.1 <;> rfl) h, ?_⟩
    simp only [nxt]
    right
    refine ⟨rfl, ?_, ?_⟩
    · cases x.1 <;> simp [kidWin] <;> omega
    · intro w' hw'; simp only [F.chw, Option.some.injEq] at hw'; subst hw'
      cases x.1 <;> cases y.1 <;> rfl

/-! ### Bitmaps -/

theorem bitmapOf_shift : ∀ (l : List Kid) (i : Nat), bitmapOf l i = 2 ^ i * bitmapOf l 0
  | [], _ => by simp [bitmapOf]
  | k :: l, i => by
    simp only [bitmapOf]
    rw [bitmapOf_shift l (i + 1), bitmapOf_shift l 1, Nat.pow_succ]
    simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (kidBit k)]

theorem bitmapOf_cons (k : Kid) (l : List Kid) : bitmapOf (k :: l) 0 = kidBit k + 2 * bitmapOf l 0 := by
  simp only [bitmapOf]; rw [bitmapOf_shift l 1]; simp

theorem kidBit_le (k : Kid) : kidBit k ≤ 1 := by cases k <;> simp [kidBit]

theorem bitOf_bitmap : ∀ (l : List Kid) (j : Nat), bitOf (bitmapOf l 0) j = kidBit (l.getD j .none)
  | [], j => by simp [bitmapOf, bitOf, kidBit]
  | k :: l, 0 => by
    rw [bitmapOf_cons]; have := kidBit_le k; simp [bitOf]; omega
  | k :: l, j + 1 => by
    rw [bitmapOf_cons, List.getD_cons_succ, ← bitOf_bitmap l j]
    have := kidBit_le k
    simp only [bitOf, Nat.pow_succ']
    rw [← Nat.div_div_eq_div_mul]
    have h2 : (kidBit k + 2 * bitmapOf l 0) / 2 = bitmapOf l 0 := by omega
    rw [h2]

theorem bitmap_lt : ∀ (l : List Kid), bitmapOf l 0 < 2 ^ l.length
  | [] => by simp [bitmapOf]
  | k :: l => by
    rw [bitmapOf_cons]; have := bitmap_lt l; have := kidBit_le k
    simp only [List.length_cons, Nat.pow_succ]; omega

theorem kidBit_ne (k : Kid) : kidBit k = if k ≠ .none then 1 else 0 := by cases k <;> simp [kidBit]

theorem sum_kidBit : ∀ (l : List Kid) (m : Nat), l.length ≤ m →
    ((List.range m).map fun i => kidBit (l.getD i .none)).sum = popK l
  | [], m, _ => by
    simp only [List.getD_nil, popK, List.filter_nil, List.length_nil]
    induction m with
    | zero => rfl
    | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih (by simp)]; rfl
  | k :: l, m + 1, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have := sum_kidBit l m (by simp at h; omega)
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, this, popK, List.filter_cons]
    rw [kidBit_ne]; split <;> simp_all <;> omega
  | _ :: _, 0, h => by simp at h

theorem foldl_sum (g : Nat → Nat) (l : List Nat) (a : Nat) :
    l.foldl (fun acc i => acc + g i) a = a + (l.map g).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem popOf_branch (v : Option VSlot) (kids : List Kid) (m : Nat) (h : kids.length = 16) :
    popOf (.branch v kids m) = popK kids := by
  have hb : bmvOf (.branch v kids m) = bitmapOf kids 0 := rfl
  show (List.range 16).foldl (fun a i => a + bitOf (bmvOf (.branch v kids m)) i) 0 = _
  rw [foldl_sum (fun i => bitOf (bmvOf (.branch v kids m)) i), Nat.zero_add, hb]
  simp only [bitOf_bitmap]
  exact sum_kidBit kids 16 (by omega)

/-! ### The fields chain -/

theorem ch_mid {α : Type} {R : α → α → Prop} : ∀ (l1 : List α) (a b : α) (l2 : List α),
    Ch R (l1 ++ [a]) → R a b → Ch R (b :: l2) → Ch R (l1 ++ a :: b :: l2)
  | [], _, _, _, _, hab, h => ⟨hab, h⟩
  | [x], _, _, _, h1, hab, h => ⟨h1.1, hab, h⟩
  | x :: y :: l1, a, b, l2, h1, hab, h => ⟨h1.1, ch_mid (y :: l1) a b l2 h1.2 hab h⟩

theorem chain_wins (I : Info) (nr : NodeRec) (kids : List Kid) (hpop : nochildOf nr = b2n (popK kids = 0)) :
    ∀ (l1 : List F), Ch (SuccOk nr) (l1 ++ [F.bm]) → Ch (SuccOk nr) (l1 ++ F.bm :: (branchWins I kids ++ [F.mem])) := by
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
    · refine ⟨by simp [F.state, Node.sTAG, Node.sCH], fun _ w' h => ?_, ?_⟩
      · simp only [F.chw, Option.some.injEq] at h; subst h; cases x.1 <;> rfl
      · simp only [nxt, hpop, List.length_cons, b2n, Nat.add_one_ne_zero, decide_false, ite_false]
        rfl
    · have := wins_chain I nr (x :: P).length (x :: P) 0 (by simp) (by simp)
      rw [winsOf_cons, List.cons_append] at this
      exact this

/-- **The non-empty fields of a record chain by `SuccOk`.** -/
theorem chain_fields (I : Info) (n : Nat) (nr : NodeRec) (hw : nr.wf) :
    Ch (SuccOk nr) (nef (hplenOf nr) (fieldsOf I n nr)) := by
  have hst : ∀ f g, SuccOk nr f g ↔ g.state ≠ Node.sTAG ∧ (f.state ≠ Node.sCH → ∀ w', g.chw = some w' → w'.w = 0) ∧
      nxt nr f g := fun _ _ => Iff.rfl
  have ok : ∀ f g, g.state ≠ Node.sTAG → f.state ≠ Node.sCH → g.chw = none → nxt nr f g → SuccOk nr f g :=
    fun f g h1 h2 h3 h4 => ⟨h1, fun _ w' h => (by rw [h3] at h; cases h), h4⟩
  cases nr with
  | leaf k v m =>
    have hkl : F.len (hplenOf (.leaf k v m)) .key = k.length / 2 := by simp [F.len, hplenOf, isLE, NodeRec.key]
    have e : nef (hplenOf (.leaf k v m)) (fieldsOf I n (.leaf k v m)) =
        [F.tag, .hpl, .hpf] ++ (if k.length / 2 = 0 then [] else [.key]) ++ [.vlen, .vh (valWin I n v), .mem] := by
      by_cases hk : k.length / 2 = 0 <;> simp [nef, fieldsOf, List.filter_cons, hkl, hk, F.len] <;>
        simp [hplenOf, isLE, NodeRec.key] <;> omega
    rw [e]
    split
    · exact ⟨ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl, ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl,
        ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl (by simp [nxt, nokeyOf, hplenOf, isLE, NodeRec.key, NodeLay.leafB, b2n, *]; rfl),
        ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl, ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl, trivial⟩
    · exact ⟨ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl, ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl,
        ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl (by simp [nxt, nokeyOf, hplenOf, isLE, NodeRec.key, NodeLay.leafB, b2n, *]; rfl),
        ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl, ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl,
        ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl, trivial⟩
  | ext k kid m =>
    have hkl : F.len (hplenOf (.ext k kid m)) .key = k.length / 2 := by simp [F.len, hplenOf, isLE, NodeRec.key]
    have e : nef (hplenOf (.ext k kid m)) (fieldsOf I n (.ext k kid m)) =
        [F.tag, .hpl, .hpf] ++ (if k.length / 2 = 0 then [] else [.key]) ++ [.ch (kidWin I kid 0 true none), .mem] := by
      by_cases hk : k.length / 2 = 0 <;> simp [nef, fieldsOf, List.filter_cons, hkl, hk, F.len] <;>
        simp [hplenOf, isLE, NodeRec.key] <;> omega
    have hch : ∀ f, f.state ≠ Node.sCH → (SuccOk (.ext k kid m) f (.ch (kidWin I kid 0 true none)) ↔
        nxt (.ext k kid m) f (.ch (kidWin I kid 0 true none))) := by
      intro f hf
      refine ⟨fun h => h.2.2, fun h => ⟨by simp [F.state, Node.sTAG, Node.sCH], fun _ w' hw => ?_, h⟩⟩
      simp only [F.chw, Option.some.injEq] at hw; subst hw; cases kid <;> rfl
    have hlast : SuccOk (.ext k kid m) (.ch (kidWin I kid 0 true none)) .mem :=
      ⟨by decide, fun _ w' h => (by cases h), .inl ⟨rfl, by cases kid <;> rfl⟩⟩
    rw [e]
    split
    · exact ⟨ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl, ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl,
        (hch _ (by decide)).2 (by simp [nxt, nokeyOf, hplenOf, isLE, NodeRec.key, NodeLay.leafB, b2n, *]; rfl),
        hlast, trivial⟩
    · exact ⟨ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl, ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl rfl,
        ok _ _ (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) (by simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH, Node.sMEM]) rfl (by simp [nxt, nokeyOf, hplenOf, isLE, NodeRec.key, NodeLay.leafB, b2n, *]; rfl),
        (hch _ (by decide)).2 rfl, hlast, trivial⟩
  | branch v kids m =>
    have hl : kids.length = 16 := hw.1
    have hpop : nochildOf (.branch v kids m) = b2n (popK kids = 0) := by
      simp only [nochildOf, isLE, popOf_branch v kids m hl]; simp [b2n]
    have hnef : nef (hplenOf (.branch v kids m)) (branchWins I kids ++ [F.mem]) = branchWins I kids ++ [F.mem] := by
      rw [List.filter_eq_self]; intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · obtain ⟨_, _, _, _, _, _, rfl⟩ := NodeLay.mem_branchWins hf; simp [F.len]
      · simp at hf; subst hf; simp [F.len]
    cases v with
    | none =>
      have e : fieldsOf I n (.branch none kids m) = [F.tag, F.bm] ++ (branchWins I kids ++ [F.mem]) := by
        simp [fieldsOf]
      rw [e, nef, List.filter_append, show List.filter (fun f => F.len _ f != 0) (branchWins I kids ++ [F.mem]) = _ from hnef]
      exact chain_wins I _ kids hpop [F.tag] ⟨⟨by decide, fun _ w' h => (by cases h), rfl⟩, trivial⟩
    | some sv =>
      have e : fieldsOf I n (.branch (some sv) kids m) =
          [F.tag, F.vlen, F.vh (valWin I n sv), F.bm] ++ (branchWins I kids ++ [F.mem]) := by
        simp [fieldsOf]
      rw [e, nef, List.filter_append, show List.filter (fun f => F.len _ f != 0) (branchWins I kids ++ [F.mem]) = _ from hnef]
      exact chain_wins I _ kids hpop [F.tag, F.vlen, F.vh (valWin I n sv)]
        ⟨⟨by decide, fun _ w' h => (by cases h), rfl⟩,
          ⟨⟨by simp [F.state, Node.sTAG, Node.sVH], fun _ w' h => (by cases h), rfl⟩,
          ⟨⟨by decide, fun _ w' h => (by cases h), rfl⟩, trivial⟩⟩⟩

/-! ## Rows of one node -/

section
variable (I : Info) (n : Nat)

theorem fields_last (nr : NodeRec) : ∃ X, fieldsOf I n nr = X ++ [F.mem] := by
  cases nr with
  | leaf k v m => exact ⟨[F.tag, .hpl, .hpf, .key, .vlen, .vh (valWin I n v)], rfl⟩
  | ext k kid m => exact ⟨[F.tag, .hpl, .hpf, .key, .ch (kidWin I kid 0 true none)], rfl⟩
  | branch v kids m => cases v with
    | none => exact ⟨[F.tag, F.bm] ++ branchWins I kids, by simp [fieldsOf]⟩
    | some sv => exact ⟨[F.tag, F.vlen, F.vh (valWin I n sv), F.bm] ++ branchWins I kids, by simp [fieldsOf]⟩

theorem lay_last : ((NodeLay.layN I n).getD ((NodeLay.layN I n).length - 1) default) = (F.mem, 7) := by
  obtain ⟨X, hX⟩ := fields_last I n (I.nodeAt n)
  have : NodeLay.layN I n = layout X (hplenOf (I.nodeAt n)) ++ (List.range 8).map (F.mem, ·) := by
    simp only [NodeLay.layN, hX, layout, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, F.len]
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

variable {I n} (hw : (I.nodeAt n).wf)
include hw

/-- Consecutive positions of a node. -/
theorem lay_adj {p : Nat} (hp : p + 1 < (NodeLay.layN I n).length) :
    let a := (NodeLay.layN I n).getD p default
    let b := (NodeLay.layN I n).getD (p + 1) default
    (b.1 = a.1 ∧ b.2 = a.2 + 1 ∧ a.2 + 1 < a.1.len (hplenOf (I.nodeAt n))) ∨
      (a.2 + 1 = a.1.len (hplenOf (I.nodeAt n)) ∧ b.2 = 0 ∧ SuccOk (I.nodeAt n) a.1 b.1) :=
  layout_adj _ _ _ (chain_fields I n _ hw) p hp

/-- The last row of a node is the last `MEM` byte, and only it. -/
theorem lay_last_iff {p : Nat} (hp : p < (NodeLay.layN I n).length) :
    p + 1 = (NodeLay.layN I n).length ↔
      (((NodeLay.layN I n).getD p default).1.state = Node.sMEM ∧ ((NodeLay.layN I n).getD p default).2 = 7) := by
  constructor
  · intro h; rw [show p = (NodeLay.layN I n).length - 1 by omega, lay_last]; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩
    apply Classical.byContradiction; intro hne
    have hadj := lay_adj hw (p := p) (by omega)
    have hm : ((NodeLay.layN I n).getD p default).1 = .mem := by
      revert h1; generalize ((NodeLay.layN I n).getD p default).1 = f; cases f <;> simp [F.state, Node.sMEM] <;> decide
    simp only [hm, h2] at hadj
    rcases hadj with ⟨_, _, h3⟩ | ⟨_, _, h3⟩
    · simp [F.len] at h3
    · exact h3.2.2

end

/-! ## Rows of the table -/

/-- First row of node `n`. -/
def off (I : Info) : Nat → Nat
  | 0 => 0
  | n + 1 => off I n + (nodeRecs I n).length

theorem off_mono (I : Info) {a b : Nat} (h : a ≤ b) : off I a ≤ off I b := by
  induction b with
  | zero => rw [show a = 0 by omega]; exact Nat.le_refl _
  | succ b ih =>
    by_cases h' : a = b + 1
    · rw [h']; exact Nat.le_refl _
    · have := ih (by omega); simp only [off]; omega

theorem recs_len' (I : Info) (N : Nat) : ((List.range N).flatMap (nodeRecs I)).length = off I N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [off]

theorem recs_get' (I : Info) (N : Nat) {n p : Nat} (hn : n < N) (hp : p < (nodeRecs I n).length) :
    ((List.range N).flatMap (nodeRecs I)).getD (off I n + p) default = (nodeRecs I n).getD p default := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.getD_eq_getElem?_getD]
    by_cases h : n < N
    · have hl : off I n + p < ((List.range N).flatMap (nodeRecs I)).length := by
        rw [recs_len']
        have := off_mono I (show n + 1 ≤ N by omega)
        simp only [off] at this; omega
      rw [List.getElem?_append_left hl, ← List.getD_eq_getElem?_getD, ih h]
    · have hnN : n = N := by omega
      subst hnN
      rw [List.getElem?_append_right (by rw [recs_len']; omega), recs_len']
      simp [List.getD_eq_getElem?_getD]

theorem recs_cover' (I : Info) (N : Nat) {q : Nat} (hq : q < off I N) :
    ∃ n p, n < N ∧ p < (nodeRecs I n).length ∧ q = off I n + p := by
  induction N with
  | zero => simp [off] at hq
  | succ N ih =>
    by_cases h : q < off I N
    · obtain ⟨n, p, h1, h2, h3⟩ := ih h; exact ⟨n, p, by omega, h2, h3⟩
    · simp only [off] at hq; exact ⟨N, q - off I N, by omega, by omega, by omega⟩

end NodeSeq

end ZkFormal.Near.Render
