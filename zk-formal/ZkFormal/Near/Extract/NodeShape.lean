import ZkFormal.Near.Extract.NodeWalk

/-!
# ZkFormal.Near.Extract.NodeShape — the field list of a node, per node type

All four node types follow the field order `TAG HPL HPF KEY VLEN VH BM CH* MEM`
with the fields selected by the node constants.
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

variable {tr : Trace Fp} {pub : List Fp}

theorem cv_one {r x : Nat} (h : tr.cell T_NODE r x = 1) : cv tr T_NODE r x = 1 := by
  simp [cv, h, Fp.toNat_one]

theorem cv_zero {r x : Nat} (h : tr.cell T_NODE r x = 0) : cv tr T_NODE r x = 0 := by
  simp [cv, h, Fp.toNat_zero]

theorem of_cv_zero {r x : Nat} (h : cv tr T_NODE r x = 0) : tr.cell T_NODE r x = 0 := by
  rw [cell_eq_cast, h]; rfl

theorem of_cv_one {r x : Nat} (h : cv tr T_NODE r x = 1) : tr.cell T_NODE r x = 1 := by
  rw [cell_eq_cast, h]; rfl

variable (hL : TableLocal Node.table tr T_NODE pub)
include hL

theorem cvb {r x : Nat} (hr : r < tr.height T_NODE) (hx : x ∈ boolCols) : cv tr T_NODE r x ≤ 1 :=
  cv_bool (isBool hL hr hx)

theorem stateSumNat {r : Nat} (hr : r < tr.height T_NODE) (ha : tr.cell T_NODE r act = 1) :
    cv tr T_NODE r sTAG + cv tr T_NODE r sHPL + cv tr T_NODE r sHPF + cv tr T_NODE r sKEY +
      cv tr T_NODE r sVLEN + cv tr T_NODE r sVH + cv tr T_NODE r sBM + cv tr T_NODE r sCH +
      cv tr T_NODE r sMEM = 1 := by
  have h := (rowFacts hL hr).2.1
  rw [ha] at h
  have b1 := cvb hL hr (x := sTAG) (by simp [boolCols, states])
  have b2 := cvb hL hr (x := sHPL) (by simp [boolCols, states])
  have b3 := cvb hL hr (x := sHPF) (by simp [boolCols, states])
  have b4 := cvb hL hr (x := sKEY) (by simp [boolCols, states])
  have b5 := cvb hL hr (x := sVLEN) (by simp [boolCols, states])
  have b6 := cvb hL hr (x := sVH) (by simp [boolCols, states])
  have b7 := cvb hL hr (x := sBM) (by simp [boolCols, states])
  have b8 := cvb hL hr (x := sCH) (by simp [boolCols, states])
  have b9 := cvb hL hr (x := sMEM) (by simp [boolCols, states])
  rw [cell_eq_cast tr T_NODE r sTAG, cell_eq_cast tr T_NODE r sHPL, cell_eq_cast tr T_NODE r sHPF,
    cell_eq_cast tr T_NODE r sKEY, cell_eq_cast tr T_NODE r sVLEN, cell_eq_cast tr T_NODE r sVH,
    cell_eq_cast tr T_NODE r sBM, cell_eq_cast tr T_NODE r sCH, cell_eq_cast tr T_NODE r sMEM] at h
  apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
  simp only [natCast_add]
  rw [show ((1 : Nat) : Fp) = 1 from rfl, ← h]
  have z : ((0 : Nat) : Fp) = 0 := rfl
  grind

theorem typeSumNat {r : Nat} (hr : r < tr.height T_NODE) (ha : tr.cell T_NODE r act = 1) :
    cv tr T_NODE r tl + cv tr T_NODE r te + cv tr T_NODE r tb1 + cv tr T_NODE r tb2 = 1 := by
  have h := (rowFacts hL hr).1
  rw [ha] at h
  have b1 := cvb hL hr (x := tl) (by simp [boolCols])
  have b2 := cvb hL hr (x := te) (by simp [boolCols])
  have b3 := cvb hL hr (x := tb1) (by simp [boolCols])
  have b4 := cvb hL hr (x := tb2) (by simp [boolCols])
  rw [cell_eq_cast tr T_NODE r tl, cell_eq_cast tr T_NODE r te, cell_eq_cast tr T_NODE r tb1,
    cell_eq_cast tr T_NODE r tb2] at h
  apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
  simp only [natCast_add]
  rw [show ((1 : Nat) : Fp) = 1 from rfl, ← h]
  grind

/-- Field states are one-hot on active rows. -/
theorem stOnly {r x y : Nat} (hr : r < tr.height T_NODE) (ha : tr.cell T_NODE r act = 1)
    (hx : tr.cell T_NODE r x = 1) (hxs : x ∈ states) (hys : y ∈ states) (hne : y ≠ x) :
    tr.cell T_NODE r y = 0 := by
  have S := stateSumNat hL hr ha
  have hx1 := cv_one hx
  apply of_cv_zero
  simp only [states, List.mem_cons, List.not_mem_nil, or_false] at hxs hys
  rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hys with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hne | omega

theorem typeOnly {r x y : Nat} (hr : r < tr.height T_NODE) (ha : tr.cell T_NODE r act = 1)
    (hx : tr.cell T_NODE r x = 1) (hxs : x ∈ [tl, te, tb1, tb2]) (hys : y ∈ [tl, te, tb1, tb2]) (hne : y ≠ x) :
    tr.cell T_NODE r y = 0 := by
  have S := typeSumNat hL hr ha
  have hx1 := cv_one hx
  apply of_cv_zero
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxs hys
  rcases hxs with rfl | rfl | rfl | rfl <;> rcases hys with rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hne | omega

variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem segAct (hC : NodeCtx tr s ℓ fl) {d : Nat} (hd : d < ℓ) : tr.cell T_NODE (s + d) act = 1 := by
  have := hC.seg.2.2.2.1 (s + d) (by omega) (by omega); rwa [one_iff] at this

theorem segConst (hC : NodeCtx tr s ℓ fl) {x : Nat} (hx : x ∈ nodeConst) {d : Nat} (hd : d < ℓ) :
    tr.cell T_NODE (s + d) x = tr.cell T_NODE s x := by
  have := const_of (f := fun q => tr.cell T_NODE q x) (s := s) (ℓ := ℓ) (fun q h1 h2 => by
    have ha := hC.seg.2.2.2.1 q h1 (by omega); rw [one_iff] at ha
    have hl := zero_of hL (by have := hC.bound; omega) (by simp [boolCols]) (hC.seg.2.2.2.2.2 q h1 h2)
    exact (inNode hL (by have := hC.bound; omega) ha hl).2.2.2 x hx) (s + d) (by omega) (by omega)
  exact this

/-- Node constant at a field start. -/
theorem fConst (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length) {x : Nat} (hx : x ∈ nodeConst) :
    tr.cell T_NODE (s + fl[i].1) x = tr.cell T_NODE s x := by
  have := (hC.fields.field _ (List.getElem_mem hi)); have := this.1.pos
  exact segConst hL hC hx (by omega)

theorem fAct (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length) : tr.cell T_NODE (s + fl[i].1) act = 1 := by
  have := (hC.fields.field _ (List.getElem_mem hi)); have := this.1.pos
  exact segAct hL hC (by omega)

/-- Step to the next field (the current one is not `MEM`). -/
theorem goNext (hC : NodeCtx tr s ℓ fl) {i x : Nat} (hi : i < fl.length)
    (hx : tr.cell T_NODE (s + fl[i].1) x = 1) (hxs : x ∈ states) (hxm : x ≠ sMEM) :
    ∃ h : i + 1 < fl.length, fl[i + 1].1 = fl[i].1 + fl[i].2 := by
  have hm := stOnly hL (fieldRow hL hC hi).1 (fAct hL hC hi) hx hxs (by simp [states]) (Ne.symm hxm)
  have h1 := notLast hL hC hi hm
  exact ⟨h1, hC.fields.next h1⟩

theorem firstField (hC : NodeCtx tr s ℓ fl) :
    ∃ h : 0 < fl.length, fl[0].1 = 0 ∧ tr.cell T_NODE s sTAG = 1 := by
  have h0 := Fields.nonempty hL hC.seg hC.fields
  refine ⟨h0, hC.fields.first h0, ?_⟩
  have := hC.seg.2.1; rw [one_iff] at this
  exact ((rowFacts hL (by have := hC.bound; have := hC.seg.1; omega)).2.2.2.1 this).2.1

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- Field lengths. -/
theorem lens (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length) :
    (tr.cell T_NODE (s + fl[i].1) sTAG = 1 → fl[i].2 = 1) ∧
    (tr.cell T_NODE (s + fl[i].1) sHPL = 1 → fl[i].2 = 4) ∧
    (tr.cell T_NODE (s + fl[i].1) sHPF = 1 → fl[i].2 = 1) ∧
    (tr.cell T_NODE (s + fl[i].1) sKEY = 1 → fl[i].2 + 1 = cv tr T_NODE s hplen) ∧
    (tr.cell T_NODE (s + fl[i].1) sVLEN = 1 → fl[i].2 = 4) ∧
    (tr.cell T_NODE (s + fl[i].1) sVH = 1 → fl[i].2 = 32) ∧
    (tr.cell T_NODE (s + fl[i].1) sBM = 1 → fl[i].2 = 2) ∧
    (tr.cell T_NODE (s + fl[i].1) sCH = 1 → fl[i].2 = 32) ∧
    (tr.cell T_NODE (s + fl[i].1) sMEM = 1 → fl[i].2 = 8) := by
  have L := fieldLength hL hC hi
  simp only at L
  refine ⟨L.1, L.2.1, L.2.2.1, fun h => ?_, L.2.2.2.2.1, L.2.2.2.2.2.1, L.2.2.2.2.2.2.1, L.2.2.2.2.2.2.2.1,
    L.2.2.2.2.2.2.2.2⟩
  have := L.2.2.2.1 h
  rw [fConst hL hC hi (by simp [nodeConst])] at this; exact this

/-- Successor states with the node constants read at the node start. -/
theorem nx (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i + 1 < fl.length) :
    (tr.cell T_NODE (s + fl[i].1) sTAG = 1 →
      tr.cell T_NODE (s + fl[i + 1].1) sHPL = tr.cell T_NODE s tl + tr.cell T_NODE s te ∧
      tr.cell T_NODE (s + fl[i + 1].1) sBM = tr.cell T_NODE s tb1 ∧
      tr.cell T_NODE (s + fl[i + 1].1) sVLEN = tr.cell T_NODE s tb2) ∧
    (tr.cell T_NODE (s + fl[i].1) sHPL = 1 → tr.cell T_NODE (s + fl[i + 1].1) sHPF = 1) ∧
    (tr.cell T_NODE (s + fl[i].1) sHPF = 1 →
      tr.cell T_NODE (s + fl[i + 1].1) sKEY = 1 - tr.cell T_NODE s nokey ∧
      tr.cell T_NODE (s + fl[i + 1].1) sVLEN = tr.cell T_NODE s nokey * tr.cell T_NODE s tl ∧
      tr.cell T_NODE (s + fl[i + 1].1) sCH = tr.cell T_NODE s nokey * tr.cell T_NODE s te) ∧
    (tr.cell T_NODE (s + fl[i].1) sKEY = 1 →
      tr.cell T_NODE (s + fl[i + 1].1) sVLEN = tr.cell T_NODE s tl ∧
      tr.cell T_NODE (s + fl[i + 1].1) sCH = tr.cell T_NODE s te) ∧
    (tr.cell T_NODE (s + fl[i].1) sVLEN = 1 → tr.cell T_NODE (s + fl[i + 1].1) sVH = 1) ∧
    (tr.cell T_NODE (s + fl[i].1) sVH = 1 →
      tr.cell T_NODE (s + fl[i + 1].1) sMEM = tr.cell T_NODE s tl ∧
      tr.cell T_NODE (s + fl[i + 1].1) sBM = tr.cell T_NODE s tb2) ∧
    (tr.cell T_NODE (s + fl[i].1) sBM = 1 →
      tr.cell T_NODE (s + fl[i + 1].1) sMEM = tr.cell T_NODE s nochild ∧
      tr.cell T_NODE (s + fl[i + 1].1) sCH = 1 - tr.cell T_NODE s nochild) ∧
    (tr.cell T_NODE (s + fl[i].1) sCH = 1 →
      tr.cell T_NODE (s + fl[i + 1].1) sCH + tr.cell T_NODE (s + fl[i + 1].1) sMEM = 1 ∧
      tr.cell T_NODE (s + fl[i + 1].1) sMEM = tr.cell T_NODE (s + fl[i].1) lastw) := by
  have N := nextState hL hC hi
  simp only at N
  have hi' : i < fl.length := by omega
  rw [fConst hL hC hi' (x := tl) (by simp [nodeConst]), fConst hL hC hi' (x := te) (by simp [nodeConst]),
    fConst hL hC hi' (x := tb1) (by simp [nodeConst]), fConst hL hC hi' (x := tb2) (by simp [nodeConst]),
    fConst hL hC hi' (x := nokey) (by simp [nodeConst]), fConst hL hC hi' (x := nochild) (by simp [nodeConst])] at N
  exact N

/-- Window constants along a `CH` field. -/
theorem chConst (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length)
    (hch : tr.cell T_NODE (s + fl[i].1) sCH = 1) {x : Nat} (hx : x ∈ windowConst) :
    ∀ d, d < fl[i].2 → tr.cell T_NODE (s + fl[i].1 + d) x = tr.cell T_NODE (s + fl[i].1) x := by
  have hF := (hC.fields.field _ (List.getElem_mem hi))
  intro d; induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    have hc : tr.cell T_NODE (s + fl[i].1 + d) sCH = 1 := by rw [hF.1.st d (by omega) sCH (by simp [states]), hch]
    have hfe : tr.cell T_NODE (s + fl[i].1 + d) fe = 0 :=
      bool01 hL (by have := hC.bound; have := hF.2; omega) (by simp [boolCols]) (fun h' => by
        have := (hF.1.fe d (by omega)).1 h'; omega)
    have := winConst hL (r := s + fl[i].1 + d) (by have := hC.bound; have := hF.2; omega) hc hfe x hx
    rw [show s + fl[i].1 + (d + 1) = s + fl[i].1 + d + 1 by omega, this, ih (by omega)]

/-- Consecutive `CH` fields: the window index counts up. -/
theorem chStep (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i + 1 < fl.length)
    (hch : tr.cell T_NODE (s + fl[i].1) sCH = 1) (hch' : tr.cell T_NODE (s + fl[i + 1].1) sCH = 1) :
    tr.cell T_NODE (s + fl[i + 1].1) w = tr.cell T_NODE (s + fl[i].1) w + 1 := by
  have hi' : i < fl.length := by omega
  obtain ⟨he, hst, -⟩ := fieldEndRow hL hC hi'
  have hF := (hC.fields.field _ (List.getElem_mem hi'))
  have hF1 := (hC.fields.field _ (List.getElem_mem hi))
  have hb : s + fl[i].1 + fl[i].2 - 1 + 1 < tr.height T_NODE := by
    have := hC.fields.next hi; have := hF1.2; have := hC.bound; have := hF1.1.pos; have := hF.1.pos; omega
  have W := (winIndex hL hb he).2 (by rw [hst sCH (by simp [states]), hch])
    (by rw [show s + fl[i].1 + fl[i].2 - 1 + 1 = s + fl[i + 1].1 by have := hC.fields.next hi; have := hF.1.pos; omega]
        exact hch')
  rw [show s + fl[i].1 + fl[i].2 - 1 + 1 = s + fl[i + 1].1 by have := hC.fields.next hi; have := hF.1.pos; omega] at W
  rw [W]
  have := chConst hL hC hi' hch (x := w) (by simp [windowConst]) (fl[i].2 - 1) (by have := hF.1.pos; omega)
  rw [show s + fl[i].1 + (fl[i].2 - 1) = s + fl[i].1 + fl[i].2 - 1 by have := hF.1.pos; omega] at this
  rw [this]

/-- A non-`CH` field followed by a `CH` field: window index 0. -/
theorem chFirst (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i + 1 < fl.length)
    (hch : tr.cell T_NODE (s + fl[i].1) sCH = 0) (hch' : tr.cell T_NODE (s + fl[i + 1].1) sCH = 1) :
    tr.cell T_NODE (s + fl[i + 1].1) w = 0 := by
  have hi' : i < fl.length := by omega
  obtain ⟨he, hst, -⟩ := fieldEndRow hL hC hi'
  have hF := (hC.fields.field _ (List.getElem_mem hi'))
  have hF1 := (hC.fields.field _ (List.getElem_mem hi))
  have hb : s + fl[i].1 + fl[i].2 - 1 + 1 < tr.height T_NODE := by
    have := hC.fields.next hi; have := hF1.2; have := hC.bound; have := hF1.1.pos; have := hF.1.pos; omega
  have e : s + fl[i].1 + fl[i].2 - 1 + 1 = s + fl[i + 1].1 := by
    have := hC.fields.next hi; have := hF.1.pos; omega
  have W := (winIndex hL hb he).1 (by rw [hst sCH (by simp [states]), hch]) (by rw [e]; exact hch')
  rwa [e] at W

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem chRunAux (hC : NodeCtx tr s ℓ fl) {i0 : Nat} (hi0 : i0 < fl.length)
    (hch : tr.cell T_NODE (s + fl[i0].1) sCH = 1) (hw0 : tr.cell T_NODE (s + fl[i0].1) w = 0) :
    ∀ j, (∀ j', j' < j → ∀ hj' : i0 + j' < fl.length, tr.cell T_NODE (s + fl[i0 + j'].1) lastw ≠ 1) →
      ∃ hj : i0 + j < fl.length, tr.cell T_NODE (s + fl[i0 + j].1) sCH = 1 ∧
        tr.cell T_NODE (s + fl[i0 + j].1) w = ((j : Nat) : Fp) ∧ fl[i0 + j].1 = fl[i0].1 + 32 * j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨hi0, hch, by show tr.cell T_NODE (s + fl[i0].1) w = _; rw [hw0]; rfl, by simp⟩
  | succ j ih =>
    intro H
    obtain ⟨hj, c1, wj, pj⟩ := ih (fun j' hj' => H j' (by omega))
    have hlw : tr.cell T_NODE (s + fl[i0 + j].1) lastw = 0 :=
      bool01 hL (fieldRow hL hC hj).1 (by simp [boolCols]) (H j (by omega) hj)
    obtain ⟨hj1, e⟩ := goNext hL hC hj c1 (by simp [states]) (by decide)
    have N := ((nx hL hC hj1).2.2.2.2.2.2.2 c1)
    rw [hlw] at N
    have c2 : tr.cell T_NODE (s + fl[i0 + j + 1].1) sCH = 1 := by rw [N.2] at N; grind
    have W := chStep hL hC hj1 c1 c2
    have l := (lens hL hC hj).2.2.2.2.2.2.2.1 c1
    refine ⟨hj1, c2, ?_, ?_⟩
    · show tr.cell T_NODE (s + fl[i0 + j + 1].1) w = _
      rw [W, wj, natCast_add]; rfl
    · show fl[i0 + j + 1].1 = _
      rw [e, pj, l]; omega

theorem chRun (hC : NodeCtx tr s ℓ fl) {i0 : Nat} (hi0 : i0 < fl.length)
    (hch : tr.cell T_NODE (s + fl[i0].1) sCH = 1) (hw0 : tr.cell T_NODE (s + fl[i0].1) w = 0) :
    ∃ m, ∃ hm : i0 + m + 1 < fl.length,
      (∀ j, j ≤ m → ∃ hj : i0 + j < fl.length, tr.cell T_NODE (s + fl[i0 + j].1) sCH = 1 ∧
        tr.cell T_NODE (s + fl[i0 + j].1) w = ((j : Nat) : Fp) ∧ fl[i0 + j].1 = fl[i0].1 + 32 * j ∧
        fl[i0 + j].2 = 32) ∧
      tr.cell T_NODE (s + fl[i0 + m].1) lastw = 1 ∧
      tr.cell T_NODE (s + fl[i0 + m + 1].1) sMEM = 1 ∧ fl[i0 + m + 1].1 = fl[i0].1 + 32 * (m + 1) := by
  have A := chRunAux hL hC hi0 hch hw0
  have hex : ∃ m, ∃ hm : i0 + m < fl.length, tr.cell T_NODE (s + fl[i0 + m].1) lastw = 1 := by
    apply Classical.byContradiction
    intro hne
    obtain ⟨h, -⟩ := A fl.length (fun j' _ hj' h => hne ⟨j', hj', h⟩)
    omega
  obtain ⟨m, ⟨hm, hlw⟩, hmin⟩ := exists_least hex
  have B : ∀ j, j ≤ m → ∃ hj : i0 + j < fl.length, tr.cell T_NODE (s + fl[i0 + j].1) sCH = 1 ∧
      tr.cell T_NODE (s + fl[i0 + j].1) w = ((j : Nat) : Fp) ∧ fl[i0 + j].1 = fl[i0].1 + 32 * j ∧
      fl[i0 + j].2 = 32 := by
    intro j hj
    obtain ⟨hj', c1, c2, c3⟩ := A j (fun j' hj'' hj''' h => hmin j' (by omega) ⟨hj''', h⟩)
    exact ⟨hj', c1, c2, c3, (lens hL hC hj').2.2.2.2.2.2.2.1 c1⟩
  obtain ⟨hm', c1, -, pm, lm⟩ := B m (Nat.le_refl _)
  obtain ⟨hm1, e⟩ := goNext hL hC hm' c1 (by simp [states]) (by decide)
  have N := ((nx hL hC hm1).2.2.2.2.2.2.2 c1)
  rw [hlw] at N
  exact ⟨m, hm1, B, hlw, N.2, by rw [e, pm, lm]; omega⟩

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

/-- Field lists `(offset, length)` per node type (`h` = `hplen`). -/
def keyFL (h : Nat) : List (Nat × Nat) := [(0, 1), (1, 4), (5, 1)] ++ (if h = 1 then [] else [(6, h - 1)])
def leafFL (h : Nat) : List (Nat × Nat) := keyFL h ++ [(5 + h, 4), (9 + h, 32), (41 + h, 8)]
def extFL (h : Nat) : List (Nat × Nat) := keyFL h ++ [(5 + h, 32), (37 + h, 8)]
/-- Branch: `o = 1` (no value) or `o = 37` (value), `p` windows. -/
def brFL (o p : Nat) : List (Nat × Nat) :=
  [(0, 1)] ++ (if o = 1 then [] else [(1, 4), (5, 32)]) ++ [(o, 2)] ++
    (List.range p).map (fun j => (o + 2 + 32 * j, 32)) ++ [(o + 2 + 32 * p, 8)]

theorem take_three {fl : List (Nat × Nat)} (h : 2 < fl.length) : fl.take 3 = [fl[0], fl[1], fl[2]] := by
  match fl, h with
  | a :: b :: c :: _, _ => rfl

theorem take_four {fl : List (Nat × Nat)} (h : 3 < fl.length) : fl.take 4 = [fl[0], fl[1], fl[2], fl[3]] := by
  match fl, h with
  | a :: b :: c :: d :: _, _ => rfl

theorem drop_cons_get {α : Type} {l : List α} {q : Nat} (h : q < l.length) : l.drop q = l[q] :: l.drop (q + 1) :=
  List.drop_eq_getElem_cons h

theorem split_at {α : Type} (l : List α) (q : Nat) : l = l.take q ++ l.drop q := (List.take_append_drop q l).symm

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem nodeStart (hC : NodeCtx tr s ℓ fl) : s < tr.height T_NODE ∧ tr.cell T_NODE s act = 1 := by
  have := hC.bound; have := hC.seg.1
  exact ⟨by omega, by simpa using segAct hL hC (d := 0) (by omega)⟩

/-- The key part `TAG HPL HPF KEY?` of a leaf or extension, then the field after it. -/
theorem keyPart (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s tl + tr.cell T_NODE s te = 1) :
    1 ≤ cv tr T_NODE s hplen ∧ (tr.cell T_NODE s nokey = 1 ↔ cv tr T_NODE s hplen = 1) ∧
    ∃ hq : (if cv tr T_NODE s hplen = 1 then 3 else 4) < fl.length,
      fl.take (if cv tr T_NODE s hplen = 1 then 3 else 4) = keyFL (cv tr T_NODE s hplen) ∧
      fl[(if cv tr T_NODE s hplen = 1 then 3 else 4)].1 = 5 + cv tr T_NODE s hplen ∧
      tr.cell T_NODE s sTAG = 1 ∧ tr.cell T_NODE (s + 1) sHPL = 1 ∧ tr.cell T_NODE (s + 5) sHPF = 1 ∧
      (cv tr T_NODE s hplen ≠ 1 → tr.cell T_NODE (s + 6) sKEY = 1) ∧
      tr.cell T_NODE (s + fl[(if cv tr T_NODE s hplen = 1 then 3 else 4)].1) sVLEN = tr.cell T_NODE s tl ∧
      tr.cell T_NODE (s + fl[(if cv tr T_NODE s hplen = 1 then 3 else 4)].1) sCH = tr.cell T_NODE s te := by
  obtain ⟨h0, f0, sT⟩ := firstField hL hC
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have sT' : tr.cell T_NODE (s + fl[0].1) sTAG = 1 := by rw [f0, Nat.add_zero]; exact sT
  have l0 := (lens hL hC h0).1 sT'
  obtain ⟨h1', e1⟩ := goNext hL hC h0 sT' (by simp [states]) (by decide)
  have h1 : 1 < fl.length := h1'
  have e1' : fl[1].1 = fl[0].1 + fl[0].2 := e1
  have N0 := (nx hL hC h1).1 sT'
  have s1 : tr.cell T_NODE (s + fl[1].1) sHPL = 1 := by rw [show fl[1].1 = fl[0 + 1].1 from rfl, N0.1, ht]
  have l1 := (lens hL hC h1).2.1 s1
  obtain ⟨h2', e2⟩ := goNext hL hC h1 s1 (by simp [states]) (by decide)
  have h2 : 2 < fl.length := h2'
  have e2' : fl[2].1 = fl[1].1 + fl[1].2 := e2
  have s2 : tr.cell T_NODE (s + fl[2].1) sHPF = 1 := (nx hL hC h2).2.1 s1
  have l2 := (lens hL hC h2).2.2.1 s2
  obtain ⟨h3', e3⟩ := goNext hL hC h2 s2 (by simp [states]) (by decide)
  have h3 : 3 < fl.length := h3'
  have e3' : fl[3].1 = fl[2].1 + fl[2].2 := e3
  have N2 := (nx hL hC h3).2.2.1 s2
  have hk := isBool hL hr0 (x := nokey) (by simp [boolCols])
  rcases hk with hk | hk
  · -- a KEY field
    rw [hk] at N2
    have s3 : tr.cell T_NODE (s + fl[3].1) sKEY = 1 := by
      rw [show fl[3].1 = fl[2 + 1].1 from rfl, N2.1]; grind
    have l3 := (lens hL hC h3).2.2.2.1 s3
    have p3 := (hC.fields.field _ (List.getElem_mem h3)).1.pos
    have hh : cv tr T_NODE s hplen ≠ 1 := by omega
    simp only [hh, if_false]
    obtain ⟨h4', e4⟩ := goNext hL hC h3 s3 (by simp [states]) (by decide)
    have h4 : 4 < fl.length := h4'
    have e4' : fl[4].1 = fl[3].1 + fl[3].2 := e4
    have N3 := (nx hL hC h4).2.2.2.1 s3
    refine ⟨by omega, ⟨fun h' => by rw [hk] at h'; exact absurd h' fp_zero_ne_one, fun h' => h'.elim⟩,
      h4, ?_, by omega, sT, ?_, ?_, fun _ => ?_, N3.1, N3.2⟩
    · simp only [keyFL, hh, if_false, take_four h3]
      simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
      exact ⟨Prod.ext f0 l0, Prod.ext (by omega) l1, Prod.ext (by omega) l2, Prod.ext (by omega) (by omega)⟩
    · rwa [show 1 = fl[1].1 by omega]
    · rwa [show 5 = fl[2].1 by omega]
    · rwa [show 6 = fl[3].1 by omega]
  · -- no KEY field: hplen = 1
    have hh1 := (flags hL hr0).1 hk
    have hh : cv tr T_NODE s hplen = 1 := cv_one hh1
    simp only [hh, if_true]
    refine ⟨by omega, ⟨fun _ => trivial, fun _ => hk⟩, h3, ?_, by omega, sT, ?_, ?_, fun h' => absurd rfl h', ?_⟩
    · simp only [keyFL, if_true, take_three h2]
      simp only [List.append_nil, List.cons.injEq, and_true]
      exact ⟨Prod.ext f0 l0, Prod.ext (by omega) l1, Prod.ext (by omega) l2⟩
    · rwa [show 1 = fl[1].1 by omega]
    · rwa [show 5 = fl[2].1 by omega]
    · have := N2.2; rw [hk] at this
      refine ⟨?_, ?_⟩
      · rw [show fl[3].1 = fl[2 + 1].1 from rfl, this.1]; grind
      · rw [show fl[3].1 = fl[2 + 1].1 from rfl, this.2]; grind

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

theorem list_of_fun {fl : List (Nat × Nat)} {n : Nat} (hlen : fl.length = n) (f : Nat → Nat × Nat)
    (h : ∀ i (hi : i < fl.length), fl[i] = f i) : fl = (List.range n).map f := by
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2; rw [h i h1]; simp

theorem drop_of_len {α : Type} {l : List α} {q : Nat} (h : l.length ≤ q) : l.drop q = [] :=
  List.drop_eq_nil_of_le h

/-- Number of present children (bitmap popcount) as a natural. -/
@[irreducible] def popN (tr : Trace Fp) (r : Nat) : Nat := ((List.range 16).map fun i => cv tr T_NODE r (bm i)).sum

theorem eval_popAux (tr : Trace Fp) (r : Nat) (pub : List Fp) (l : List Nat) :
    (sum (l.map fun i => c (bm i))).eval tr T_NODE r pub = (((l.map fun i => cv tr T_NODE r (bm i)).sum : Nat) : Fp) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, eval_sum_cons, eval_c, List.sum_cons, natCast_add, ih]
    rw [cell_eq_cast]

theorem eval_popE (tr : Trace Fp) (r : Nat) (pub : List Fp) :
    popE.eval tr T_NODE r pub = (popN tr r : Fp) := by unfold popN; exact eval_popAux tr r pub _

theorem popN_le {tr : Trace Fp} {r : Nat} (h : ∀ i, i < 16 → cv tr T_NODE r (bm i) ≤ 1) : popN tr r ≤ 16 := by
  unfold popN
  have : ∀ l : List Nat, (∀ i ∈ l, i < 16) → ((l.map fun i => cv tr T_NODE r (bm i)).sum ≤ l.length) := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => intro hl; simp only [List.map_cons, List.sum_cons, List.length_cons]
                     have := h a (hl a (by simp)); have := ih (fun i hi => hl i (by simp [hi])); omega
  have := this (List.range 16) (fun i hi => by simpa using hi); simpa using this

theorem bm_bool {i : Nat} (hi : i < 16) : bm i ∈ boolCols := by
  unfold boolCols; simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩)))

theorem fp_one_sub_zero : (1 : Fp) - 0 = 1 := by decide
theorem fp_lin1 {a b : Fp} (h : a = 1 * b + 0) : a = b := by grind
theorem fp_one_mul_zero {a : Fp} (h : 1 * a = 0) : a = (0 : Nat) := by
  rw [show ((0 : Nat) : Fp) = 0 from rfl]; grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem popN_small {r : Nat} (hr : r < tr.height T_NODE) : popN tr r ≤ 16 :=
  popN_le (fun i hi => cvb hL hr (bm_bool hi))

theorem popNConst (hC : NodeCtx tr s ℓ fl) {d : Nat} (hd : d < ℓ) : popN tr (s + d) = popN tr s := by
  unfold popN; congr 1; apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
  unfold cv; rw [segConst hL hC (x := bm i) (by unfold nodeConst; simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨i, hi, rfl⟩) hd]

theorem lastIdx (hC : NodeCtx tr s ℓ fl) {i : Nat} (hi : i < fl.length)
    (hm : tr.cell T_NODE (s + fl[i].1) sMEM = 1) : fl.length = i + 1 ∧ ℓ = fl[i].1 + 8 := by
  have h1 := memLast hL hC hi hm
  have l := (lens hL hC hi).2.2.2.2.2.2.2.2 hm
  have := hC.fields.last (by omega)
  simp only [show fl.length - 1 = i by omega] at this
  exact ⟨h1.symm, by omega⟩

set_option maxHeartbeats 4000000 in
/-- Branch tail from the `BM` field (index `iB`, offset `o`). -/
theorem brTail (hC : NodeCtx tr s ℓ fl) {iB : Nat} (hiB : iB < fl.length)
    (hbm : tr.cell T_NODE (s + fl[iB].1) sBM = 1) (hbr : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) :
    fl.drop iB = (fl[iB].1, 2) :: ((List.range (popN tr s)).map (fun j => (fl[iB].1 + 2 + 32 * j, 32)) ++
      [(fl[iB].1 + 2 + 32 * popN tr s, 8)]) ∧
    ℓ = fl[iB].1 + 2 + 32 * popN tr s + 8 ∧
    (tr.cell T_NODE s nochild = 1 ↔ popN tr s = 0) ∧
    tr.cell T_NODE (s + (fl[iB].1 + 2 + 32 * popN tr s)) sMEM = 1 ∧
    ∀ j, j < popN tr s → ∃ hj : iB + 1 + j < fl.length, fl[iB + 1 + j] = (fl[iB].1 + 2 + 32 * j, 32) ∧
      tr.cell T_NODE (s + fl[iB + 1 + j].1) sCH = 1 ∧ tr.cell T_NODE (s + fl[iB + 1 + j].1) w = ((j : Nat) : Fp) ∧
      (tr.cell T_NODE (s + fl[iB + 1 + j].1) lastw = 1 ↔ j + 1 = popN tr s) := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have lB := (lens hL hC hiB).2.2.2.2.2.2.1 hbm
  obtain ⟨h1', e1⟩ := goNext hL hC hiB hbm (by simp [states]) (by decide)
  have N := (nx hL hC h1').2.2.2.2.2.2.1 hbm
  have hpop := (flags hL hr0).2.1
  rw [eval_popE] at hpop
  have hpS := popN_small hL hr0
  rcases isBool hL hr0 (x := nochild) (by simp [boolCols]) with hn | hn
  · -- children: a CH run
    rw [hn] at N
    have c0 : tr.cell T_NODE (s + fl[iB + 1].1) sCH = 1 := by rw [N.2, fp_one_sub_zero]
    have hbmCH : tr.cell T_NODE (s + fl[iB].1) sCH = 0 :=
      stOnly hL (x := sBM) (y := sCH) (fieldRow hL hC hiB).1 (fAct hL hC hiB) hbm (by simp [states])
        (by simp [states]) (by decide)
    have w0 := chFirst hL hC h1' hbmCH c0
    obtain ⟨m, hm, R, hlw, hmem, pm⟩ := chRun hL hC h1' c0 w0
    obtain ⟨hlen, hℓ⟩ := lastIdx hL hC hm hmem
    -- m + 1 = pop
    obtain ⟨hjm, cm, wm, -, -⟩ := R m (Nat.le_refl _)
    have hrm := (fieldRow hL hC hjm).1
    have W := (winSlot hL hrm cm).2.2 hlw
    simp only [nWinE, isBr, eval_add, eval_mul, eval_c, eval_popE] at W
    have hdl : fl[iB + 1 + m].1 < ℓ := by
      have hFm := (hC.fields.field _ (List.getElem_mem hjm)); have := hFm.1.pos; have := hFm.2; omega
    rw [fConst hL hC hjm (x := tb1) (by simp [nodeConst]), fConst hL hC hjm (x := tb2) (by simp [nodeConst]),
      fConst hL hC hjm (x := te) (by simp [nodeConst]), wm, hbr, popNConst hL hC hdl] at W
    have hte : tr.cell T_NODE s te = 0 := by
      have := typeSumNat hL hr0 ha0
      have h1 := cv_bool (isBool hL hr0 (x := tb1) (by simp [boolCols]))
      have h2 := cv_bool (isBool hL hr0 (x := tb2) (by simp [boolCols]))
      have e := hbr
      rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add] at e
      have := ofNat_inj (by unfold P; omega) (by unfold P; omega) (e.trans (show (1 : Fp) = ((1 : Nat) : Fp) from rfl))
      exact of_cv_zero (by omega)
    rw [hte] at W
    have hp : m + 1 = popN tr s := by
      have := height_le hL; have := hC.bound
      obtain ⟨-, -, -, pm', -⟩ := R m (Nat.le_refl _)
      apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
      rw [natCast_add]; exact fp_lin1 W
    have hpop0 : popN tr s ≠ 0 := by omega
    have hiB1 : fl[iB + 1].1 = fl[iB].1 + 2 := by rw [e1, lB]
    refine ⟨?_, ?_, ⟨fun h => by rw [hn] at h; exact absurd h fp_zero_ne_one, fun h => absurd h hpop0⟩, ?_, ?_⟩
    · rw [drop_cons_get hiB, List.cons.injEq]
      refine ⟨Prod.ext rfl lB, ?_⟩
      have hlist := list_of_fun (fl := fl.drop (iB + 1)) (n := m + 2) (by simp only [List.length_drop]; omega)
          (fun j => if j ≤ m then (fl[iB].1 + 2 + 32 * j, 32) else (fl[iB].1 + 2 + 32 * (m + 1), 8)) (by
        intro j hj
        simp only [List.getElem_drop, List.length_drop] at hj ⊢
        by_cases hjm' : j ≤ m
        · rw [if_pos hjm']
          obtain ⟨hj', -, -, pj, lj⟩ := R j hjm'
          exact Prod.ext (by show fl[iB + 1 + j].1 = fl[iB].1 + 2 + 32 * j; rw [pj, hiB1]) lj
        · rw [if_neg hjm']
          have : j = m + 1 := by omega
          subst this
          have l8 := (lens hL hC hm).2.2.2.2.2.2.2.2 hmem
          exact Prod.ext (by show fl[iB + 1 + m + 1].1 = _; rw [pm, hiB1]) l8)
      rw [hlist, List.range_succ, List.map_append, ← hp]
      simp only [List.map_cons, List.map_nil, if_neg (show ¬ (m + 1 ≤ m) by omega)]
      apply congrArg (· ++ _)
      apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj; rw [if_pos (by omega)]
    · rw [hℓ, pm, hiB1, ← hp]
    · rw [← hp, show fl[iB].1 + 2 + 32 * (m + 1) = fl[iB + 1 + m + 1].1 by rw [pm, hiB1]]; exact hmem
    · intro j hj
      obtain ⟨hj', cj, wj, pj, lj⟩ := R j (by omega)
      refine ⟨hj', Prod.ext (by rw [pj, hiB1]) lj, cj, wj, ⟨fun h => ?_, fun h => ?_⟩⟩
      · apply Classical.byContradiction; intro hne
        -- an earlier window with lastw = 1 ends the run
        have hjm2 : j < m := by omega
        obtain ⟨hj2, e2⟩ := goNext hL hC hj' cj (by simp [states]) (by decide)
        have N2 := (nx hL hC hj2).2.2.2.2.2.2.2 cj
        rw [h] at N2
        obtain ⟨hj1, cj1, wj1, pj1, lj1⟩ := R (j + 1) (by omega)
        have : tr.cell T_NODE (s + fl[iB + 1 + (j + 1)].1) sMEM = 0 :=
          stOnly hL (x := sCH) (y := sMEM) (fieldRow hL hC hj1).1 (fAct hL hC hj1) cj1 (by simp [states])
            (by simp [states]) (by decide)
        have this' : tr.cell T_NODE (s + fl[iB + 1 + j + 1].1) sMEM = 0 := this
        rw [this'] at N2; exact fp_zero_ne_one N2.2
      · have : j = m := by omega
        subst this; exact hlw
  · -- no children
    have hp0 : popN tr s = 0 := by
      rw [hn] at hpop
      exact ofNat_inj (by unfold P; omega) (by unfold P; omega) (fp_one_mul_zero hpop)
    rw [hn] at N
    have hmem : tr.cell T_NODE (s + fl[iB + 1].1) sMEM = 1 := N.1
    obtain ⟨hlen, hℓ⟩ := lastIdx hL hC h1' hmem
    have hiB1 : fl[iB + 1].1 = fl[iB].1 + 2 := by rw [e1, lB]
    refine ⟨?_, by rw [hℓ, hiB1, hp0], ⟨fun _ => hp0, fun _ => hn⟩, by rw [hp0]; simpa [hiB1] using hmem,
      fun j hj => by omega⟩
    rw [drop_cons_get hiB, drop_cons_get h1', drop_of_len (by omega), hp0]
    have l8 := (lens hL hC h1').2.2.2.2.2.2.2.2 hmem
    simp only [List.range_zero, List.map_nil, List.nil_append, List.cons.injEq, and_true]
    refine ⟨Prod.ext rfl lB, Prod.ext ?_ l8⟩
    simp [hiB1]

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

theorem fp_add_zero' {a : Fp} (h : a = 1 + 0) : a = 1 := by grind
theorem fp_zero_add' {a : Fp} (h : a = 0 + 1) : a = 1 := by grind
theorem fp_eq_one_of_sum {a b : Fp} (h : a + b = 1) (hb : b = 0) : a = 1 := by grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem typeZeros (hC : NodeCtx tr s ℓ fl) {x : Nat} (hx : x ∈ [tl, te, tb1, tb2])
    (h1 : tr.cell T_NODE s x = 1) {y : Nat} (hy : y ∈ [tl, te, tb1, tb2]) (hne : y ≠ x) :
    tr.cell T_NODE s y = 0 := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  exact typeOnly hL hr0 ha0 h1 hx hy hne

set_option maxHeartbeats 1000000 in
theorem leafFields (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s tl = 1) :
    1 ≤ cv tr T_NODE s hplen ∧ (tr.cell T_NODE s nokey = 1 ↔ cv tr T_NODE s hplen = 1) ∧
    fl = leafFL (cv tr T_NODE s hplen) ∧ ℓ = 49 + cv tr T_NODE s hplen ∧
    tr.cell T_NODE s sTAG = 1 ∧ tr.cell T_NODE (s + 1) sHPL = 1 ∧ tr.cell T_NODE (s + 5) sHPF = 1 ∧
    (cv tr T_NODE s hplen ≠ 1 → tr.cell T_NODE (s + 6) sKEY = 1) ∧
    tr.cell T_NODE (s + (5 + cv tr T_NODE s hplen)) sVLEN = 1 ∧
    tr.cell T_NODE (s + (9 + cv tr T_NODE s hplen)) sVH = 1 ∧
    tr.cell T_NODE (s + (41 + cv tr T_NODE s hplen)) sMEM = 1 := by
  have hte := typeZeros hL hC (x := tl) (y := te) (by simp) ht (by simp) (by decide)
  obtain ⟨hh1, hnk, hq, htake, pq, sT, sH, sF, sK, sV, -⟩ := keyPart hL hC (by rw [ht, hte]; exact fp_add_zero' rfl)
  generalize (if cv tr T_NODE s hplen = 1 then 3 else 4) = q at *
  generalize cv tr T_NODE s hplen = h at *
  rw [ht] at sV
  have l0 := (lens hL hC hq).2.2.2.2.1 sV
  obtain ⟨hq1', e1⟩ := goNext hL hC hq sV (by simp [states]) (by decide)
  have hq1 : q + 1 < fl.length := hq1'
  have s1 : tr.cell T_NODE (s + fl[q + 1].1) sVH = 1 := (nx hL hC hq1).2.2.2.2.1 sV
  have l1 := (lens hL hC hq1).2.2.2.2.2.1 s1
  obtain ⟨hq2', e2⟩ := goNext hL hC hq1 s1 (by simp [states]) (by decide)
  have hq2 : q + 2 < fl.length := hq2'
  have e2' : fl[q + 2].1 = fl[q + 1].1 + fl[q + 1].2 := e2
  have s2 : tr.cell T_NODE (s + fl[q + 2].1) sMEM = 1 := by
    have := ((nx hL hC hq2).2.2.2.2.2.1 s1).1; rw [ht] at this; exact this
  obtain ⟨hlen, hℓ⟩ := lastIdx hL hC hq2 s2
  have l2 := (lens hL hC hq2).2.2.2.2.2.2.2.2 s2
  refine ⟨hh1, hnk, ?_, by omega, sT, sH, sF, sK, by rw [← pq]; exact sV,
    by rw [show 9 + h = fl[q + 1].1 by omega]; exact s1, by rw [show 41 + h = fl[q + 2].1 by omega]; exact s2⟩
  rw [split_at fl q, htake, drop_cons_get hq, drop_cons_get hq1, drop_cons_get hq2, drop_of_len (by omega)]
  unfold leafFL
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq,
    List.cons.injEq, and_true]
  exact ⟨Prod.ext pq l0, Prod.ext (by omega) l1, Prod.ext (by omega) l2⟩

set_option maxHeartbeats 1000000 in
theorem extFields (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s te = 1) :
    1 ≤ cv tr T_NODE s hplen ∧ (tr.cell T_NODE s nokey = 1 ↔ cv tr T_NODE s hplen = 1) ∧
    fl = extFL (cv tr T_NODE s hplen) ∧ ℓ = 45 + cv tr T_NODE s hplen ∧
    tr.cell T_NODE s sTAG = 1 ∧ tr.cell T_NODE (s + 1) sHPL = 1 ∧ tr.cell T_NODE (s + 5) sHPF = 1 ∧
    (cv tr T_NODE s hplen ≠ 1 → tr.cell T_NODE (s + 6) sKEY = 1) ∧
    tr.cell T_NODE (s + (5 + cv tr T_NODE s hplen)) sCH = 1 ∧
    tr.cell T_NODE (s + (37 + cv tr T_NODE s hplen)) sMEM = 1 := by
  have htl := typeZeros hL hC (x := te) (y := tl) (by simp) ht (by simp) (by decide)
  obtain ⟨hh1, hnk, hq, htake, pq, sT, sH, sF, sK, -, sC⟩ := keyPart hL hC (by rw [ht, htl]; exact fp_zero_add' rfl)
  generalize (if cv tr T_NODE s hplen = 1 then 3 else 4) = q at *
  generalize cv tr T_NODE s hplen = h at *
  rw [ht] at sC
  have l0 := (lens hL hC hq).2.2.2.2.2.2.2.1 sC
  have w0 := (winSlot hL (fieldRow hL hC hq).1 sC).2.1 (by rw [fConst hL hC hq (by simp [nodeConst]), ht])
  obtain ⟨hq1', e1⟩ := goNext hL hC hq sC (by simp [states]) (by decide)
  have hq1 : q + 1 < fl.length := hq1'
  have N := (nx hL hC hq1).2.2.2.2.2.2.2 sC
  have hlw : tr.cell T_NODE (s + fl[q].1) lastw = 1 := by
    rcases isBool hL (fieldRow hL hC hq).1 (x := lastw) (by simp [boolCols]) with h0 | h0
    · exfalso
      rw [h0] at N
      have c1 : tr.cell T_NODE (s + fl[q + 1].1) sCH = 1 := fp_eq_one_of_sum N.1 N.2
      have W := chStep hL hC hq1 sC c1
      have w1 := (winSlot hL (fieldRow hL hC hq1).1 c1).2.1 (by rw [fConst hL hC hq1 (by simp [nodeConst]), ht])
      rw [w1, w0] at W
      exact fp_zero_ne_one (by rw [W]; decide)
    · exact h0
  rw [hlw] at N
  have s1 : tr.cell T_NODE (s + fl[q + 1].1) sMEM = 1 := N.2
  obtain ⟨hlen, hℓ⟩ := lastIdx hL hC hq1 s1
  have l1 := (lens hL hC hq1).2.2.2.2.2.2.2.2 s1
  refine ⟨hh1, hnk, ?_, by omega, sT, sH, sF, sK, by rw [← pq]; exact sC,
    by rw [show 37 + h = fl[q + 1].1 by omega]; exact s1⟩
  rw [split_at fl q, htake, drop_cons_get hq, drop_cons_get hq1, drop_of_len (by omega)]
  unfold extFL
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq,
    List.cons.injEq, and_true]
  exact ⟨Prod.ext pq l0, Prod.ext (by omega) l1⟩

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

set_option maxHeartbeats 1000000 in
/-- Branch field list (`o = 1` for `b1`, `37` for `b2`). -/
theorem brFields (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) :
    let o := if tr.cell T_NODE s tb2 = 1 then 37 else 1
    fl = brFL o (popN tr s) ∧ ℓ = o + 2 + 32 * popN tr s + 8 ∧
    tr.cell T_NODE s sTAG = 1 ∧ (o = 37 → tr.cell T_NODE (s + 1) sVLEN = 1 ∧ tr.cell T_NODE (s + 5) sVH = 1) ∧
    tr.cell T_NODE (s + o) sBM = 1 ∧
    (tr.cell T_NODE s nochild = 1 ↔ popN tr s = 0) ∧
    tr.cell T_NODE (s + (o + 2 + 32 * popN tr s)) sMEM = 1 ∧
    ∀ j, j < popN tr s → tr.cell T_NODE (s + (o + 2 + 32 * j)) sCH = 1 ∧
      tr.cell T_NODE (s + (o + 2 + 32 * j)) w = ((j : Nat) : Fp) ∧
      (tr.cell T_NODE (s + (o + 2 + 32 * j)) lastw = 1 ↔ j + 1 = popN tr s) := by
  intro o
  obtain ⟨h0, f0, sT⟩ := firstField hL hC
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have sT' : tr.cell T_NODE (s + fl[0].1) sTAG = 1 := by rw [f0, Nat.add_zero]; exact sT
  have l0 := (lens hL hC h0).1 sT'
  obtain ⟨h1', e1⟩ := goNext hL hC h0 sT' (by simp [states]) (by decide)
  have h1 : 1 < fl.length := h1'
  have e1' : fl[1].1 = fl[0].1 + fl[0].2 := e1
  have N0 := (nx hL hC h1).1 sT'
  rcases isBool hL hr0 (x := tb2) (by simp [boolCols]) with h2 | h2
  · -- b1
    have ho : o = 1 := by simp only [o, h2]; decide
    have h1' : tr.cell T_NODE s tb1 = 1 := by rw [h2] at hb; grind
    have sB : tr.cell T_NODE (s + fl[1].1) sBM = 1 := by rw [N0.2.1, h1']
    obtain ⟨hD, hℓ, hnc, hM, hW⟩ := brTail hL hC h1 sB hb
    have p1 : fl[1].1 = 1 := by omega
    rw [p1] at hD hℓ hM hW
    rw [ho]
    refine ⟨?_, hℓ, sT, fun h => absurd h (by decide), by rw [← p1]; exact sB, hnc, hM, fun j hj => ?_⟩
    · rw [split_at fl 1, hD]
      unfold brFL
      simp [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
      exact Prod.ext f0 l0
    · obtain ⟨hj, ej, cj, wj, lj⟩ := hW j hj
      have : fl[1 + 1 + j].1 = 1 + 2 + 32 * j := by rw [ej]
      rw [this] at cj wj lj
      exact ⟨cj, wj, lj⟩
  · -- b2
    have ho : o = 37 := by simp only [o, h2]; decide
    have sV : tr.cell T_NODE (s + fl[1].1) sVLEN = 1 := by rw [N0.2.2, h2]
    have l1 := (lens hL hC h1).2.2.2.2.1 sV
    obtain ⟨h2', e2⟩ := goNext hL hC h1 sV (by simp [states]) (by decide)
    have h2'' : 2 < fl.length := h2'
    have e2' : fl[2].1 = fl[1].1 + fl[1].2 := e2
    have sH : tr.cell T_NODE (s + fl[2].1) sVH = 1 := (nx hL hC h2'').2.2.2.2.1 sV
    have l2 := (lens hL hC h2'').2.2.2.2.2.1 sH
    obtain ⟨h3', e3⟩ := goNext hL hC h2'' sH (by simp [states]) (by decide)
    have h3 : 3 < fl.length := h3'
    have e3' : fl[3].1 = fl[2].1 + fl[2].2 := e3
    have sB : tr.cell T_NODE (s + fl[3].1) sBM = 1 := by rw [((nx hL hC h3).2.2.2.2.2.1 sH).2, h2]
    obtain ⟨hD, hℓ, hnc, hM, hW⟩ := brTail hL hC h3 sB hb
    have p3 : fl[3].1 = 37 := by omega
    rw [p3] at hD hℓ hM hW
    rw [ho]
    refine ⟨?_, hℓ, sT, fun _ => ⟨by rw [show 1 = fl[1].1 by omega]; exact sV, by rw [show 5 = fl[2].1 by omega]; exact sH⟩,
      by rw [← p3]; exact sB, hnc, hM, fun j hj => ?_⟩
    · rw [split_at fl 3, hD, take_three h2'']
      unfold brFL
      simp only [show (37 : Nat) ≠ 1 by decide, if_false, List.cons_append, List.nil_append, List.singleton_append,
        List.append_assoc, List.cons.injEq, true_and]
      exact ⟨Prod.ext f0 l0, Prod.ext (by omega) l1, Prod.ext (by omega) l2, trivial⟩
    · obtain ⟨hj, ej, cj, wj, lj⟩ := hW j hj
      have : fl[3 + 1 + j].1 = 37 + 2 + 32 * j := by rw [ej]
      rw [this] at cj wj lj
      exact ⟨cj, wj, lj⟩

end ZkFormal.Near.NodeProof
