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
