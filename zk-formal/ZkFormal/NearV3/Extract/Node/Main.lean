import ZkFormal.NearV3.Extract.Node.ViewLists

/-!
# ZkFormal.Near.Extract.NodeMain — the node table's traffic is its view's traffic
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL

theorem stateZero {r : Nat} (hr : r < tr.height T_NODE) (ha : tr.cell T_NODE r act = 0) {x : Nat} (hx : x ∈ states) :
    tr.cell T_NODE r x = 0 := by
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
  have S : cv tr T_NODE r sTAG + (cv tr T_NODE r sHPL + (cv tr T_NODE r sHPF + (cv tr T_NODE r sKEY +
      (cv tr T_NODE r sVLEN + (cv tr T_NODE r sVH + (cv tr T_NODE r sBM + (cv tr T_NODE r sCH +
      (cv tr T_NODE r sMEM + 0)))))))) = 0 := by
    apply fp_cast_eq (b := 0) (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add]
    have z0 : ((0 : Nat) : Fp) = 0 := rfl
    simp only [z0] at h ⊢; exact h
  apply of_cv_zero
  simp only [states, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
/-- Inactive rows emit nothing, except the `SUM` row's `SIZE` send. -/
theorem padRowT {r : Nat} (hr : r < tr.height T_NODE) (ha : tr.cell T_NODE r act = 0)
    (bb : Nat) (sd : Bool) (hs : ¬ (bb = B_SIZE ∧ sd = true)) : rowT tr pub r bb sd = [] := by
  have z := fun x (hx : x ∈ states) => stateZero hL hr ha hx
  have hnf : tr.cell T_NODE r nf = 0 := bool01 hL hr (by simp [boolCols]) (fun h => by
    have := ((rowFacts hL hr).2.2.2.1 h).1; rw [ha] at this; exact fp_zero_ne_one this)
  have F := flags hL hr
  have hdup : tr.cell T_NODE r dup = 0 := by have := F.2.2.2.2.1; rw [ha] at this; grind
  have hhd : tr.cell T_NODE r NodeV3.hd = 0 := by have := F.2.2.2.2.2.1; rw [ha] at this; grind
  have G := linkGates hL hr
  simp only at G
  have M := winMisc hL hr
  have hgP : tr.cell T_NODE r gP = 0 := by rw [G.1, z sCH (by simp [states])]; grind
  have hgD : tr.cell T_NODE r gD = 0 := by rw [M.2.1, hgP, z sVH (by simp [states])]; grind
  have hgDp : tr.cell T_NODE r gDp = 0 := by rw [G.2.2.2.2.2.1, hgP, hgD]; grind
  have hgV : tr.cell T_NODE r gV = 0 := by rw [G.2.1, hnf]; grind
  have hgS : tr.cell T_NODE r gS = 0 := by rw [G.2.2.2.1, z sCH (by simp [states]), z sVH (by simp [states])]; grind
  have hgBm : tr.cell T_NODE r gBm = 0 := by rw [G.2.2.2.2.2.2.1, z sBM (by simp [states])]; grind
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  have hgA : tr.cell T_NODE r gA = 0 := by
    rw [GA, z sKEY (by simp [states]), z sHPF (by simp [states]), z sCH (by simp [states]), z sVH (by simp [states])]
    grind
  have hgB : tr.cell T_NODE r gB = 0 := by rw [GB, z sKEY (by simp [states]), z sMEM (by simp [states])]; grind
  by_cases b0 : bb = B_BYTES
  · subst b0; cases sd
    · exact rowT_bytesR r
    · rw [rowT_bytes, ha]; simp [gate]
  by_cases b1 : bb = B_DIGEST
  · subst b1; cases sd
    · rw [rowT_digest, hgD, hgDp]; simp [gate]
    · exact rowT_digestS r
  by_cases b2 : bb = B_PARENT
  · subst b2; cases sd
    · rw [rowT_parentR, hnf]; simp [gate]
    · rw [rowT_parentS, hgP]; simp [gate]
  by_cases b3 : bb = B_VPARENT
  · subst b3; cases sd
    · exact rowT_vparentR r
    · rw [rowT_vparentS, hgD, hgP, show (0 : Fp) - 0 = 0 by decide]; simp [gate]
  by_cases b4 : bb = B_EDGE
  · subst b4; cases sd
    · rw [rowT_edgeR, hgA, hgB]; simp [gate]
    · rw [rowT_edgeS, hgA, hgB]; simp [gate]
  by_cases b5 : bb = B_BMAP
  · subst b5; cases sd
    · rw [rowT_bmapR, hgBm]; simp [gate]
    · rw [rowT_bmapS, hgBm]; simp [gate]
  by_cases b6 : bb = B_DIGS
  · subst b6; cases sd
    · exact rowT_digsR r
    · rw [rowT_digsS, hgS]; simp [gate]
  by_cases b7 : bb = B_DUP
  · subst b7; cases sd
    · rw [rowT_dupR, hgV]; simp [gate]
    · exact rowT_dupS r
  by_cases b8 : bb = B_ENT
  · subst b8; cases sd
    · rw [rowT_entR, hdup]; simp [gate]
    · rw [rowT_entS, hhd]; simp [gate]
  by_cases b9 : bb = B_SIZE
  · subst b9; cases sd
    · exact rowT_sizeR r
    · exact absurd ⟨rfl, rfl⟩ hs
  exact rowT_other r bb sd ⟨b0, b1, b2, b4, b5, b6, b9, b7, b8, b3⟩

/-- A non-`SUM` row is silent on `SIZE`. -/
theorem sizeQuiet {r : Nat} (hs : tr.cell T_NODE r sumr = 0) (sd : Bool) : rowT tr pub r B_SIZE sd = [] := by
  cases sd
  · exact rowT_sizeR r
  · rw [rowT_sizeS, hs]; simp [gate]

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near


def viewOf (tr : Trace Fp) (pub : List Fp) (segs : List (Nat × Nat)) : List NodeS3 :=
  segs.map fun p => nodeSOf tr pub p.1 p.2

/-- Bytes of the non-duplicate records, by segments. -/
def sizeOf (tr : Trace Fp) (segs : List (Nat × Nat)) : Nat :=
  (segs.map fun p => if cv tr T_NODE p.1 dup = 1 then 0 else p.2).sum

theorem sum_flatMap_map (l : List (Nat × Nat)) (h : Nat × Nat → List Nat) (g : Nat → Nat) :
    ((l.flatMap h).map g).sum = (l.map fun p => ((h p).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.map_append, List.sum_append, ih]

theorem sum_range'_const (g : Nat → Nat) (c : Nat) : ∀ (s ℓ : Nat), (∀ d, d < ℓ → g (s + d) = c) →
    ((List.range' s ℓ).map g).sum = ℓ * c := by
  intro s ℓ; induction ℓ with
  | zero => intro _; simp
  | succ ℓ ih =>
    intro h
    rw [range'_succ', List.map_append, List.sum_append, ih (fun d hd => h d (by omega))]
    have := h ℓ (by omega)
    simp [this, Nat.succ_mul]

theorem fp_bool_mul {a d : Fp} {an dn : Nat} (ha : a = ((an : Nat) : Fp)) (hd : d = ((dn : Nat) : Fp)) (han : an ≤ 1)
    (hdn : dn ≤ 1) : a * (1 - d) = ((an * (1 - dn) : Nat) : Fp) := by
  subst ha hd
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp han with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdn with h' | h' <;> subst h h' <;> decide

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {segs : List (Nat × Nat)}

theorem NodeSegs.lenLt (hS : NodeSegs tr segs) : segs.length ≤ tr.height T_NODE := by
  have hb : ∀ q (hq : q < segs.length), q < segs[q].1 + segs[q].2 := by
    intro q; induction q with
    | zero => intro hq; have := (hS.seg' hL hq).1; omega
    | succ q ih => intro hq; have := hS.next hL hq; have := ih (by omega); have := (hS.seg' hL hq).1; omega
  rcases Nat.eq_zero_or_pos segs.length with h | h
  · omega
  · have := hb (segs.length - 1) (by omega); have := hS.bound' hL (n := segs.length - 1) (by omega); omega

/-- The `SUM` row: the row after the last node. -/
theorem NodeSegs.sumRow (hS : NodeSegs tr segs) :
    segEnd 0 segs < tr.height T_NODE ∧ tr.cell T_NODE (segEnd 0 segs) sumr = 1 ∧
    ∀ r, segEnd 0 segs < r → r < tr.height T_NODE → tr.cell T_NODE r sumr = 0 := by
  obtain ⟨h0, -⟩ := hS.first hL
  have hE := hS.endEq hL h0
  have hs := hS.seg' hL (n := segs.length - 1) (by omega)
  have hp := hs.1
  have hact : tr.cell T_NODE (segEnd 0 segs - 1) act = 1 := by
    have := hs.2.2.2.1 (segEnd 0 segs - 1) (by omega) (by omega); rwa [one_iff] at this
  have hH := height_ge hL
  have hlt : segEnd 0 segs < tr.height T_NODE := by
    rcases Nat.lt_or_ge (segEnd 0 segs) (tr.height T_NODE) with h | h
    · exact h
    · exfalso
      have := hS.endLe
      have hl := lastRow hL (by omega)
      rw [show tr.height T_NODE - 1 = segEnd 0 segs - 1 by omega, hact] at hl
      exact fp_one_ne_zero hl
  have hl : tr.cell T_NODE (segEnd 0 segs - 1) nl = 1 := by
    have := hs.2.2.1; rw [one_iff] at this; rwa [show segEnd 0 segs - 1 = segs[segs.length - 1].1 +
      segs[segs.length - 1].2 - 1 by omega]
  have A := (atEnd hL (r := segEnd 0 segs - 1) (by omega) hl).1
  rw [show segEnd 0 segs - 1 + 1 = segEnd 0 segs by omega] at A
  have hpad := zero_of hL hlt (by simp [boolCols]) (hS.pad (segEnd 0 segs) (by omega) hlt)
  rw [hpad] at A
  have h1 : tr.cell T_NODE (segEnd 0 segs) sumr = 1 := by grind
  refine ⟨hlt, h1, ?_⟩
  have gen : ∀ k, segEnd 0 segs + 1 + k < tr.height T_NODE → tr.cell T_NODE (segEnd 0 segs + 1 + k) sumr = 0 := by
    intro k; induction k with
    | zero =>
      intro hk
      have := afterInactive hL (r := segEnd 0 segs) (by omega) hpad
      rw [this.2.1, if_pos h1]
    | succ k ih =>
      intro hk
      have ha := zero_of hL (r := segEnd 0 segs + 1 + k) (by omega) (by simp [boolCols])
        (hS.pad _ (by omega) (by omega))
      have := (afterInactive hL (r := segEnd 0 segs + 1 + k) (by omega) ha).2.2 (ih (by omega))
      rwa [show segEnd 0 segs + 1 + (k + 1) = segEnd 0 segs + 1 + k + 1 by omega]
  intro r h1 h2
  have := gen (r - (segEnd 0 segs + 1)) (by omega)
  rwa [show segEnd 0 segs + 1 + (r - (segEnd 0 segs + 1)) = r by omega] at this

/-- The size counter at the `SUM` row. -/
theorem NodeSegs.szSum (hS : NodeSegs tr segs) :
    tr.cell T_NODE (segEnd 0 segs) sz = ((sizeOf tr segs : Nat) : Fp) := by
  have hlt := (hS.sumRow hL).1
  let g := fun i => cv tr T_NODE i act * (1 - cv tr T_NODE i dup)
  have step : ∀ r, r ≤ segEnd 0 segs → tr.cell T_NODE r sz = ((((List.range r).map g).sum : Nat) : Fp) := by
    intro r; induction r with
    | zero => intro _; rw [(firstRow hL (by omega)).2.2.2]; rfl
    | succ r ih =>
      intro hr
      rw [sizeFacts hL (r := r) (by omega) (by omega), ih (by omega), List.range_succ, List.map_append,
        List.sum_append, natCast_add]
      congr 1
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      exact fp_bool_mul (cell_eq_cast tr T_NODE r act) (cell_eq_cast tr T_NODE r dup)
        (cvb hL (by omega) (by simp [boolCols])) (cvb hL (by omega) (by simp [boolCols]))
  rw [step _ (Nat.le_refl _)]
  congr 1
  rw [List.range_eq_range', show segEnd 0 segs = segEnd 0 segs - 0 by omega, range'_segs segs 0 hS.consec,
    sum_flatMap_map]
  unfold sizeOf
  congr 1
  apply List.map_congr_left; intro p hp
  obtain ⟨fl, hC⟩ := hS.ctx hL hp
  have hd := cvb hL (nodeStart hL hC).1 (x := dup) (by simp [boolCols])
  rw [sum_range'_const g (1 - cv tr T_NODE p.1 dup) p.1 p.2 (fun d hd' => by
    show cv tr T_NODE (p.1 + d) act * (1 - cv tr T_NODE (p.1 + d) dup) = _
    rw [cv_one (segAct hL hC hd'), show cv tr T_NODE (p.1 + d) dup = cv tr T_NODE p.1 dup by
      unfold cv; rw [segConst hL hC (by simp [nodeConst]) hd']]
    omega)]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with h | h <;> simp [h]

theorem viewOf_size (hS : NodeSegs tr segs) :
    (((viewOf tr pub segs).filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum = sizeOf tr segs := by
  have hlen : ∀ p ∈ segs, ((nodeVOf tr p.1).ser false).length = p.2 := by
    intro p hp; obtain ⟨fl, hC⟩ := hS.ctx hL hp
    rw [← (nodeSer hL hC).1, rowsB_length]
  unfold viewOf sizeOf
  clear hS
  induction segs with
  | nil => rfl
  | cons p rest ih =>
    rw [List.map_cons, List.filter_cons, List.map_cons, List.sum_cons,
      ← ih (fun q hq => hlen q (by simp [hq]))]
    show _ = (if cv tr T_NODE p.1 dup = 1 then 0 else p.2) + _
    by_cases h : cv tr T_NODE p.1 dup = 1
    · simp [nodeSOf, h]
    · simp [nodeSOf, h, hlen p (by simp)]

theorem rowsEq (hS : NodeSegs tr segs) (bb : Nat) (sd : Bool) (hs : ¬ (bb = B_SIZE ∧ sd = true)) :
    (List.range (tr.height T_NODE)).flatMap (fun r => rowT tr pub r bb sd) =
      (List.range segs.length).flatMap fun q =>
        (List.range' (segs.getD q default).1 (segs.getD q default).2).flatMap fun r => rowT tr pub r bb sd := by
  rw [flatMap_rows_segs _ segs _ hS.consec hS.endLe (fun r h1 h2 => padRowT hL h2
    (zero_of hL h2 (by simp [boolCols]) (hS.pad r h1 h2)) bb sd hs)]
  exact flatMap_eq_range segs _

theorem rowsSize (hS : NodeSegs tr segs) :
    (List.range (tr.height T_NODE)).flatMap (fun r => rowT tr pub r B_SIZE true) =
      [[0, ((sizeOf tr segs : Nat) : Fp)]] := by
  obtain ⟨hlt, h1, h2⟩ := hS.sumRow hL
  have e1 : List.range (tr.height T_NODE) = List.range' 0 (segEnd 0 segs - 0) ++
      ([segEnd 0 segs] ++ List.range' (segEnd 0 segs + 1) (tr.height T_NODE - segEnd 0 segs - 1)) := by
    rw [List.range_eq_range', Nat.sub_zero, range'_split _ _ (Nat.le_of_lt hlt),
      show tr.height T_NODE - segEnd 0 segs = (tr.height T_NODE - segEnd 0 segs - 1) + 1 by omega, List.range'_succ]
    rfl
  rw [e1, List.flatMap_append, List.flatMap_append, range'_segs segs 0 hS.consec, List.flatMap_assoc]
  rw [flatMap_eq_nil' (l := segs) (fun p hp => by obtain ⟨fl, hC⟩ := hS.ctx hL hp; exact nodeSize hL hC true)]
  rw [flatMap_eq_nil' (l := List.range' _ _) (fun r hr => by
    rw [List.mem_range'_1] at hr; exact sizeQuiet hL (h2 r (by omega) (by omega)) true)]
  rw [List.flatMap_singleton, rowT_sizeS, h1, hS.szSum hL]
  simp [gate]

theorem nodePerm (hS : NodeSegs tr segs) (bb : Nat) :
    ((List.range (tr.height T_NODE)).flatMap (fun r => rowT tr pub r bb true)).Perm
      ((nodeSends3 (viewOf tr pub segs) bb).map Msg.toFp) ∧
    ((List.range (tr.height T_NODE)).flatMap (fun r => rowT tr pub r bb false)).Perm
      ((nodeRecvs3 (viewOf tr pub segs) bb).map Msg.toFp) := by
  have hlen : (viewOf tr pub segs).length = segs.length := by simp [viewOf]
  have hget : ∀ q (hq : q < segs.length), (viewOf tr pub segs).getD q default = nodeSOf tr pub segs[q].1 segs[q].2 := by
    intro q hq; rw [getD_eq_getElem' _ _ (by rw [hlen]; exact hq)]; simp [viewOf]
  have hH := hS.lenLt hL
  have hHP : tr.height T_NODE < P := by have := height_le hL; unfold P; omega
  have per : ∀ q (hq : q < segs.length),
      ((List.range' segs[q].1 segs[q].2).flatMap (fun r => rowT tr pub r bb true)).Perm
        ((pnSend q (nodeSOf tr pub segs[q].1 segs[q].2) bb).map Msg.toFp) ∧
      ((List.range' segs[q].1 segs[q].2).flatMap (fun r => rowT tr pub r bb false)).Perm
        ((pnRecv q (nodeSOf tr pub segs[q].1 segs[q].2) bb).map Msg.toFp) := fun q hq => by
    obtain ⟨fl, hC⟩ := hS.ctx hL (List.getElem_mem hq)
    exact nodeAll hL hC (hS.nid hL q hq) (by omega) (hS.posAt hL hq) bb
  constructor
  · by_cases hb : bb = B_SIZE
    · subst hb
      rw [rowsSize hL hS]
      unfold nodeSends3
      simp only [show ¬ B_SIZE = B_BYTES by decide, show ¬ B_SIZE = B_PARENT by decide,
        show ¬ B_SIZE = B_VPARENT by decide, show ¬ B_SIZE = B_EDGE by decide, show ¬ B_SIZE = B_BMAP by decide,
        show ¬ B_SIZE = B_DIGS by decide, show ¬ B_SIZE = B_ENT by decide, if_false, if_true]
      rw [viewOf_size hL hS]
      simp [Msg.toFp, ← natCast_eq]
      try rfl
    · rw [rowsEq hL hS bb true (fun h => hb h.1), sends_eq _ _ hb, hlen, List.map_flatMap]
      apply perm_flatMap_congr'; intro q hq; rw [List.mem_range] at hq
      rw [getD_eq_getElem' _ _ hq, hget q hq]; exact (per q hq).1
  · rw [rowsEq hL hS bb false (fun h => Bool.false_ne_true h.2), recvs_eq, hlen, List.map_flatMap]
    apply perm_flatMap_congr'; intro q hq; rw [List.mem_range] at hq
    rw [getD_eq_getElem' _ _ hq, hget q hq]; exact (per q hq).2

theorem nodeTrafficOf (hS : NodeSegs tr segs) :
    TableTraffic NodeV3.interactions tr T_NODE pub (nodeTraffic3 (viewOf tr pub segs)) := by
  intro bb m
  rw [tableBusCount_eq, tableBusCount_eq]
  exact ⟨(nodePerm hL hS bb).1.count_eq m, (nodePerm hL hS bb).2.count_eq m⟩

end ZkFormal.NearV3.NodeProof3
