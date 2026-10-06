import ZkFormal.NearV3.Render.Node.TEdge4
import ZkFormal.NearV3.Render.Node.Bool

/-!
# ZkFormal.NearV3.Render.Node.Traffic — **the honest `nodeV3` table has the traffic `nodeTraffic3 vs`**

Every row's traffic is `rowN` of its cells (`rowT_eq`); node rows group into records
(`nodes_flat`), each record's messages are (up to order) its part of `nodeSends3` /
`nodeRecvs3` (`rec_*`), the `SUM` row sends `SIZE [0, total]` and padding is silent.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

theorem gate_le3 (vs : List NodeS3) (H q col : Nat)
    (hcol : col = 0 ∨ col = 1 ∨ col = 3 ∨ col = 142 ∨ col = 143 ∨ col = 144 ∨ col = 145 ∨ col = 160 ∨ col = 170 ∨
      col = 171 ∨ col = 181 ∨ col = 183 ∨ col = 184) :
    cell vs H q col ≤ 1 := by
  have hb : ∀ x ∈ NodeV3.boolCols, cell vs H q x ≤ 1 := fun x hx => cell_bool vs H q hx
  apply hb
  rcases hcol with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem vs_le (vs : List NodeS3) (H q : Nat) :
    cell vs H q 143 ≤ cell vs H q 142 ∧ cell vs H q 142 - cell vs H q 143 ≤ 1 := by
  have hnat : cell vs H q 142 = cell vs H q 143 ∨ (cell vs H q 142 = 1 ∧ cell vs H q 143 = 0) := by
    simp only [NodeGen3.cell]
    split
    · rw [Rc.c142, Rc.c143]
      generalize digOf _ _ = dd
      rcases dd with _ | ⟨a, b', c'⟩
      · simp
      · cases c' <;> simp
    · split <;> simp [sumCell, padCell]
  omega

theorem perm_eq_r {α : Type} {a b c : List α} (h : a.Perm b) (e : b = c) : a.Perm c := e ▸ h

theorem sum_filter (vs : List NodeS3) :
    (vs.map fun s => if s.dup then 0 else (s.v.ser false).length).sum =
      ((vs.filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum := by
  induction vs with
  | nil => rfl
  | cons s vs ih => cases h : s.dup <;> simp [h, ih]

theorem total_eq (vs : List NodeS3) :
    total vs = ((vs.filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum := by
  rw [← sum_filter, total, szBefore]
  exact congrArg List.sum (map_getD' default (fun s : NodeS3 => if s.dup then 0 else (s.v.ser false).length) vs)

theorem cell_node {vs : List NodeS3} {H q : Nat} (hq : q < R vs) :
    cell vs H q = rowCell vs ((recsOf vs).getD q default) := by
  funext x; simp [cell, hq]

theorem cell_sum {vs : List NodeS3} {H : Nat} : cell vs H (R vs) = sumCell (total vs) := by
  funext x; simp [cell]

theorem cell_pad {vs : List NodeS3} {H q : Nat} (hq : R vs < q) : cell vs H q = padCell (total vs) := by
  funext x; simp [cell, show ¬ q < R vs by omega, show q ≠ R vs by omega]

/-- All rows: the records' messages, then the `SUM` row's. -/
theorem rows_all (vs : List NodeS3) {H : Nat} (hHR : R vs + 1 ≤ H) (b : Nat) (sd : Bool) :
    (List.range H).flatMap (fun q => rowN (cell vs H q) b sd) =
      (List.range vs.length).flatMap (fun n => recN vs n b sd) ++
        (if b = B_SIZE ∧ sd = true then [[0, total vs]] else []) := by
  rw [range_split hHR, List.flatMap_append,
    flatMap_nil' (l := List.map _ _) (fun q hq => by
      obtain ⟨q', _, rfl⟩ := List.mem_map.1 hq
      rw [cell_pad (by omega), rowN_pad]),
    List.append_nil, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    cell_sum, rowN_sum,
    ZkFormal.Near.Render.flatMap_congr' (fun q hq => by rw [cell_node (List.mem_range.1 hq)]), nodes_flat]

theorem rowN_other (c : Nat → Nat) (b : Nat) (sd : Bool) (h1 : b ≠ B_BYTES) (h2 : b ≠ B_DIGEST) (h3 : b ≠ B_PARENT)
    (h4 : b ≠ B_VPARENT) (h5 : b ≠ B_EDGE) (h6 : b ≠ B_BMAP) (h7 : b ≠ B_DIGS) (h8 : b ≠ B_DUP) (h9 : b ≠ B_ENT)
    (h10 : b ≠ B_SIZE) (h11 : b ≠ B_UPB) (h12 : b ≠ B_VSLOT) : rowN c b sd = [] := by
  simp [rowN, rowN0, rowNU, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8,
    Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12]

/-- The `VSLOT` receive of a row: the `VPARENT` message's first entry when `tw = 1`. -/
theorem rowN_vslot (c : Nat → Nat) (h : c 167 ≤ 1) :
    rowN c B_VSLOT false = if c 167 = 1 then (rowN c B_VPARENT true).map (List.take 1) else [] := by
  rcases (show c 167 = 0 ∨ c 167 = 1 by omega) with h0 | h1
  · simp [rowN, rowN0, rowNU, B_DIGEST, B_BYTES, B_PARENT, B_VPARENT, B_VSLOT, B_EDGE, B_BMAP, B_DIGS, B_DUP,
      B_ENT, B_SIZE, B_UPB, h0, gt]
  · simp only [rowN, rowN0, rowNU, B_DIGEST, B_BYTES, B_PARENT, B_VPARENT, B_VSLOT, B_EDGE, B_BMAP, B_DIGS, B_DUP,
      B_ENT, B_SIZE, B_UPB, h1, Nat.mul_one, if_true]
    simp [gt]
    split <;> simp

/-- `VSLOT` receive of a lockstep-written value slot. -/
def tgtVs (v : NodeV3) : List ZkFormal.Near.Msg := match v.value with | some (i, _, _, _, true) => [[i]] | _ => []

theorem rec_vslot {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    (recN vs n B_VSLOT false).Perm (tgtVs (rec vs n).v) := by
  have hrow : ∀ p ∈ List.range (layN vs n).length, rowN (rowCell vs (mkR vs n p)) B_VSLOT false =
      if twOf (rec vs n).v = true then (rowN (rowCell vs (mkR vs n p)) B_VPARENT true).map (List.take 1) else [] := by
    intro p _
    rw [rowN_vslot _ (by rw [Rc.c167]; cases twOf _ <;> decide), Rc.c167]
    show (if b2n (twOf (rec vs n).v) = 1 then _ else _) = _
    cases twOf (rec vs n).v <;> simp [b2n]
  unfold recN
  rw [ZkFormal.Near.Render.flatMap_congr' hrow]
  have hvp := rec_vpS ok hn
  unfold recN at hvp
  cases htw : twOf (rec vs n).v
  · simp only [Bool.false_eq_true, if_false, flatMap_nil' (fun _ _ => rfl)]
    unfold tgtVs; unfold twOf at htw
    generalize (rec vs n).v.value = o at htw ⊢
    rcases o with _ | ⟨i, l, pre, po, w⟩
    · exact List.Perm.refl _
    · simp only at htw; subst htw; exact List.Perm.refl _
  · simp only [if_true]
    rw [← List.map_flatMap]
    refine (hvp.map (List.take 1)).trans ?_
    unfold tgtVs tgtVp; unfold twOf at htw
    generalize (rec vs n).v.value = o at htw ⊢
    rcases o with _ | ⟨i, l, pre, po, w⟩
    · simp at htw
    · simp only at htw; subst htw; simp

/-- Sends of the records, per bus. -/
theorem sends_perm {vs : List NodeS3} (ok : NodeOk vs) (b : Nat) :
    ((List.range vs.length).flatMap (fun n => recN vs n b true) ++
        (if b = B_SIZE ∧ true = true then [[0, total vs]] else [])).Perm (nodeSends3 vs b) := by
  have R' : ∀ {F' : Nat → List ZkFormal.Near.Msg} {G : NodeS3 × Nat → List ZkFormal.Near.Msg},
      (∀ n, n < vs.length → (recN vs n b true).Perm (F' n)) → (∀ n, F' n = G (rec vs n, n)) →
      ((List.range vs.length).flatMap (fun n => recN vs n b true)).Perm ((vs.zip (List.range vs.length)).flatMap G) := by
    intro F' G h he
    rw [zip_flatMap]
    exact perm_flatMap_congr (fun n hn => perm_eq_r (h n (List.mem_range.1 hn)) (he n))
  by_cases hS : b = B_SIZE
  · subst hS
    rw [flatMap_nil' (fun n hn => rec_sizeS ok (List.mem_range.1 hn))]
    simp [nodeSends3, B_SIZE, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_ENT, B_UPB, B_VSLOT, total_eq]
  rw [if_neg (fun h => hS h.1), List.append_nil]
  by_cases h1 : b = B_BYTES
  · subst h1; simp only [nodeSends3, if_true]
    exact R' (fun n hn => rec_bytesS ok hn) (fun n => rfl)
  by_cases h2 : b = B_PARENT
  · subst h2; simp only [nodeSends3, B_BYTES, B_PARENT, Nat.reduceEqDiff, if_true, if_false]
    exact R' (fun n hn => rec_parS ok hn) (fun n => rfl)
  by_cases h3 : b = B_VPARENT
  · subst h3; simp only [nodeSends3, B_BYTES, B_PARENT, B_VPARENT, Nat.reduceEqDiff, if_true, if_false]
    exact R' (fun n hn => rec_vpS ok hn) (fun n => rfl)
  by_cases h4 : b = B_EDGE
  · subst h4; simp only [nodeSends3, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, Nat.reduceEqDiff, if_true, if_false]
    exact R' (fun n hn => rec_edgeS ok hn) (fun n => rfl)
  by_cases h5 : b = B_BMAP
  · subst h5; simp only [nodeSends3, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, Nat.reduceEqDiff, if_true,
      if_false]
    exact R' (fun n hn => rec_bm ok hn true) (fun n => rfl)
  by_cases h6 : b = B_DIGS
  · subst h6; simp only [nodeSends3, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, Nat.reduceEqDiff,
      if_true, if_false]
    exact R' (fun n hn => rec_digsS ok hn) (fun n => rfl)
  by_cases h7 : b = B_ENT
  · subst h7; simp only [nodeSends3, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_ENT,
      Nat.reduceEqDiff, if_true, if_false]
    exact R' (fun n hn => perm_eq_r (List.Perm.refl _) (rec_entS ok hn)) (fun n => rfl)
  by_cases hU : b = B_UPB
  · subst hU; simp only [nodeSends3, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_ENT, B_SIZE, B_UPB,
      Nat.reduceEqDiff, if_true, if_false]
    exact R' (fun n hn => perm_eq_r (List.Perm.refl _) (rec_upb ok hn true)) (fun n => rfl)
  rw [flatMap_nil' (fun n _ => show recN vs n b _ = [] from flatMap_nil' (fun p _ => by
    rcases (show b = B_DIGEST ∨ b = B_DUP ∨ (b ≠ B_DIGEST ∧ b ≠ B_DUP) by omega) with h | h | ⟨h8, h9⟩
    · subst h; simp [rowN, rowN0, rowNU, B_DIGEST, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_DUP, B_ENT, B_SIZE, B_UPB, B_VSLOT]
    · subst h; simp [rowN, rowN0, rowNU, B_DIGEST, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_DUP, B_ENT, B_SIZE, B_UPB, B_VSLOT]
    · rcases (show b = B_VSLOT ∨ b ≠ B_VSLOT by omega) with hV | hV
      · subst hV; simp [rowN, rowN0, rowNU, B_DIGEST, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_DUP,
          B_ENT, B_SIZE, B_UPB, B_VSLOT]
      · exact rowN_other _ _ _ h1 h8 h2 h3 h4 h5 h6 h9 h7 hS hU hV))]
  have hV : b ≠ B_VSLOT ∨ b = B_VSLOT := by omega
  rcases hV with hV | hV
  · simp [nodeSends3, h1, h2, h3, h4, h5, h6, h7, hS, hU, hV]
  · subst hV; simp [nodeSends3, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_ENT, B_SIZE, B_UPB, B_VSLOT]

/-- Receives of the records, per bus. -/
theorem recvs_perm {vs : List NodeS3} (ok : NodeOk vs) (b : Nat) :
    ((List.range vs.length).flatMap (fun n => recN vs n b false) ++
        (if b = B_SIZE ∧ false = true then [[0, total vs]] else [])).Perm (nodeRecvs3 vs b) := by
  have R' : ∀ {F' : Nat → List ZkFormal.Near.Msg} {G : NodeS3 × Nat → List ZkFormal.Near.Msg},
      (∀ n, n < vs.length → (recN vs n b false).Perm (F' n)) → (∀ n, F' n = G (rec vs n, n)) →
      ((List.range vs.length).flatMap (fun n => recN vs n b false)).Perm ((vs.zip (List.range vs.length)).flatMap G) := by
    intro F' G h he
    rw [zip_flatMap]
    exact perm_flatMap_congr (fun n hn => perm_eq_r (h n (List.mem_range.1 hn)) (he n))
  simp only [Bool.false_eq_true, and_false, if_false, List.append_nil]
  by_cases h1 : b = B_DIGEST
  · subst h1; simp only [nodeRecvs3, if_true]
    exact R' (fun n hn => rec_digR ok hn) (fun n => rfl)
  by_cases h2 : b = B_PARENT
  · subst h2; simp only [nodeRecvs3, B_DIGEST, B_PARENT, Nat.reduceEqDiff, if_true, if_false]
    rw [zip_map]
    exact perm_flatMap_congr (fun n hn => perm_eq_r (List.Perm.refl _) (rec_parentR ok (List.mem_range.1 hn)))
  by_cases h3 : b = B_EDGE
  · subst h3; simp only [nodeRecvs3, B_DIGEST, B_PARENT, B_EDGE, Nat.reduceEqDiff, if_true, if_false]
    exact R' (fun n hn => rec_edgeR ok hn) (fun n => rfl)
  by_cases h4 : b = B_BMAP
  · subst h4; simp only [nodeRecvs3, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, Nat.reduceEqDiff, if_true, if_false]
    exact R' (fun n hn => rec_bm ok hn false) (fun n => rfl)
  by_cases h5 : b = B_DUP
  · subst h5; simp only [nodeRecvs3, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DUP, Nat.reduceEqDiff, if_true, if_false]
    rw [zip_filterMap]
    exact perm_flatMap_congr (fun n hn => perm_eq_r (List.Perm.refl _) (by
      rw [show (19 : Nat) = B_DUP from rfl, rec_dupR ok (List.mem_range.1 hn)]; cases (rec vs n).dup <;> rfl))
  by_cases h6 : b = B_ENT
  · subst h6; simp only [nodeRecvs3, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DUP, B_ENT, Nat.reduceEqDiff, if_true,
      if_false]
    exact R' (fun n hn => perm_eq_r (List.Perm.refl _) (rec_entR ok hn)) (fun n => rfl)
  by_cases hU : b = B_UPB
  · subst hU; simp only [nodeRecvs3, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DUP, B_ENT, B_UPB, Nat.reduceEqDiff,
      if_true, if_false]
    exact R' (fun n hn => perm_eq_r (List.Perm.refl _) (rec_upb ok hn false)) (fun n => rfl)
  by_cases hV : b = B_VSLOT
  · subst hV; simp only [nodeRecvs3, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DUP, B_ENT, B_UPB, B_VSLOT,
      Nat.reduceEqDiff, if_true, if_false]
    exact R' (fun n hn => rec_vslot ok hn) (fun n => rfl)
  rw [flatMap_nil' (fun n _ => show recN vs n b _ = [] from flatMap_nil' (fun p _ => by
    rcases (show b = B_BYTES ∨ b = B_VPARENT ∨ b = B_DIGS ∨ b = B_SIZE ∨
        (b ≠ B_BYTES ∧ b ≠ B_VPARENT ∧ b ≠ B_DIGS ∧ b ≠ B_SIZE) by omega) with h | h | h | h | ⟨h7, h8, h9, h10⟩
    all_goals try (subst h; simp [rowN, rowN0, rowNU, B_DIGEST, B_BYTES, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_DUP,
      B_ENT, B_SIZE, B_UPB, B_VSLOT])
    exact rowN_other _ _ _ h7 h1 h2 h8 h3 h4 h9 h5 h6 h10 hU hV))]
  simp [nodeRecvs3, h1, h2, h3, h4, h5, h6, hU, hV]

end NodeGen3

open NodeGen3 in
/-- **The honest `nodeV3` table has the traffic `nodeTraffic3 vs`.**  Same hypotheses as
`node_render_local`. -/
theorem node_render_traffic (vs : List NodeS3) (hok : NodeOk vs) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf ((vs.map fun s => (s.v.ser false).length).sum + 1))
    (hcell : ∀ r x, r < tr.height t → x < NodeV3.width →
      tr.cell t r x = Fp.ofNat (NodeGen3.cell vs (tr.height t) r x)) :
    TableTraffic NodeV3.interactions tr t pub (nodeTraffic3 vs) := by
  rw [← R_eq hok] at hlog
  have hHR : R vs + 1 ≤ tr.height t := by
    simp only [Trace.height, hlog]; exact le_pow_logOf _
  have hall : ∀ b sd, (List.range (tr.height t)).flatMap (fun q => rowTraffic NodeV3.interactions tr t q pub b sd) =
      ((List.range vs.length).flatMap (fun n => recN vs n b sd) ++
        (if b = B_SIZE ∧ sd = true then [[0, total vs]] else [])).map Msg.toFp := by
    intro b sd
    rw [ZkFormal.Near.Render.flatMap_congr' (g := fun q => (rowN (cell vs (tr.height t) q) b sd).map Msg.toFp)
      (fun q hq => rowT_eq _ (fun x hx => hcell q x (List.mem_range.1 hq) hx)
        (fun x hx => gate_le3 vs _ q x hx) (vs_le vs _ q)
        (cell_bool vs _ q (x := NodeV3.tw) (by decide)) b sd),
      ← List.map_flatMap, rows_all vs hHR]
  apply traffic_of
  · intro b; rw [hall b true]; exact (sends_perm hok b).map _
  · intro b; rw [hall b false]; exact (recvs_perm hok b).map _

end ZkFormal.NearV3.Render
