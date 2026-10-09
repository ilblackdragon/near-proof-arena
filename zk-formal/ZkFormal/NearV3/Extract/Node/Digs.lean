import ZkFormal.NearV3.Extract.Node.Gated2

/-!
# ZkFormal.NearV3.Extract.Node.Digs — `DIGS`, `ENT` and `SIZE` messages of one node

`DIGS (eid, τ, i, byte)` is sent on every row of a revealed child window (`eid = NPRE(cid)`)
and of a revealed value window (`eid = VPRE(vid)`); `ENT` is sent / received on every row
of a record with a duplicate / a duplicate record; `SIZE` is silent on node rows.
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

/-- `DIGS` of a child slot. -/
def kidDigs (t : Nat) (kd : NKid) : List Msg := match kd with
  | .node c _ _ pre _ => (List.range 32).map fun i => [msgId K_NPRE c, t, i, pre.getD i 0]
  | _ => []

/-- `DIGS` of a value slot. -/
def valDigsS (t : Nat) (sl : NSlot3) : List Msg := match sl with
  | .val _ i _ pre _ _ => (List.range 32).map fun j => [msgId K_VPRE i, t, j, pre.getD j 0]
  | _ => []

/-- `DIGS` of one record (the `B_DIGS` part of `nodeSends3`). -/
def pnDigs (S : NodeS3) : List Msg :=
  (S.v.revealed.flatMap fun (c, _, _, pre, _) =>
    (List.range 32).map fun i => [msgId K_NPRE c, S.tau, i, pre.getD i 0]) ++
  (match S.v.value with
   | some (i, _, pre, _, _) => (List.range 32).map fun j => [msgId K_VPRE i, S.tau, j, pre.getD j 0]
   | none => [])

/-- `ENT` of one record. -/
def pnEntS (n : Nat) (S : NodeS3) : List Msg := if S.hd then
  (List.range (S.v.ser false).length).map fun p => [eidN n, (S.v.ser false).length, p, (S.v.ser false).getD p 0]
  else []
def pnEntR (S : NodeS3) : List Msg := if S.dup then
  (List.range (S.v.ser false).length).map fun p => [S.repE, (S.v.ser false).length, p, (S.v.ser false).getD p 0]
  else []

theorem fp_mul_zero_add (a b' : Fp) : 1 * a + 0 * b' = a := by grind
theorem fp_zero_mul_add (a b' : Fp) : 0 * a + 1 * b' = b' := by grind
theorem fp_eid1 {g d x y : Fp} (hg : g = 1) (h : g * (d - (1 * x + 0 * y)) = 0) : d = x := by
  rw [hg] at h; grind
theorem fp_eid2 {g d x y : Fp} (hg : g = 1) (h : g * (d - (0 * x + 1 * y)) = 0) : d = y := by
  rw [hg] at h; grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-! ## Field sums -/

theorem leafFieldSum (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s tl = 1) {α : Type} (F : Nat × Nat → List α)
    (hz : ∀ o L x, (o, L) ∈ fl → tr.cell T_NODE (s + o) x = 1 → x ∈ states → sVH ≠ x → sCH ≠ x → F (o, L) = []) :
    fl.flatMap F = F (9 + cv tr T_NODE s hplen, 32) := by
  obtain ⟨hh1, -, hfl, hℓ, sT, sH, sF, sK, sV, sVH, sM⟩ := leafFields hL hC ht
  have mem : ∀ p ∈ leafFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  have z0 := hz 0 1 _ (mem _ (by simp [leafFL, keyFL])) (by simpa using sT) (by simp [states]) (by decide) (by decide)
  have z1 := hz _ 4 _ (mem _ (by simp [leafFL, keyFL])) sH (by simp [states]) (by decide) (by decide)
  have z5 := hz _ 1 _ (mem _ (by simp [leafFL, keyFL])) sF (by simp [states]) (by decide) (by decide)
  have zV := hz _ 4 _ (mem _ (by simp [leafFL, keyFL])) sV (by simp [states]) (by decide) (by decide)
  have zM := hz _ 8 _ (mem _ (by simp [leafFL, keyFL])) sM (by simp [states]) (by decide) (by decide)
  rw [hfl]; unfold leafFL keyFL
  by_cases h1 : cv tr T_NODE s hplen = 1
  · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil]
    simp only [z0, z1, z5, zV, zM, List.nil_append, List.append_nil]
  · have zK := hz _ (cv tr T_NODE s hplen - 1) _ (mem _ (by simp [leafFL, keyFL, h1])) (sK h1) (by simp [states])
      (by decide) (by decide)
    simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil]
    simp only [z0, z1, z5, zV, zM, zK, List.nil_append, List.append_nil]

theorem extFieldSum (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s te = 1) {α : Type} (F : Nat × Nat → List α)
    (hz : ∀ o L x, (o, L) ∈ fl → tr.cell T_NODE (s + o) x = 1 → x ∈ states → sVH ≠ x → sCH ≠ x → F (o, L) = []) :
    fl.flatMap F = F (5 + cv tr T_NODE s hplen, 32) := by
  obtain ⟨hh1, -, hfl, hℓ, sT, sH, sF, sK, sC, sM⟩ := extFields hL hC ht
  have mem : ∀ p ∈ extFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  have z0 := hz 0 1 _ (mem _ (by simp [extFL, keyFL])) (by simpa using sT) (by simp [states]) (by decide) (by decide)
  have z1 := hz _ 4 _ (mem _ (by simp [extFL, keyFL])) sH (by simp [states]) (by decide) (by decide)
  have z5 := hz _ 1 _ (mem _ (by simp [extFL, keyFL])) sF (by simp [states]) (by decide) (by decide)
  have zM := hz _ 8 _ (mem _ (by simp [extFL, keyFL])) sM (by simp [states]) (by decide) (by decide)
  rw [hfl]; unfold extFL keyFL
  by_cases h1 : cv tr T_NODE s hplen = 1
  · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil]
    simp only [z0, z1, z5, zM, List.nil_append, List.append_nil]
  · have zK := hz _ (cv tr T_NODE s hplen - 1) _ (mem _ (by simp [extFL, keyFL, h1])) (sK h1) (by simp [states])
      (by decide) (by decide)
    simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil]
    simp only [z0, z1, z5, zM, zK, List.nil_append, List.append_nil]

theorem brFieldSum (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) {α : Type}
    (F : Nat × Nat → List α)
    (hz : ∀ o L x, (o, L) ∈ fl → tr.cell T_NODE (s + o) x = 1 → x ∈ states → sVH ≠ x → sCH ≠ x → F (o, L) = []) :
    fl.flatMap F = (if brOff tr s = 37 then F (5, 32) else []) ++
      (List.range (popN tr s)).flatMap fun j => F (brOff tr s + 2 + 32 * j, 32) := by
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, hℓ, sT, sVV, sB, -, sM, -⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  have hoff : brOff tr s = 1 ∨ brOff tr s = 37 := by unfold brOff; split <;> simp
  have z0 := hz 0 1 _ (mem _ (by simp [brFL])) (by simpa using sT) (by simp [states]) (by decide) (by decide)
  have zB := hz _ 2 _ (mem _ (by simp [brFL])) sB (by simp [states]) (by decide) (by decide)
  have zM := hz _ 8 _ (mem _ (by simp [brFL])) sM (by simp [states]) (by decide) (by decide)
  rw [hfl]; unfold brFL
  rcases hoff with ho | ho
  · have n37 : ¬ brOff tr s = 37 := by rw [ho]; decide
    rw [if_neg n37, if_pos ho]
    simp only [List.append_nil, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.flatMap_map, z0, zB, zM]
  · obtain ⟨sV, sH⟩ := sVV ho
    have zV := hz _ 4 _ (mem _ (by simp [brFL, ho])) sV (by simp [states]) (by decide) (by decide)
    have n1 : ¬ brOff tr s = 1 := by rw [ho]; decide
    rw [if_pos ho, if_neg n1]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map]
    rw [z0, zV, zB, zM]
    simp only [List.nil_append, List.append_nil]

/-! ## `DIGS` per field -/

theorem winConstM (hC : NodeCtx tr s ℓ fl) {o L : Nat} (hm : (o, L) ∈ fl)
    (hch : tr.cell T_NODE (s + o) sCH = 1) {x : Nat} (hx : x ∈ windowConst) :
    ∀ d, d < L → tr.cell T_NODE (s + o + d) x = tr.cell T_NODE (s + o) x := by
  have hF := hC.fields.field _ hm
  simp only at hF
  intro d; induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    have hc : tr.cell T_NODE (s + o + d) sCH = 1 := by rw [hF.1.st d (by omega) sCH (by simp [states]), hch]
    have hfe : tr.cell T_NODE (s + o + d) fe = 0 :=
      bool01 hL (by have := hC.bound; have := hF.2; omega) (by simp [boolCols]) (fun h' => by
        have := (hF.1.fe d (by omega)).1 h'; omega)
    have := winConst hL (r := s + o + d) (by have := hC.bound; have := hF.2; omega) hc hfe x hx
    rw [show s + o + (d + 1) = s + o + d + 1 by omega, this, ih (by omega)]

theorem digsPlain (hC : NodeCtx tr s ℓ fl) {o L x : Nat} (hm : (o, L) ∈ fl) (hx : tr.cell T_NODE (s + o) x = 1)
    (hxs : x ∈ states) (h1 : sVH ≠ x) (h2 : sCH ≠ x) :
    (List.range' (s + o) L).flatMap (fun r => rowT tr pub r B_DIGS true) = [] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  rw [List.range'_eq_map_range, List.flatMap_map]
  apply flatMap_eq_nil'; intro d hd; rw [List.mem_range] at hd
  have hr : s + o + d < tr.height T_NODE := by omega
  have ha := hF.act d hd
  have hx' : tr.cell T_NODE (s + o + d) x = 1 := by rw [hF.st d hd x hxs, hx]
  have hv := stOnly hL hr ha hx' hxs (by simp [states]) h1
  have hc := stOnly hL hr ha hx' hxs (by simp [states]) h2
  have G := linkGates hL hr; simp only at G
  have h0 : tr.cell T_NODE (s + o + d) gS = 0 := by rw [G.2.2.2.1, hv, hc]; grind
  rw [rowT_digsS, h0]; simp [gate]


set_option maxHeartbeats 1000000 in
theorem digsCH (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl) (hc : tr.cell T_NODE (s + o) sCH = 1) :
    (List.range' (s + o) 32).flatMap (fun r => rowT tr pub r B_DIGS true) =
      (kidDigs (cv tr T_NODE s tau) (kidOf tr (s + o))).map Msg.toFp := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hin : o + 32 ≤ ℓ := (hC.fields.field _ hm).2
  have hr0 : s + o < tr.height T_NODE := by omega
  have ha0 : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 (by omega)
  have W := (winField hL hF (by omega) (by
    rw [hc, stOnly hL hr0 ha0 hc (by simp [states]) (y := sVH) (by simp [states]) (by decide)]; grind)).1
  have per : ∀ d, d < 32 → rowT tr pub (s + o + d) B_DIGS true =
      if cv tr T_NODE (s + o) rv = 1 then
        [Msg.toFp [msgId K_NPRE (cv tr T_NODE (s + o) cid), cv tr T_NODE s tau, d, (win tr reg (s + o)).getD d 0]]
      else [] := by
    intro d hd
    have hr : s + o + d < tr.height T_NODE := by omega
    have ha := hF.act d hd
    have hc' : tr.cell T_NODE (s + o + d) sCH = 1 := by rw [hF.st d hd sCH (by simp [states]), hc]
    have hv := stOnly hL hr ha hc' (by simp [states]) (y := sVH) (by simp [states]) (by decide)
    have G := linkGates hL hr; simp only at G
    have hrv := winConstM hL hC hm hc (x := rv) (by simp [windowConst]) d hd
    have hcid := winConstM hL hC hm hc (x := cid) (by simp [windowConst]) d hd
    have htau : tr.cell T_NODE (s + o + d) tau = tr.cell T_NODE s tau := by
      rw [show s + o + d = s + (o + d) by omega]; exact segConst hL hC (by simp [nodeConst]) (by omega)
    have hgS : tr.cell T_NODE (s + o + d) gS = tr.cell T_NODE (s + o) rv := by
      rw [G.2.2.2.1, hc', hv, hrv]; grind
    rw [rowT_digsS, hgS]
    rcases isBool hL hr0 (x := rv) (by simp [boolCols]) with h | h
    · rw [h, if_neg (by rw [cv_zero h]; decide)]; simp [gate]
    · rw [h, if_pos (cv_one h), gate_one]
      have hdE := G.2.2.2.2.1
      rw [hc', hv] at hdE
      have hdE' := fp_eid1 (by rw [hgS, h]) hdE
      have hb : (win tr reg (s + o)).getD d 0 = cv tr T_NODE (s + o + d) b := by
        have := congrArg (fun l => l.getD d 0) W
        simp only [rowsB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd, Option.map_some,
          Option.getD_some] at this
        rw [List.getD_eq_getElem?_getD]; exact this.symm
      rw [hb]
      simp only [Msg.toFp, List.map_cons, List.map_nil, ofNat_npre, ofNat_cv']
      rw [hdE', hcid, htau, (hF.idx d hd), ← natCast_eq, ← cast_cv tr (s + o) cid]
  rw [List.range'_eq_map_range, List.flatMap_map, flatMap_congr' (fun d hd => per d (List.mem_range.mp hd))]
  unfold kidOf
  by_cases hrv : cv tr T_NODE (s + o) rv = 1
  · simp only [if_pos hrv, kidDigs, List.map_map]
    rw [map_eq_flatMap]; rfl
  · simp only [if_neg hrv, kidDigs]; simp

set_option maxHeartbeats 1000000 in
theorem digsVH (hC : NodeCtx tr s ℓ fl) {o rV : Nat} (hm : (o, 32) ∈ fl) (hc : tr.cell T_NODE (s + o) sVH = 1) :
    (List.range' (s + o) 32).flatMap (fun r => rowT tr pub r B_DIGS true) =
      (valDigsS (cv tr T_NODE s tau) (slotOf tr s rV (s + o))).map Msg.toFp := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hin : o + 32 ≤ ℓ := (hC.fields.field _ hm).2
  have hr0 : s + o < tr.height T_NODE := by omega
  have ha0 : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 (by omega)
  have W := (winField hL hF (by omega) (by
    rw [hc, stOnly hL hr0 ha0 hc (by simp [states]) (y := sCH) (by simp [states]) (by decide)]; grind)).1
  have per : ∀ d, d < 32 → rowT tr pub (s + o + d) B_DIGS true =
      if cv tr T_NODE s tv = 1 then
        [Msg.toFp [msgId K_VPRE (cv tr T_NODE s vid), cv tr T_NODE s tau, d, (win tr reg (s + o)).getD d 0]]
      else [] := by
    intro d hd
    have hr : s + o + d < tr.height T_NODE := by omega
    have ha := hF.act d hd
    have hc' : tr.cell T_NODE (s + o + d) sVH = 1 := by rw [hF.st d hd sVH (by simp [states]), hc]
    have hch := stOnly hL hr ha hc' (by simp [states]) (y := sCH) (by simp [states]) (by decide)
    have G := linkGates hL hr; simp only at G
    have k : ∀ x ∈ nodeConst, tr.cell T_NODE (s + o + d) x = tr.cell T_NODE s x := fun x hx => by
      rw [show s + o + d = s + (o + d) by omega]; exact segConst hL hC hx (by omega)
    have hgS : tr.cell T_NODE (s + o + d) gS = tr.cell T_NODE s tv := by
      rw [G.2.2.2.1, hc', hch, k tv (by simp [nodeConst])]; grind
    rw [rowT_digsS, hgS]
    rcases isBool hL (nodeStart hL hC).1 (x := tv) (by simp [boolCols]) with h | h
    · rw [h, if_neg (by rw [cv_zero h]; decide)]; simp [gate]
    · rw [h, if_pos (cv_one h), gate_one]
      have hdE := G.2.2.2.2.1
      rw [hc', hch] at hdE
      have hdE' := fp_eid2 (by rw [hgS, h]) hdE
      have hb : (win tr reg (s + o)).getD d 0 = cv tr T_NODE (s + o + d) b := by
        have := congrArg (fun l => l.getD d 0) W
        simp only [rowsB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd, Option.map_some,
          Option.getD_some] at this
        rw [List.getD_eq_getElem?_getD]; exact this.symm
      rw [hb]
      simp only [Msg.toFp, List.map_cons, List.map_nil, ofNat_vpre, ofNat_cv']
      rw [hdE', k vid (by simp [nodeConst]), k tau (by simp [nodeConst]), (hF.idx d hd), ← natCast_eq,
        ← cast_cv tr s vid]
  rw [List.range'_eq_map_range, List.flatMap_map, flatMap_congr' (fun d hd => per d (List.mem_range.mp hd))]
  unfold slotOf
  by_cases htv : cv tr T_NODE s tv = 1
  · simp only [if_pos htv, valDigsS, List.map_map]
    rw [map_eq_flatMap]; rfl
  · simp only [if_neg htv, valDigsS]; simp

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem valDigsS_eq (t : Nat) (sl : NSlot3) : valDigsS t sl = match slotValue sl with
    | some (i, _, pre, _, _) => (List.range 32).map fun j => [msgId K_VPRE i, t, j, pre.getD j 0]
    | none => [] := by cases sl <;> rfl

theorem revF_kidDigs (t : Nat) (kd : NKid) :
    (revF kd).toList.flatMap (fun x : Nat × Nat × Nat × List Nat × List Nat =>
      (List.range 32).map fun i => [msgId K_NPRE x.1, t, i, x.2.2.2.1.getD i 0]) = kidDigs t kd := by
  cases kd <;> simp [revF, kidDigs]

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

set_option maxHeartbeats 1000000 in
/-- `DIGS` of one record. -/
theorem nodeDigs (hC : NodeCtx tr s ℓ fl) (S : NodeS3) (hv : S.v = nodeVOf tr s) (ht : S.tau = cv tr T_NODE s tau) :
    ((List.range' s ℓ).flatMap (fun r => rowT tr pub r B_DIGS true)).Perm ((pnDigs S).map Msg.toFp) := by
  rw [rowsFields hL hC]
  have hz : ∀ o L x, (o, L) ∈ fl → tr.cell T_NODE (s + o) x = 1 → x ∈ states → sVH ≠ x → sCH ≠ x →
      (fun p : Nat × Nat => (List.range' (s + p.1) p.2).flatMap (fun r => rowT tr pub r B_DIGS true)) (o, L) = [] :=
    fun o L x hm hx hxs h1 h2 => digsPlain hL hC hm hx hxs h1 h2
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  simp only [pnDigs, hv, ht]
  by_cases h1 : cv tr T_NODE s tl = 1
  · have htl := of_cv_one h1
    obtain ⟨-, -, hfl, -, -, -, -, -, -, sVH, -⟩ := leafFields hL hC htl
    have hm : (9 + cv tr T_NODE s hplen, 32) ∈ fl := hfl ▸ (by simp [leafFL])
    rw [leafFieldSum hL hC htl _ hz]
    simp only
    rw [digsVH hL hC (rV := s + (5 + cv tr T_NODE s hplen)) hm sVH]
    unfold nodeVOf; rw [if_pos h1]
    simp only [NodeV3.revealed, value_leaf, List.flatMap_nil, List.nil_append, valDigsS_eq]
    exact List.Perm.refl _
  by_cases h2 : cv tr T_NODE s te = 1
  · have hte := of_cv_one h2
    obtain ⟨-, -, hfl, -, -, -, -, -, sC, -⟩ := extFields hL hC hte
    have hm : (5 + cv tr T_NODE s hplen, 32) ∈ fl := hfl ▸ (by simp [extFL])
    rw [extFieldSum hL hC hte _ hz]
    simp only
    rw [digsCH hL hC hm sC]
    unfold nodeVOf; rw [if_neg h1, if_pos h2]
    simp only [revealed_ext, value_ext, List.append_nil, revF_kidDigs]
    exact List.Perm.refl _
  have hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1 := by
    have b1 := cvb hL hr0 (x := tb1) (by simp [boolCols])
    have b2 := cvb hL hr0 (x := tb2) (by simp [boolCols])
    rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add,
      show cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 by omega]; rfl
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, -, -, sVV, -, -, -, hW⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  rw [brFieldSum hL hC hb _ hz]
  simp only
  rw [flatMap_congr' (l := List.range (popN tr s))
    (G := fun j => (kidDigs (cv tr T_NODE s tau) (kidOf tr (s + (brOff tr s + 2 + 32 * j)))).map Msg.toFp)
    (fun j hj => digsCH hL hC (mem _ (by simp [brFL]; exact Or.inr ⟨j, List.mem_range.mp hj, rfl⟩))
      (hW j (List.mem_range.mp hj)).1)]
  have hk : ((kidsOf tr s (brOff tr s)).filterMap revF).flatMap (fun x : Nat × Nat × Nat × List Nat × List Nat =>
      (List.range 32).map fun i => [msgId K_NPRE x.1, cv tr T_NODE s tau, i, x.2.2.2.1.getD i 0]) =
      (List.range (popN tr s)).flatMap fun w => kidDigs (cv tr T_NODE s tau) (kidOf tr (s + (brOff tr s + 2 + 32 * w))) := by
    rw [flatMap_filterMap]; simp only [revF_kidDigs]
    exact kidsFlat hL hC (brOff tr s) (kidDigs _) rfl
  unfold nodeVOf; rw [if_neg h1, if_neg h2]
  simp only [revealed_branch, value_br, hk]
  rw [← List.map_flatMap]
  by_cases h37 : brOff tr s = 37
  · obtain ⟨-, sH⟩ := sVV h37
    have hm5 : (5, 32) ∈ fl := mem _ (by simp [brFL, h37])
    have hb2 : cv tr T_NODE s tb2 = 1 := by unfold brOff at h37; split at h37 <;> simp_all
    rw [if_pos h37, digsVH hL hC (rV := s + 1) hm5 sH, if_pos hb2]
    simp only [Option.bind_some, valDigsS_eq, List.map_append]
    exact List.perm_append_comm
  · have hb1 : cv tr T_NODE s tb2 ≠ 1 := by intro h; apply h37; unfold brOff; rw [if_pos h]
    rw [if_neg h37, if_neg hb1]
    simp only [Option.bind_none, List.nil_append, List.append_nil]
    exact List.Perm.refl _

/-- `ENT` of one record (both sides). -/
theorem nodeEnt (hC : NodeCtx tr s ℓ fl) {n : Nat} (S : NodeS3) (hv : S.v = nodeVOf tr s)
    (hdu : S.dup = decide (cv tr T_NODE s dup = 1)) (hhd : S.hd = decide (cv tr T_NODE s hd = 1))
    (hre : S.repE = cv tr T_NODE s repE) (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp))
    (hpos : ∀ d, d < ℓ → tr.cell T_NODE (s + d) pos = ((d : Nat) : Fp)) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_ENT true) = (pnEntS n S).map Msg.toFp ∧
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_ENT false) = (pnEntR S).map Msg.toFp := by
  obtain ⟨S1, -⟩ := nodeSer hL hC
  have hr0 := (nodeStart hL hC).1
  have k : ∀ x ∈ nodeConst, ∀ d, d < ℓ → tr.cell T_NODE (s + d) x = tr.cell T_NODE s x :=
    fun x hx d hd => segConst hL hC hx hd
  have hlen : ∀ d, d < ℓ → tr.cell T_NODE (s + d) len = ((ℓ : Nat) : Fp) := fun d hd => by
    rw [k len (by simp [nodeConst]) d hd, lenCell hL hC]
  unfold pnEntS pnEntR
  rw [hv, ← S1, rowsB_length, hdu, hhd, hre]
  have row : ∀ d, d < ℓ → (rowsB tr b s ℓ).getD d 0 = cv tr T_NODE (s + d) b := fun d hd => by
    simp [rowsB, List.getD_eq_getElem?_getD, List.getElem?_range hd]
  constructor
  · rw [List.range'_eq_map_range, List.flatMap_map]
    rcases isBool hL hr0 (x := hd) (by simp [boolCols]) with h | h
    · rw [cv_zero h]; simp only [show ¬ (0 : Nat) = 1 by decide, decide_false, Bool.false_eq_true, if_false,
        List.map_nil]
      apply flatMap_eq_nil'; intro d hdl; rw [List.mem_range] at hdl
      rw [rowT_entS, k NodeV3.hd (by simp [nodeConst]) d hdl, h]; simp [gate]
    · rw [cv_one h]; simp only [decide_true, if_true, List.map_map]
      rw [map_eq_flatMap]
      apply flatMap_congr'; intro d hdl; rw [List.mem_range] at hdl
      rw [rowT_entS, k NodeV3.hd (by simp [nodeConst]) d hdl, h, gate_one]
      simp only [Function.comp_apply]
      rw [row d hdl]
      simp only [ Msg.toFp, List.map_cons, List.map_nil, eidN, ofNat_npre, ofNat_cv']
      rw [k nid (by simp [nodeConst]) d hdl, hn, hlen d hdl, hpos d hdl, ← natCast_eq, ← natCast_eq]
  · rw [List.range'_eq_map_range, List.flatMap_map]
    rcases isBool hL hr0 (x := dup) (by simp [boolCols]) with h | h
    · rw [cv_zero h]; simp only [show ¬ (0 : Nat) = 1 by decide, decide_false, Bool.false_eq_true, if_false,
        List.map_nil]
      apply flatMap_eq_nil'; intro d hdl; rw [List.mem_range] at hdl
      rw [rowT_entR, k dup (by simp [nodeConst]) d hdl, h]; simp [gate]
    · rw [cv_one h]; simp only [decide_true, if_true, List.map_map]
      rw [map_eq_flatMap]
      apply flatMap_congr'; intro d hdl; rw [List.mem_range] at hdl
      rw [rowT_entR, k dup (by simp [nodeConst]) d hdl, h, gate_one]
      simp only [Function.comp_apply]
      rw [row d hdl]
      simp only [ Msg.toFp, List.map_cons, List.map_nil, ofNat_cv']
      rw [k repE (by simp [nodeConst]) d hdl, hlen d hdl, hpos d hdl, ← natCast_eq, ← natCast_eq]

/-- Node rows are silent on `SIZE`. -/
theorem nodeSize (hC : NodeCtx tr s ℓ fl) (sd : Bool) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_SIZE sd) = [] := by
  rw [List.range'_eq_map_range, List.flatMap_map]
  apply flatMap_eq_nil'; intro d hd; rw [List.mem_range] at hd
  cases sd
  · exact rowT_sizeR _
  · have hr : s + d < tr.height T_NODE := by have := hC.bound; omega
    have h := (rowFacts hL hr).2.2.1
    rw [segAct hL hC hd] at h
    rw [rowT_sizeS, show tr.cell T_NODE (s + d) sumr = 0 by grind]; simp [gate]

end ZkFormal.NearV3.NodeProof3
