import ZkFormal.NearV3.Extract.Node.Traffic

/-!
# ZkFormal.Near.Extract.NodeGated — DIGEST / PARENT / VSLOT messages of a node
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

/-- The gated (bus, side) pairs. -/
def Gated (bb : Nat) (sd : Bool) : Prop :=
  (bb = B_DIGEST ∧ sd = false) ∨ (bb = B_PARENT ∧ sd = true) ∨ (bb = B_PARENT ∧ sd = false) ∨
    (bb = B_VPARENT ∧ sd = true) ∨ (bb = B_BMAP ∧ sd = true) ∨ (bb = B_BMAP ∧ sd = false) ∨
    (bb = B_DUP ∧ sd = false)

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem gatedQuiet (hC : NodeCtx tr s ℓ fl) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    ∀ r, s ≤ r → r < s + ℓ → tr.cell T_NODE r fs = 0 → rowT tr pub r bb sd = [] := by
  intro r h1 h2 h3
  have Q := quietRow hL hC h1 h2 h3
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Q.1
  · exact Q.2.1
  · exact Q.2.2.1
  · exact Q.2.2.2.1
  · exact Q.2.2.2.2.1
  · exact Q.2.2.2.2.2.1
  · exact Q.2.2.2.2.2.2

theorem gatedFields (hC : NodeCtx tr s ℓ fl) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) = fl.flatMap fun p => rowT tr pub (s + p.1) bb sd := by
  rw [rowsFields hL hC]
  exact flatMap_congr' (fun p hp => fieldGated hL hC hp (gatedQuiet hL hC hg))

/-- A field start that is not a window, a bitmap or the node start is silent on gated buses. -/
theorem plainStartG (hC : NodeCtx tr s ℓ fl) {o L x : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o)
    (hx : tr.cell T_NODE (s + o) x = 1) (hxs : x ∈ states) (h1 : sVH ≠ x) (h2 : sCH ≠ x) (h3 : sBM ≠ x)
    {bb : Nat} {sd : Bool} (hg : Gated bb sd) : rowT tr pub (s + o) bb sd = [] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by have := hF.pos; omega
  have ha : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 hF.pos
  have hv := stOnly hL hr ha hx hxs (by simp [states]) h1
  have hc := stOnly hL hr ha hx hxs (by simp [states]) h2
  have hb := stOnly hL hr ha hx hxs (by simp [states]) h3
  obtain ⟨P1, P2, P3, P4, P5⟩ := plainStart hL hC hm ho hc hv hb
  obtain ⟨I1, I2⟩ := innerStart hL hC hm ho
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact P2
  · exact P1
  · exact I1
  · exact P3
  · exact P4
  · exact P5
  · exact I2

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem leafGated (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s tl = 1) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) =
      rowT tr pub s bb sd ++ rowT tr pub (s + (9 + cv tr T_NODE s hplen)) bb sd := by
  obtain ⟨hh1, -, hfl, hℓ, sT, sH, sF, sK, sV, sVH, sM⟩ := leafFields hL hC ht
  have mem : ∀ p ∈ leafFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  rw [gatedFields hL hC hg, hfl]
  have z1 := plainStartG hL hC (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sH (by simp [states]) (by decide) (by decide) (by decide) hg
  have z5 := plainStartG hL hC (L := 1) (mem _ (by simp [leafFL, keyFL])) (by omega) sF (by simp [states]) (by decide) (by decide) (by decide) hg
  have zV := plainStartG hL hC (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sV (by simp [states]) (by decide) (by decide) (by decide) hg
  have zM := plainStartG hL hC (L := 8) (mem _ (by simp [leafFL, keyFL])) (by omega) sM (by simp [states]) (by decide) (by decide) (by decide) hg
  unfold leafFL keyFL
  by_cases h1 : cv tr T_NODE s hplen = 1
  · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zV, zM, List.nil_append, List.append_nil]
  · have zK := plainStartG hL hC (L := cv tr T_NODE s hplen - 1) (mem _ (by simp [leafFL, keyFL, h1])) (by omega)
      (sK h1) (by simp [states]) (by decide) (by decide) (by decide) hg
    simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zV, zM, zK, List.nil_append, List.append_nil]

theorem extGated (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s te = 1) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) =
      rowT tr pub s bb sd ++ rowT tr pub (s + (5 + cv tr T_NODE s hplen)) bb sd := by
  obtain ⟨hh1, -, hfl, hℓ, sT, sH, sF, sK, sC, sM⟩ := extFields hL hC ht
  have mem : ∀ p ∈ extFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  rw [gatedFields hL hC hg, hfl]
  have z1 := plainStartG hL hC (L := 4) (mem _ (by simp [extFL, keyFL])) (by omega) sH (by simp [states]) (by decide) (by decide) (by decide) hg
  have z5 := plainStartG hL hC (L := 1) (mem _ (by simp [extFL, keyFL])) (by omega) sF (by simp [states]) (by decide) (by decide) (by decide) hg
  have zM := plainStartG hL hC (L := 8) (mem _ (by simp [extFL, keyFL])) (by omega) sM (by simp [states]) (by decide) (by decide) (by decide) hg
  unfold extFL keyFL
  by_cases h1 : cv tr T_NODE s hplen = 1
  · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zM, List.nil_append, List.append_nil]
  · have zK := plainStartG hL hC (L := cv tr T_NODE s hplen - 1) (mem _ (by simp [extFL, keyFL, h1])) (by omega)
      (sK h1) (by simp [states]) (by decide) (by decide) (by decide) hg
    simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zM, zK, List.nil_append, List.append_nil]

theorem brGated (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) {bb : Nat} {sd : Bool}
    (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) =
      rowT tr pub s bb sd ++ ((if brOff tr s = 37 then rowT tr pub (s + 5) bb sd else []) ++
        (rowT tr pub (s + brOff tr s) bb sd ++
        (List.range (popN tr s)).flatMap fun j => rowT tr pub (s + (brOff tr s + 2 + 32 * j)) bb sd)) := by
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, hℓ, sT, sVV, sB, -, sM, -⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  have hoff : brOff tr s = 1 ∨ brOff tr s = 37 := by unfold brOff; split <;> simp
  rw [gatedFields hL hC hg, hfl]
  have zM := plainStartG hL hC (L := 8) (mem _ (by simp [brFL])) (by omega) sM (by simp [states]) (by decide) (by decide) (by decide) hg
  unfold brFL
  rcases hoff with ho | ho
  · have n37 : ¬ brOff tr s = 37 := by rw [ho]; decide
    rw [if_neg n37, if_pos ho]
    simp only [List.append_nil, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.flatMap_map, Nat.add_zero, zM]
  · obtain ⟨sV, sH⟩ := sVV ho
    have zV := plainStartG hL hC (L := 4) (mem _ (by simp [brFL, ho])) (by omega) sV (by simp [states]) (by decide) (by decide) (by decide) hg
    have n1 : ¬ brOff tr s = 1 := by rw [ho]; decide
    rw [if_pos ho, if_neg n1]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map,
      Nat.add_zero]
    rw [zV, zM]
    simp only [List.nil_append, List.append_nil, List.append_assoc]

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

def revDigs (kd : NKid) : List Msg := match kd with
  | .node c l _ pre po => [digMsg (msgId K_NPRE c) l pre, digMsg (msgId K_NPOST c) l po]
  | _ => []

def revPar (t d : Nat) (kd : NKid) : List Msg := match kd with
  | .node c l r _ _ => [[c, t, d + 1, l, r]]
  | _ => []

theorem win_toFp (tr : Trace Fp) (col : Nat → Nat) (r : Nat) : (win tr col r).map Fp.ofNat = regW tr r col := by
  unfold win regW; rw [List.map_map]; apply List.map_congr_left; intro i _; exact ofNat_cv tr T_NODE r (col i)

theorem cast_cv (tr : Trace Fp) (r x : Nat) : ((cv tr T_NODE r x : Nat) : Fp) = tr.cell T_NODE r x :=
  (cell_eq_cast tr T_NODE r x).symm

theorem ofNat_msgId (k i : Nat) : Fp.ofNat (msgId k i) = (k : Fp) + ((16 : Nat) : Fp) * ((i : Nat) : Fp) := by
  rw [← natCast_eq]; exact toFp_msgId k i

theorem ofNat_npre (c : Nat) : Fp.ofNat (msgId K_NPRE c) = ((K_NPRE : Nat) : Fp) + ((16 : Nat) : Fp) * (c : Fp) :=
  ofNat_msgId _ _
theorem ofNat_npost (c : Nat) :
    Fp.ofNat (msgId K_NPOST c) = ((K_NPRE : Nat) : Fp) + ((16 : Nat) : Fp) * (c : Fp) + ((1 : Nat) : Fp) := by
  rw [← ofNat_npre, ← natCast_eq, ← natCast_eq, ← natCast_add]; congr 1; unfold msgId K_NPOST K_NPRE; omega
theorem ofNat_vpre (c : Nat) : Fp.ofNat (msgId K_VPRE c) = ((K_VPRE : Nat) : Fp) + ((16 : Nat) : Fp) * (c : Fp) :=
  ofNat_msgId _ _
theorem ofNat_vpost (c : Nat) :
    Fp.ofNat (msgId K_VPOST c) = ((K_VPRE : Nat) : Fp) + ((16 : Nat) : Fp) * (c : Fp) + ((1 : Nat) : Fp) := by
  rw [← ofNat_vpre, ← natCast_eq, ← natCast_eq, ← natCast_add]; congr 1; unfold msgId K_VPOST K_VPRE; omega

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem chView (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl)
    (hc : tr.cell T_NODE (s + o) sCH = 1) :
    rowT tr pub (s + o) B_DIGEST false = (revDigs (kidOf tr (s + o))).map Msg.toFp ∧
    rowT tr pub (s + o) B_PARENT true =
      (revPar (cv tr T_NODE s tau) (cv tr T_NODE s depth) (kidOf tr (s + o))).map Msg.toFp := by
  obtain ⟨-, -, -, P, D⟩ := chStartMsgs hL hC hm hc
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by omega
  have hin : o < ℓ := by have := (hC.fields.field _ hm).2; simp at this; omega
  have hdep : tr.cell T_NODE (s + o) depth = tr.cell T_NODE s depth := segConst hL hC (by simp [nodeConst]) hin
  have htau : tr.cell T_NODE (s + o) tau = tr.cell T_NODE s tau := segConst hL hC (by simp [nodeConst]) hin
  rw [P, D]
  unfold kidOf
  rcases isBool hL hr (x := rv) (by simp [boolCols]) with h | h
  · rw [h, if_neg (by rw [cv_zero h]; decide)]; simp [gate, revDigs, revPar]
  · rw [h, if_pos (cv_one h)]
    rw [hdep, htau]
    simp only [gate, if_true, revDigs, revPar, List.replicate_one, List.map_cons, List.map_nil,
      Msg.toFp, digMsg, List.map_append, win_toFp, ofNat_npre, ofNat_npost, ofNat_cv', List.cons_append,
      List.nil_append]
    simp only [cast_cv, ← natCast_eq, natCast_add, and_true]

/-- The value window: `DIGEST` lookups and `VPARENT`. -/
def valDigs (sl : NSlot3) : List Msg := match sl with
  | .val _ i l pre po w => [digMsg (msgId K_VPRE i) l pre] ++ (if w then [digMsg (msgId K_VPOST i) l po] else [])
  | _ => []

def valPar (sl : NSlot3) : List Msg := match sl with
  | .val _ i l _ _ _ => [[i, l]]
  | _ => []

theorem vhView (hC : NodeCtx tr s ℓ fl) {o rV : Nat} (hm : (o, 32) ∈ fl) (hv : tr.cell T_NODE (s + o) sVH = 1) :
    rowT tr pub (s + o) B_PARENT true = [] ∧ rowT tr pub (s + o) B_BMAP true = [] ∧
    rowT tr pub (s + o) B_BMAP false = [] ∧
    rowT tr pub (s + o) B_DIGEST false = (valDigs (slotOf tr s rV (s + o))).map Msg.toFp ∧
    rowT tr pub (s + o) B_VPARENT true = (valPar (slotOf tr s rV (s + o))).map Msg.toFp := by
  obtain ⟨P, B1, B2, D, V⟩ := vhStart hL hC hm hv
  have hin : o < ℓ := by have := (hC.fields.field _ hm); simp at this; have := this.1.pos; omega
  have k : ∀ x ∈ nodeConst, tr.cell T_NODE (s + o) x = tr.cell T_NODE s x := fun x hx => segConst hL hC hx hin
  refine ⟨P, B1, B2, ?_, ?_⟩
  · rw [D, k tv (by simp [nodeConst]), k tw (by simp [nodeConst]), k vid (by simp [nodeConst]),
      k vlen (by simp [nodeConst])]
    unfold slotOf
    rcases isBool hL (nodeStart hL hC).1 (x := tv) (by simp [boolCols]) with h | h
    · rw [h, if_neg (by rw [cv_zero h]; decide), show (0 : Fp) * tr.cell T_NODE s tw = 0 by grind]
      simp [gate, valDigs]
    · rw [h, if_pos (cv_one h), show (1 : Fp) * tr.cell T_NODE s tw = tr.cell T_NODE s tw by grind]
      rcases isBool hL (nodeStart hL hC).1 (x := tw) (by simp [boolCols]) with h2 | h2
      · rw [h2]
        simp only [gate, if_true, List.replicate_one, valDigs, cv_zero h2, decide_false, Bool.false_eq_true,
          if_false, List.append_nil, List.map_cons, List.map_nil, Msg.toFp, digMsg, List.map_append, win_toFp,
          ofNat_vpre, fp_zero_ne_one, List.replicate_zero]
        simp [cast_cv, ← natCast_eq]
      · rw [h2]
        simp only [gate, if_true, List.replicate_one, valDigs, cv_one h2, decide_true, List.cons_append,
          List.nil_append, List.map_cons, List.map_nil, Msg.toFp, digMsg, List.map_append, win_toFp,
          ofNat_vpre, ofNat_vpost, List.singleton_append]
        simp [cast_cv, ← natCast_eq]
  · rw [V, k tv (by simp [nodeConst]), k vid (by simp [nodeConst]), k vlen (by simp [nodeConst])]
    unfold slotOf
    rcases isBool hL (nodeStart hL hC).1 (x := tv) (by simp [boolCols]) with h | h
    · rw [h, if_neg (by rw [cv_zero h]; decide)]; simp [gate, valPar]
    · rw [h, if_pos (cv_one h)]
      simp [gate, valPar, Msg.toFp, cast_cv, ← natCast_eq]

end ZkFormal.NearV3.NodeProof3
