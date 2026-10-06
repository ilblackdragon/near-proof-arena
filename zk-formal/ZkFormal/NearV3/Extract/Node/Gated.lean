import ZkFormal.NearV3.Extract.Node.Traffic

/-!
# ZkFormal.Near.Extract.NodeGated — DIGEST / PARENT / VSLOT messages of a node
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

/-- The gated (bus, side) pairs. -/
def Gated (bb : Nat) (sd : Bool) : Prop :=
  (bb = B_DIGEST ∧ sd = false) ∨ (bb = B_PARENT ∧ sd = true) ∨ (bb = B_PARENT ∧ sd = false) ∨
    (bb = B_VSLOT ∧ sd = false)

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem gatedQuiet (hC : NodeCtx tr s ℓ fl) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    ∀ r, s ≤ r → r < s + ℓ → tr.cell T_NODE r fs = 0 → rowT tr pub r bb sd = [] := by
  intro r h1 h2 h3
  have Q := quietRow hL hC h1 h2 h3
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Q.1
  · exact Q.2.1
  · exact Q.2.2.1
  · exact Q.2.2.2

theorem gatedFields (hC : NodeCtx tr s ℓ fl) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) = fl.flatMap fun p => rowT tr pub (s + p.1) bb sd := by
  rw [rowsFields hL hC]
  exact flatMap_congr' (fun p hp => fieldGated hL hC hp (gatedQuiet hL hC hg))

/-- A field start that is not a window and not the node start is silent on gated buses. -/
theorem plainStart (hC : NodeCtx tr s ℓ fl) {o L x : Nat} (hm : (o, L) ∈ fl) (ho : 0 < o)
    (hx : tr.cell T_NODE (s + o) x = 1) (hxs : x ∈ states) (h1 : sVH ≠ x) (h2 : sCH ≠ x)
    {bb : Nat} {sd : Bool} (hg : Gated bb sd) : rowT tr pub (s + o) bb sd = [] := by
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by have := hF.pos; omega
  have ha : tr.cell T_NODE (s + o) act = 1 := by simpa using hF.act 0 hF.pos
  have hv := stOnly hL hr ha hx hxs (by simp [states]) h1
  have hc := stOnly hL hr ha hx hxs (by simp [states]) h2
  obtain ⟨P1, P2, hgP, hgD, h0⟩ := innerStart hL hC hm ho
  rw [hv, hc] at hgD; rw [hc] at hgP
  have hgP' : tr.cell T_NODE (s + o) gP = 0 := by rw [hgP]; grind
  have hgD' : tr.cell T_NODE (s + o) gD = 0 := by rw [hgD]; grind
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [rowT_digest, hgD', if_neg h0]; simp [gate]
  · rw [rowT_parentS, hgP']; simp [gate]
  · exact P1
  · exact P2

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
  have z1 := plainStart hL hC (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sH (by simp [states]) (by decide) (by decide) hg
  have z5 := plainStart hL hC (L := 1) (mem _ (by simp [leafFL, keyFL])) (by omega) sF (by simp [states]) (by decide) (by decide) hg
  have zV := plainStart hL hC (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sV (by simp [states]) (by decide) (by decide) hg
  have zM := plainStart hL hC (L := 8) (mem _ (by simp [leafFL, keyFL])) (by omega) sM (by simp [states]) (by decide) (by decide) hg
  unfold leafFL keyFL
  by_cases h1 : cv tr T_NODE s hplen = 1
  · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zV, zM, List.nil_append, List.append_nil]
  · have zK := plainStart hL hC (L := cv tr T_NODE s hplen - 1) (mem _ (by simp [leafFL, keyFL, h1])) (by omega)
      (sK h1) (by simp [states]) (by decide) (by decide) hg
    simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zV, zM, zK, List.nil_append, List.append_nil]

theorem extGated (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s te = 1) {bb : Nat} {sd : Bool} (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) =
      rowT tr pub s bb sd ++ rowT tr pub (s + (5 + cv tr T_NODE s hplen)) bb sd := by
  obtain ⟨hh1, -, hfl, hℓ, sT, sH, sF, sK, sC, sM⟩ := extFields hL hC ht
  have mem : ∀ p ∈ extFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  rw [gatedFields hL hC hg, hfl]
  have z1 := plainStart hL hC (L := 4) (mem _ (by simp [extFL, keyFL])) (by omega) sH (by simp [states]) (by decide) (by decide) hg
  have z5 := plainStart hL hC (L := 1) (mem _ (by simp [extFL, keyFL])) (by omega) sF (by simp [states]) (by decide) (by decide) hg
  have zM := plainStart hL hC (L := 8) (mem _ (by simp [extFL, keyFL])) (by omega) sM (by simp [states]) (by decide) (by decide) hg
  unfold extFL keyFL
  by_cases h1 : cv tr T_NODE s hplen = 1
  · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zM, List.nil_append, List.append_nil]
  · have zK := plainStart hL hC (L := cv tr T_NODE s hplen - 1) (mem _ (by simp [extFL, keyFL, h1])) (by omega)
      (sK h1) (by simp [states]) (by decide) (by decide) hg
    simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      Nat.add_zero]
    simp only [z1, z5, zM, zK, List.nil_append, List.append_nil]

theorem brGated (hC : NodeCtx tr s ℓ fl) (hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) {bb : Nat} {sd : Bool}
    (hg : Gated bb sd) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) =
      rowT tr pub s bb sd ++ ((if brOff tr s = 37 then rowT tr pub (s + 5) bb sd else []) ++
        (List.range (popN tr s)).flatMap fun j => rowT tr pub (s + (brOff tr s + 2 + 32 * j)) bb sd) := by
  have B := brFields hL hC hb
  simp only at B
  rw [← brOff_eq hL hC] at B
  obtain ⟨hfl, hℓ, sT, sVV, sB, -, sM, -⟩ := B
  have mem : ∀ p ∈ brFL (brOff tr s) (popN tr s), p ∈ fl := fun p hp => hfl ▸ hp
  have hoff : brOff tr s = 1 ∨ brOff tr s = 37 := by unfold brOff; split <;> simp
  rw [gatedFields hL hC hg, hfl]
  have zB := plainStart hL hC (L := 2) (mem _ (by simp [brFL])) (by omega) sB (by simp [states]) (by decide) (by decide) hg
  have zM := plainStart hL hC (L := 8) (mem _ (by simp [brFL])) (by omega) sM (by simp [states]) (by decide) (by decide) hg
  unfold brFL
  rcases hoff with ho | ho
  · rw [ho] at zB zM ⊢
    simp only [List.append_nil, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.flatMap_map, Nat.add_zero, zB, zM,
      show (1 : Nat) ≠ 37 by decide, if_false, ite_true]
  · rw [ho] at zB zM sVV ⊢
    obtain ⟨sV, sH⟩ := sVV rfl
    have zV := plainStart hL hC (L := 4) (mem _ (by simp [brFL, ho])) (by omega) sV (by simp [states]) (by decide) (by decide) hg
    simp only [show (37 : Nat) ≠ 1 by decide, if_false, if_true, List.append_nil, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.flatMap_map, Nat.add_zero, zB, zM, zV]

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

def revDigs (kd : NKid) : List Msg := match kd with
  | .node c l _ pre po => [digMsg (msgId K_NPRE c) l pre, digMsg (msgId K_NPOST c) l po]
  | _ => []

def revPar (d : Nat) (kd : NKid) : List Msg := match kd with
  | .node c l r _ _ => [[c, d + 1, l, r]]
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

theorem chView (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl) (ho : 0 < o)
    (hc : tr.cell T_NODE (s + o) sCH = 1) :
    rowT tr pub (s + o) B_DIGEST false = (revDigs (kidOf tr (s + o))).map Msg.toFp ∧
    rowT tr pub (s + o) B_PARENT true = (revPar (cv tr T_NODE s depth) (kidOf tr (s + o))).map Msg.toFp := by
  obtain ⟨P, D⟩ := chStartMsgs hL hC hm ho hc
  obtain ⟨hF, hH⟩ := fieldAt hL hC hm
  have hr : s + o < tr.height T_NODE := by omega
  have hdep : tr.cell T_NODE (s + o) depth = tr.cell T_NODE s depth :=
    segConst hL hC (by simp [nodeConst]) (by have := (hC.fields.field _ hm).2; simp at this; omega)
  rw [P, D]
  unfold kidOf
  rcases isBool hL hr (x := rv) (by simp [boolCols]) with h | h
  · rw [h, if_neg (by rw [cv_zero h]; decide)]; simp [gate, revDigs, revPar]
  · rw [h, if_pos (cv_one h)]
    rw [hdep]
    simp only [gate, if_true, revDigs, revPar, List.replicate_one, List.map_cons, List.map_nil,
      Msg.toFp, digMsg, List.map_append, win_toFp, ofNat_npre, ofNat_npost, ofNat_cv', List.cons_append,
      List.nil_append]
    simp only [cast_cv, ← natCast_eq, natCast_add, and_true]

theorem vhView (hC : NodeCtx tr s ℓ fl) {o n : Nat} (hm : (o, 32) ∈ fl) (ho : 0 < o)
    (hv : tr.cell T_NODE (s + o) sVH = 1) (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) :
    rowT tr pub (s + o) B_PARENT true = [] ∧
    rowT tr pub (s + o) B_DIGEST false = (if cv tr T_NODE s tv = 1 then
      [digMsg (msgId K_VPRE n) 72 (win tr reg (s + o)), digMsg (msgId K_VPOST n) 72 (win tr preg (s + o))]
      else []).map Msg.toFp := by
  obtain ⟨P, D⟩ := vhStart hL hC hm ho hv
  have hin : o < ℓ := by have := (hC.fields.field _ hm); simp at this; have := this.1.pos; omega
  have htv : tr.cell T_NODE (s + o) tv = tr.cell T_NODE s tv := segConst hL hC (by simp [nodeConst]) hin
  have hnid : tr.cell T_NODE (s + o) nid = ((n : Nat) : Fp) := by rw [segConst hL hC (by simp [nodeConst]) hin, hn]
  refine ⟨P, ?_⟩
  rw [D, htv, hnid]
  rcases isBool hL (nodeStart hL hC).1 (x := tv) (by simp [boolCols]) with h | h
  · rw [h, if_neg (by rw [cv_zero h]; decide)]; simp [gate]
  · rw [h, if_pos (cv_one h)]
    simp only [gate, if_true, List.replicate_one, List.map_cons, List.map_nil,
      Msg.toFp, digMsg, List.map_append, win_toFp, ofNat_vpre, ofNat_vpost, List.cons_append, List.nil_append]
    rfl

end ZkFormal.NearV3.NodeProof3
