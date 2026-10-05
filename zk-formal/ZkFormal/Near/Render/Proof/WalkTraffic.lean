import ZkFormal.Near.Render.Proof.WalkIdx
import ZkFormal.Near.Render.Proof.WalkLocal

/-!
# ZkFormal.Near.Render.Proof.WalkTraffic — `WalkTrafficStmt`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace WalkTraffic
open SortLocal (ofNat0 ofNat1)

/-- Traffic of the row of step `p` with counter `u`. -/
def rowW (p : Nat × WStep) (u b : Nat) (s : Bool) : List (List Fp) :=
  if b = B_KEYNIB ∧ s = false then
    (if p.2.t.isNone then [] else
      [[Fp.ofNat p.1, Fp.ofNat (p.2.t.getD 0), Fp.ofNat p.2.sym, Fp.ofNat (if p.2.last then 1 else 0)]])
  else if b = B_EDGE ∧ s = false then
    [[Fp.ofNat (p.2.edge.getD 0 0), Fp.ofNat (p.2.edge.getD 1 0), Fp.ofNat p.2.sym,
      Fp.ofNat (p.2.edge.getD 3 0), Fp.ofNat (p.2.edge.getD 4 0), Fp.ofNat u]]
  else if b = B_EDGE ∧ s = true then
    [[Fp.ofNat (p.2.edge.getD 0 0), Fp.ofNat (p.2.edge.getD 1 0), Fp.ofNat p.2.sym,
      Fp.ofNat (p.2.edge.getD 3 0), Fp.ofNat (p.2.edge.getD 4 0), Fp.ofNat (u + 1)]]
  else if b = B_FINAL ∧ s = true then
    (if p.2.last then [[Fp.ofNat p.1, Fp.ofNat (p.2.edge.getD 3 0)]] else [])
  else []

section
variable {st : List (Nat × WStep)} {us : List Nat} {tr : Trace Fp} {pub : List Fp} {H : Nat}
  (hcell : ∀ q col, q < H → col < 12 → tr.cell T_WALK q col = Fp.ofNat (WalkLocal.V st us q col))
include hcell

theorem row {q : Nat} (hq : q < H) (b : Nat) (s : Bool) :
    rowTraffic WalkTab.interactions tr T_WALK q pub b s =
      if q < st.length then rowW (st.getD q default) (us.getD q 0) b s else [] := by
  have hc : ∀ col, col < 12 → tr.cell T_WALK q col = Fp.ofNat (WalkLocal.V st us q col) :=
    fun col h => hcell q col hq h
  simp only [rowTraffic, WalkTab.interactions, WalkTab.edge, send, recv, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, eval_c, eval_add, eval_k,
    WalkTab.act, WalkTab.ws, WalkTab.we, WalkTab.gK, WalkTab.r, WalkTab.t, WalkTab.sym, WalkTab.nN, WalkTab.nI,
    WalkTab.nN2, WalkTab.nI2, WalkTab.u, hc, Nat.reduceLT, natCast_eq, ofNat_add']
  by_cases ha : q < st.length
  · simp only [WalkLocal.V, ha, if_true, walkCell, rowW]
    rcases (show b = 4 ∨ b = 5 ∨ b = 6 ∨ (b ≠ 4 ∧ b ≠ 5 ∧ b ≠ 6) by omega) with rfl | rfl | rfl | ⟨h4, h5, h6⟩ <;>
    cases s <;> cases h1 : (st.getD q default).2.t.isNone <;> cases h2 : (st.getD q default).2.last <;>
    simp [B_KEYNIB, B_EDGE, B_FINAL, ofNat1, ofNat0, fp_zero_ne_one, *] <;> omega
  · simp only [WalkLocal.V, ha, if_false, ofNat0]
    simp [fp_zero_ne_one]

end

theorem rowW_edgeS (p : Nat × WStep) (u : Nat) : rowW p u B_EDGE true =
    [[Fp.ofNat (p.2.edge.getD 0 0), Fp.ofNat (p.2.edge.getD 1 0), Fp.ofNat p.2.sym,
      Fp.ofNat (p.2.edge.getD 3 0), Fp.ofNat (p.2.edge.getD 4 0), Fp.ofNat (u + 1)]] := by
  simp [rowW, B_EDGE, B_KEYNIB]
theorem rowW_edgeR (p : Nat × WStep) (u : Nat) : rowW p u B_EDGE false =
    [[Fp.ofNat (p.2.edge.getD 0 0), Fp.ofNat (p.2.edge.getD 1 0), Fp.ofNat p.2.sym,
      Fp.ofNat (p.2.edge.getD 3 0), Fp.ofNat (p.2.edge.getD 4 0), Fp.ofNat u]] := by
  simp [rowW, B_EDGE, B_KEYNIB]
theorem rowW_final (p : Nat × WStep) (u : Nat) : rowW p u B_FINAL true =
    (if p.2.last then [[Fp.ofNat p.1, Fp.ofNat (p.2.edge.getD 3 0)]] else []) := by
  simp [rowW, B_EDGE, B_KEYNIB, B_FINAL]
theorem rowW_keynib (p : Nat × WStep) (u : Nat) : rowW p u B_KEYNIB false =
    (if p.2.t.isNone then [] else
      [[Fp.ofNat p.1, Fp.ofNat (p.2.t.getD 0), Fp.ofNat p.2.sym, Fp.ofNat (if p.2.last then 1 else 0)]]) := by
  simp [rowW, B_KEYNIB]
theorem rowW_otherS (p : Nat × WStep) (u b : Nat) (h1 : b ≠ B_EDGE) (h2 : b ≠ B_FINAL) : rowW p u b true = [] := by
  simp [rowW, h1, h2]
theorem rowW_otherR (p : Nat × WStep) (u b : Nat) (h1 : b ≠ B_EDGE) (h2 : b ≠ B_KEYNIB) : rowW p u b false = [] := by
  simp [rowW, h1, h2]

theorem edge2 {s : WStep} (h : StepOk s) : s.edge.getD 2 0 = s.sym := by
  rw [h.1]; rfl

theorem edge_toFp {s : WStep} (h : StepOk s) (u : Nat) :
    Msg.toFp (s.edge ++ [u]) = [Fp.ofNat (s.edge.getD 0 0), Fp.ofNat (s.edge.getD 1 0), Fp.ofNat s.sym,
      Fp.ofNat (s.edge.getD 3 0), Fp.ofNat (s.edge.getD 4 0), Fp.ofNat u] := by
  conv => lhs; rw [h.1]
  rfl

section seg
variable {w : List WStep} (hw : WalkIdx w) (r : Nat)
include hw

theorem final_seg :
    ((List.range w.length).flatMap fun j => if (w.getD j default).last then
      [[Fp.ofNat r, Fp.ofNat ((w.getD j default).edge.getD 3 0)]] else []) =
    [[Fp.ofNat r, Fp.ofNat ((w.getD (w.length - 1) default).edge.getD 3 0)]] := by
  have hL := hw.len
  have hsplit : List.range w.length = List.range (w.length - 1) ++ [w.length - 1] := by
    rw [← List.range_succ]; congr 1; omega
  rw [hsplit, List.flatMap_append,
    flatMap_nil' (fun j hj => by
      have := List.mem_range.1 hj
      rw [hw.lasts j (by omega), if_neg (by simp; omega)])]
  have hl : (w.getD (w.length - 1) default).last = true := by rw [hw.lasts _ (by omega)]; simp
  simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, hl, if_true]

theorem keynib_seg :
    ((List.range w.length).flatMap fun j => if (w.getD j default).t.isNone then [] else
      [[Fp.ofNat r, Fp.ofNat ((w.getD j default).t.getD 0), Fp.ofNat (w.getD j default).sym,
        Fp.ofNat (if (w.getD j default).last then 1 else 0)]]) =
    ((List.range (w.length - 1)).map fun t =>
      [r, t, ((w.getD (t + 1) default).edge.getD 2 0), if t + 2 = w.length then 1 else 0]).map Msg.toFp := by
  have hL := hw.len
  have hsplit : List.range w.length = 0 :: (List.range (w.length - 1)).map Nat.succ := by
    rw [← List.range_succ_eq_map]; congr 1; omega
  rw [hsplit, List.flatMap_cons, List.flatMap_map]
  simp only [hw.first.1, Option.isNone_none, if_true, List.nil_append]
  rw [flatMap_single (g := fun t => Msg.toFp [r, t, ((w.getD (t + 1) default).edge.getD 2 0),
      if t + 2 = w.length then 1 else 0])]
  · simp only [List.map_map]; rfl
  · intro t ht
    have ht' := List.mem_range.1 ht
    have h1 := hw.ts (t + 1) (by omega) (by omega)
    rw [h1, edge2 (hw.ok (t + 1) (by omega)), hw.lasts (t + 1) (by omega)]
    simp only [Option.isNone_some, Bool.false_eq_true, if_false, Option.getD_some, Nat.add_sub_cancel]
    simp only [Msg.toFp, List.map_cons, List.map_nil, decide_eq_true_eq]
    congr 4
    split <;> split <;> first | rfl | omega

end seg

end WalkTraffic

theorem walkOff_add_le : ∀ (ws : List (List WStep)) (r : Nat), r < ws.length →
    walkOff ws r + (ws.getD r []).length ≤ (ws.map List.length).sum
  | [], _, h => absurd h (by simp)
  | w :: ws, 0, _ => by simp [walkOff]
  | w :: ws, r + 1, h => by
    rw [walkOff_succ]; simp only [List.getD_cons_succ, List.map_cons, List.sum_cons]
    have := walkOff_add_le ws r (by simpa using h); omega

open WalkTraffic in
/-- **`WalkTrafficStmt`.** -/
theorem walkTraffic_ok : WalkTrafficStmt := by
  intro c e hg _
  have hp : partOf (bundle c.1 e) T_WALK =
      mkTab (2 ^ logOf (walkSteps (walksOf (mkInfo c.1 e))).length) WalkTab.width
        (fun q col => WalkLocal.V (walkSteps (walksOf (mkInfo c.1 e))) (usesL (walkSteps (walksOf (mkInfo c.1 e))))
          q col) := rfl
  obtain ⟨_, hH, hcell⟩ := render_mkTab (by decide) (by decide) hp
  have htf : htf c.1 e T_WALK = walkTraffic (walkViewsOf (walksOf (mkInfo c.1 e))) := rfl
  rw [htf]
  have hidx : ∀ r, r < (walksOf (mkInfo c.1 e)).length → WalkIdx ((walksOf (mkInfo c.1 e)).getD r []) :=
    fun r hr => walkIdx hg (by rw [← walksOf_len hg]; exact hr)
  generalize walksOf (mkInfo c.1 e) = ws at hp hH hcell hidx
  have hle : (walkSteps ws).length ≤ 2 ^ logOf (walkSteps ws).length := le_pow_logOf _
  have hcell' : ∀ q col, q < 2 ^ logOf (walkSteps ws).length → col < 12 →
      (render c.1 e).cell T_WALK q col = Fp.ofNat (WalkLocal.V (walkSteps ws) (usesL (walkSteps ws)) q col) :=
    fun q col hq hc => hcell q col hq hc
  have hrows : ∀ b s, ((List.range ((render c.1 e).height T_WALK)).flatMap fun q =>
      rowTraffic WalkTab.interactions (render c.1 e) T_WALK q (publicOf c) b s) =
      (List.range ws.length).flatMap fun r => (List.range (ws.getD r []).length).flatMap fun j =>
        rowW (r, (ws.getD r []).getD j default) ((usesL (walkSteps ws)).getD (walkOff ws r + j) 0) b s := by
    intro b s
    rw [hH, range_split hle, List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        have := List.mem_range.1 hq'
        rw [row hcell' (by omega), if_neg (by omega)]),
      List.append_nil, walkSteps, stepsFrom_length, range_chunks_var]
    apply flatMap_congr'; intro r hr
    apply flatMap_congr'; intro j hj
    have hr' := List.mem_range.1 hr; have hj' := List.mem_range.1 hj
    have hlt : walkOff ws r + j < (stepsFrom ws 0).length := by
      rw [stepsFrom_length]; have := walkOff_add_le ws r hr'; omega
    rw [row hcell' (by rw [← walkSteps] at hlt; omega), if_pos (by rw [walkSteps]; exact hlt),
      walkSteps, stepsFrom_getD ws 0 r j hr' hj', Nat.zero_add]
  have hok : ∀ r, r < ws.length → ∀ j, j < (ws.getD r []).length → StepOk ((ws.getD r []).getD j default) :=
    fun r hr j hj => (hidx r hr).ok j hj
  apply traffic_of
  · intro b
    rw [hrows]
    apply List.Perm.of_eq
    by_cases h4 : b = B_EDGE
    · subst h4
      simp only [walkTraffic, walkSends, if_true, walkViewsOf, List.flatMap_map, List.map_flatMap, List.map_map]
      apply flatMap_congr'; intro r hr
      rw [flatMap_single]; intro j hj
      rw [rowW_edgeS]; dsimp only [Function.comp_apply]
      rw [edge_toFp (hok r (List.mem_range.1 hr) j (List.mem_range.1 hj))]
    · by_cases h6 : b = B_FINAL
      · subst h6
        simp only [walkTraffic, walkSends, show B_FINAL ≠ B_EDGE by decide, if_false, if_true, walkViewsOf,
          List.map_map]
        rw [← flatMap_single (fun _ _ => rfl)]
        apply flatMap_congr'; intro r hr
        have hr' := List.mem_range.1 hr
        have hw := hidx r hr'
        simp only [rowW_final]
        rw [final_seg hw r]
        simp only [Function.comp_apply, WalkV.edge, List.length_map, List.length_range,
          steps_getD (show (ws.getD r []).length - 1 < (ws.getD r []).length by have := hw.len; omega)]
        rfl
      · rw [flatMap_nil' (fun r _ => flatMap_nil' (fun j _ => rowW_otherS _ _ _ h4 h6))]
        simp [walkTraffic, walkSends, h4, h6]
  · intro b
    rw [hrows]
    apply List.Perm.of_eq
    by_cases h4 : b = B_EDGE
    · subst h4
      simp only [walkTraffic, walkRecvs, if_true, walkViewsOf, List.flatMap_map, List.map_flatMap, List.map_map]
      apply flatMap_congr'; intro r hr
      rw [flatMap_single]; intro j hj
      rw [rowW_edgeR]; dsimp only [Function.comp_apply]
      rw [edge_toFp (hok r (List.mem_range.1 hr) j (List.mem_range.1 hj))]
    · by_cases h5 : b = B_KEYNIB
      · subst h5
        simp only [walkTraffic, walkRecvs, show B_KEYNIB ≠ B_EDGE by decide, if_false, if_true, walkViewsOf,
          List.flatMap_map, List.map_flatMap]
        apply flatMap_congr'; intro r hr
        have hr' := List.mem_range.1 hr
        have hw := hidx r hr'
        simp only [rowW_keynib]
        rw [keynib_seg hw r]
        simp only [List.length_map, List.length_range, List.map_map]
        apply List.map_congr_left; intro t ht
        have ht' := List.mem_range.1 ht
        simp only [Function.comp_apply, WalkV.edge, steps_getD (show t + 1 < (ws.getD r []).length by omega)]
      · rw [flatMap_nil' (fun r _ => flatMap_nil' (fun j _ => rowW_otherR _ _ _ h4 h5))]
        simp [walkTraffic, walkRecvs, h4, h5]

end ZkFormal.Near.Render
