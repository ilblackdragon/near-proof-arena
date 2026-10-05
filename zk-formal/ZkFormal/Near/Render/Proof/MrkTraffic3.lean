import ZkFormal.Near.Render.Proof.MrkTraffic2

/-!
# ZkFormal.Near.Render.Proof.MrkTraffic3 — `MrkTrafficStmt`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace MrkTraffic
open MrkGen

theorem shape_rec {n : Nat} (hn : 1 ≤ n) {x : Nat × Nat × Bool} (hx : x ∈ mrkShape n) :
    RecOk n (x.1, x.2.1, x.2.2, 0) := by
  obtain ⟨_, rok, _, _⟩ := recs_facts n hn
  apply rok
  rw [recs_eq, List.mem_flatMap]
  refine ⟨x, hx, ?_⟩
  have := expand_head x
  cases h : expand x with
  | nil => exact absurd h (expand_ne x)
  | cons a l => rw [h] at this; simp at this; simp [this]

def isH (nd : MrkNode) : Bool := match nd with | .hashed .. => true | _ => false

theorem isH_gNode (lv : List (List MNode)) (x : Nat × Nat × Bool) : isH (gNode lv x) = x.2.2 := by
  obtain ⟨j, i, h⟩ := x; cases h <;> rfl

theorem hashedBefore_eq {n : Nat} (hn : 1 ≤ n) (lv : List (List MNode)) {k : Nat} (hk : k < (mrkShape n).length)
    (hh : (mrkShape n)[k].2.2 = true) :
    hashedBefore ((mrkShape n).map (gNode lv)) k = qBase n (mrkShape n)[k].1 + (mrkShape n)[k].2.1 := by
  have := levels_hashedBefore n (n + 1) 0 hn (by simp [size]) k hk hh
  simp only [show mrkLevels (n + 1) (0 + 1) (size n 0) = mrkShape n from rfl, show qBase n (0 + 1) = 0 from rfl,
    Nat.add_zero] at this
  rw [← this, hashedBefore, ← List.map_take, List.filter_map, List.length_map]
  congr 2
  funext x; simp only [Function.comp_apply]; exact isH_gNode lv x

end MrkTraffic

end ZkFormal.Near.Render

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option maxHeartbeats 1000000 in
open MrkTraffic MrkGen in
/-- **`MrkTrafficStmt`.** -/
theorem mrkTraffic_ok : MrkTrafficStmt := by
  intro c e hg
  have hnI : (mkInfo c.1 e).nRcpt = e.rs.length := rfl
  have hn1 : 1 ≤ (mkInfo c.1 e).nRcpt := by rw [hnI, hg.len]; exact hg.n_pos
  have hp : partOf (bundle c.1 e) T_MRK =
      mkTab (2 ^ logOf ((recs (mkInfo c.1 e).nRcpt).length + 2)) Mrk.width
        (cell (mkInfo c.1 e).nRcpt ((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e)))
          (recs (mkInfo c.1 e).nRcpt)) := rfl
  obtain ⟨_, hH, hcell⟩ := render_mkTab (by decide) (by decide) hp
  have htf : htf c.1 e T_MRK = mrkTraffic (publicOf c)
      ⟨(mkInfo c.1 e).nRcpt, topJ (mkInfo c.1 e).nRcpt,
        ((((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))).getD (topJ (mkInfo c.1 e).nRcpt) []).getD 0 default).id,
        ((((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))).getD (topJ (mkInfo c.1 e).nRcpt) []).getD 0 default).len,
        (mrkShape (mkInfo c.1 e).nRcpt).map (gNode ((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))))⟩ := rfl
  rw [htf]
  -- digests of the children
  have hdig : ∀ x ∈ mrkShape (mkInfo c.1 e).nRcpt,
      (ch ((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))) x.1 (2 * x.2.1)).dig.length = 32 ∧
      (x.2.2 = true → (ch ((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))) x.1 (2 * x.2.1 + 1)).dig.length = 32) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, _⟩ := shape_rec hn1 hx
    simp only at h1 h2 h3 h4
    have hsz : size (mkInfo c.1 e).nRcpt x.1 = (size (mkInfo c.1 e).nRcpt (x.1 - 1) + 1) / 2 := by
      obtain ⟨j', hj'⟩ : ∃ j', x.1 = j' + 1 := ⟨x.1 - 1, by omega⟩
      rw [hj']; rfl
    simp only [ch, lv_getD (mkInfo c.1 e) (show x.1 - 1 < (mkInfo c.1 e).nRcpt + 2 by omega)]
    refine ⟨levels_getD_dig _ _ _ (by omega), fun hh => levels_getD_dig _ _ _ ?_⟩
    rw [hh] at h4; simp at h4; omega
  obtain ⟨_, rok, _, _⟩ := recs_facts _ hn1
  have hlen := le_pow_logOf ((recs (mkInfo c.1 e).nRcpt).length + 2)
  have hcell' : ∀ q col, q < 2 ^ logOf ((recs (mkInfo c.1 e).nRcpt).length + 2) → col < 58 →
      (render c.1 e).cell T_MRK q col = Fp.ofNat (cell (mkInfo c.1 e).nRcpt
        ((List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e))) (recs (mkInfo c.1 e).nRcpt) q col) :=
    fun q col hq hc => hcell q col hq hc
  generalize (List.range ((mkInfo c.1 e).nRcpt + 2)).map (levels (mkInfo c.1 e)) = lv at *
  generalize (mkInfo c.1 e).nRcpt = n at *
  have hrows : ∀ b s, ((List.range ((render c.1 e).height T_MRK)).flatMap fun q =>
      rowTraffic Mrk.interactions (render c.1 e) T_MRK q (publicOf c) b s) =
      rowRoot n lv (publicOf c) b s ++ (mrkShape n).flatMap (fun x => (expand x).flatMap (fun r => rowM n lv r b s)) := by
    intro b s
    rw [hH, range_split (show (recs n).length + 1 ≤ _ by omega), List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        have := List.mem_range.1 hq'
        exact row_pad hcell' (by omega) (by omega) (by omega) b s),
      List.append_nil, List.range_succ_eq_map, List.flatMap_cons, row_root hcell' (by omega), List.flatMap_map]
    congr 1
    rw [flatMap_congr' (g := fun k => rowM n lv ((recs n).getD k default) b s) (fun k hk => by
        have hk' := List.mem_range.1 hk
        refine row_node hcell' (by omega) (by omega) (by simpa using hk') (fun j i p hr => ?_) b s
        have hm : (recs n).getD (k + 1 - 1) default ∈ recs n := by
          simp only [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
          exact List.getElem_mem _
        have := (rok _ hm).2.2.2.2.1
        rw [hr] at this; exact this rfl),
      show ((List.range (recs n).length).flatMap fun k => rowM n lv ((recs n).getD k default) b s) =
        (recs n).flatMap (fun r => rowM n lv r b s) from
        (flatMap_getD (default : Rec) (recs n) (fun r => rowM n lv r b s)).symm,
      recs_eq, List.flatMap_assoc]
  have hqs : ((mrkShape n).map (gNode lv)).zip (List.range ((mrkShape n).map (gNode lv)).length) =
      (List.range (mrkShape n).length).map fun k => (gNode lv ((mrkShape n).getD k default), k) := by
    rw [zip_range_getD (default : MrkNode), List.length_map]
    apply List.map_congr_left; intro k hk
    have hk' := List.mem_range.1 hk
    simp [List.getD_eq_getElem?_getD, hk']
  have hmem : ∀ k, k < (mrkShape n).length → (mrkShape n).getD k default ∈ mrkShape n := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact List.getElem_mem _
  have hgetD : ∀ k (hk : k < (mrkShape n).length), (mrkShape n).getD k default = (mrkShape n)[k] := by
    intro k hk; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  apply traffic_of
  · intro b
    rw [hrows, flatMap_getD default (mrkShape n)]
    apply List.Perm.of_eq
    dsimp only [mrkTraffic, mrkSends]
    rw [hqs]
    by_cases h0 : b = B_BYTES
    · subst h0
      simp only [if_true, rowRoot, show ¬ (B_BYTES = B_DIGEST ∧ true = false) by decide,
        show ¬ (B_BYTES = B_MPOS ∧ true = false) by decide, if_false, List.nil_append, List.flatMap_map,
        List.map_flatMap]
      apply flatMap_congr'; intro k hk
      have hk' := List.mem_range.1 hk
      obtain ⟨d1, d2⟩ := hdig _ (hmem k hk')
      rcases hx : (mrkShape n).getD k default with ⟨j, i, h⟩
      rw [hx] at d1 d2
      cases h with
      | true =>
        rw [node_bytes n lv j i d1 (d2 rfl)]
        simp only [gNode, if_true]
        rw [hashedBefore_eq hn1 lv hk' (by rw [← hgetD k hk', hx]), ← hgetD k hk', hx]
      | false => rw [node_bytesP]; rfl
    · by_cases h9 : b = B_MPOS
      · subst h9
        simp only [show B_MPOS ≠ B_BYTES by decide, if_false, if_true, rowRoot,
          show ¬ (B_MPOS = B_DIGEST ∧ true = false) by decide, show ¬ (B_MPOS = B_MPOS ∧ true = false) by decide,
          List.nil_append, List.map_map]
        rw [← flatMap_single (f := fun k => [_]) (fun _ _ => rfl)]
        apply flatMap_congr'; intro k hk
        have hk' := List.mem_range.1 hk
        rcases hx : (mrkShape n).getD k default with ⟨j, i, h⟩
        have hx' : (mrkShape n).getD k (0, 0, false) = (j, i, h) := hx
        rw [node_mposS]
        simp only [Function.comp_apply, mrkPos, hx']
        cases h with
        | true =>
          simp only [gNode, if_true]
          rw [hashedBefore_eq hn1 lv hk' (by rw [← hgetD k hk', hx]), ← hgetD k hk', hx]
          rfl
        | false => rw [hx]; rfl
      · rw [flatMap_nil' (fun k _ => flatMap_nil' (fun r _ => rowM_otherS n lv r b h0 h9))]
        simp [rowRoot, h0, h9]
  · intro b
    rw [hrows, flatMap_getD default (mrkShape n)]
    apply List.Perm.of_eq
    dsimp only [mrkTraffic, mrkRecvs]
    rw [hqs]
    by_cases h1 : b = B_DIGEST
    · subst h1
      simp only [if_true, rowRoot, and_self, show ¬ (B_DIGEST = B_MPOS) by decide, false_and, if_false,
        List.append_nil, List.flatMap_map, List.map_cons, List.map_flatMap, List.cons_append, List.nil_append]
      rw [List.cons.injEq]
      refine ⟨?_, ?_⟩
      · simp only [Msg.toFp, digMsg, List.map_append, List.map_cons, List.map_nil, List.map_map, List.cons_append,
          List.nil_append, List.cons.injEq, true_and]
        apply List.map_congr_left; intro x _
        simp only [Function.comp_apply, pubNat, Fp.ofNat_toNat]
      · apply flatMap_congr'; intro k hk
        have hk' := List.mem_range.1 hk
        obtain ⟨d1, d2⟩ := hdig _ (hmem k hk')
        rcases hx : (mrkShape n).getD k default with ⟨j, i, h⟩
        rw [hx] at d1 d2
        rw [node_digest n lv j i h d1 d2]
        cases h <;> rfl
    · by_cases h9 : b = B_MPOS
      · subst h9
        simp only [show B_MPOS ≠ B_DIGEST by decide, if_false, if_true, rowRoot, false_and, and_self,
          List.nil_append, List.flatMap_map, List.map_cons, List.map_flatMap, List.cons_append]
        rw [List.cons.injEq]
        refine ⟨rfl, ?_⟩
        apply flatMap_congr'; intro k hk
        rcases hx : (mrkShape n).getD k default with ⟨j, i, h⟩
        have hx' : (mrkShape n).getD k (0, 0, false) = (j, i, h) := hx
        rw [node_mposR]
        simp only [mrkPos, hx', gNode]
        cases h <;> rfl
      · rw [flatMap_nil' (fun k _ => flatMap_nil' (fun r _ => rowM_otherR n lv r b h1 h9))]
        simp [rowRoot, h1, h9]

end ZkFormal.Near.Render
