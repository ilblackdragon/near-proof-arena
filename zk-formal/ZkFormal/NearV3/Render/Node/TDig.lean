import ZkFormal.NearV3.Render.Node.TLay

/-!
# ZkFormal.NearV3.Render.Node.TDig — record traffic: DIGEST, PARENT (send), VPARENT, DIGS
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

def w32 (l : List Nat) : List Nat := (List.range 32).map fun j => l.getD (0 + j) 0

/-- `DIGEST` receives of a field position. -/
def gDig (v : NodeV3) (fi : F × Nat) : List ZkFormal.Near.Msg :=
  match fi.1 with
  | .ch w => if fi.2 = 0 ∧ w.look = true then
      [[msgId K_NPRE w.cid, w.clen] ++ w32 w.pre, [msgId K_NPRE w.cid + 1, w.clen] ++ w32 w.post] else []
  | .vh w => if fi.2 = 0 ∧ tvOf v = true then
      [[msgId K_VPRE (vidOf v), vlenOf v] ++ w32 w.pre] ++
        (if twOf v then [[msgId K_VPRE (vidOf v) + 1, vlenOf v] ++ w32 w.post] else []) else []
  | _ => []

theorem regN_reg (vs : List NodeS3) (r : NRec) : regN (rowCell vs r) 72 =
    (List.range 32).map fun i => (match r.f.win with | some w => w.pre.getD (r.idx + i) 0 | none => 0) := by
  simp only [regN]; apply List.map_congr_left; intro i hi; exact rc_reg vs r i (List.mem_range.1 hi)

theorem regN_preg (vs : List NodeS3) (r : NRec) : regN (rowCell vs r) 104 =
    (List.range 32).map fun i => (match r.f.win with | some w => w.post.getD (r.idx + i) 0 | none => 0) := by
  simp only [regN]; apply List.map_congr_left; intro i hi; exact rc_preg vs r i (List.mem_range.1 hi)

theorem rowN_digR (vs : List NodeS3) (r : NRec) :
    rowN (rowCell vs r) B_DIGEST false = gDig (rec vs r.n).v (r.f, r.idx) := by
  rown_simp
  rw [regN_reg, regN_preg]
  simp only [Rc.c142, Rc.c140, Rc.c141, Rc.c183]
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  simp only
  cases f with
  | ch w =>
    by_cases h : j = 0 ∧ w.look = true
    · obtain ⟨rfl, hl⟩ := h; simp [digOf, gDig, hl, gt, w32, NodeGen.F.win]
    · have : ¬ (j = 0 ∧ w.look = true) := h
      simp only [digOf, gDig, if_neg this, gt]; simp
  | vh w =>
    by_cases h : j = 0 ∧ tvOf (rec vs rn).v = true
    · obtain ⟨rfl, hl⟩ := h
      cases htw : twOf (rec vs rn).v <;> simp [digOf, gDig, hl, htw, gt, w32, NodeGen.F.win, b2n]
    · have : ¬ (j = 0 ∧ tvOf (rec vs rn).v = true) := h
      simp only [digOf, gDig, if_neg this, gt]; simp
  | _ => simp [digOf, gDig, gt]


end NodeGen3

end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
namespace NodeGen3

/-- The per-record `DIGEST` target. -/
def tgtDig (v : NodeV3) : List ZkFormal.Near.Msg :=
  (v.revealed.flatMap fun (c, l, _, pre, po) => [digMsg (msgId K_NPRE c) l pre, digMsg (msgId K_NPOST c) l po]) ++
  (match v.value with
   | some (i, l, pre, po, w) => [digMsg (msgId K_VPRE i) l pre] ++ (if w then [digMsg (msgId K_VPOST i) l po] else [])
   | none => [])

theorem npost (c : Nat) : msgId K_NPRE c + 1 = msgId K_NPOST c := by simp [msgId, K_NPRE, K_NPOST]; omega
theorem vpost (c : Nat) : msgId K_VPRE c + 1 = msgId K_VPOST c := by simp [msgId, K_VPRE, K_VPOST]; omega

theorem gDig_i (v : NodeV3) (f : F) (i : Nat) (hi : i ≠ 0) : gDig v (f, i) = [] := by
  cases f <;> simp [gDig, hi]

theorem range_gDig (v : NodeV3) (f : F) (L : Nat) (hL : 1 ≤ L ∨ gDig v (f, 0) = []) :
    (List.range L).flatMap (fun i => gDig v (f, i)) = gDig v (f, 0) := by
  rcases Nat.eq_zero_or_pos L with rfl | hpos
  · rcases hL with h | h
    · omega
    · simp [h]
  · obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      ZkFormal.Near.Render.flatMap_nil' (fun i _ => gDig_i v f (i + 1) (by omega))]
    simp

theorem map32' (l : List Nat) (h : l.length = 32) : (List.range 32).map (fun j => l[j]?.getD 0) = l := by
  have := map32 l h; simpa [List.getD_eq_getElem?_getD] using this

theorem kid32 {k : NKid} (hk : k.wf) : ∀ c l r pre po, k = .node c l r pre po → pre.length = 32 ∧ po.length = 32 := by
  intro c l r pre po h; subst h; exact hk

theorem tgtDig_branch (sv : Option NSlot3) (kids : List NKid) (m : List Nat) :
    tgtDig (.branch sv kids m) = kids.flatMap (fun k => match k with
        | .node c l r pre po => [digMsg (msgId K_NPRE c) l pre, digMsg (msgId K_NPOST c) l po] | _ => []) ++
      (match (NodeV3.branch sv kids m).value with
       | some (i, l, pre, po, w) => [digMsg (msgId K_VPRE i) l pre] ++ (if w then [digMsg (msgId K_VPOST i) l po] else [])
       | none => []) := by
  simp only [tgtDig]; congr 1; simp only [NodeV3.revealed]
  induction kids with
  | nil => rfl
  | cons k kids ih => cases k <;> simp [List.filterMap_cons, ih]

theorem rec_digR {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    (recN vs n B_DIGEST false).Perm (tgtDig (rec vs n).v) := by
  rw [recN_lay ok hn B_DIGEST false (gDig (rec vs n).v) (fun p _ => by rw [rowN_digR]; rfl)]
  have hw := rwf ok hn
  generalize (rec vs n).v = v at hw ⊢
  have hfl : ∀ fs : List F, (∀ f ∈ fs, 1 ≤ f.len (hplenOf v) ∨ gDig v (f, 0) = []) →
      (fs.flatMap fun f => (List.range (f.len (hplenOf v))).flatMap fun i => gDig v (f, i)) =
        fs.flatMap fun f => gDig v (f, 0) := by
    intro fs h
    exact ZkFormal.Near.Render.flatMap_congr' (fun f hf => range_gDig v f _ (h f hf))
  rw [hfl _ (fun f hf => by
    cases f <;> first | (left; simp [F.len]; done) | (right; simp [gDig]))]
  cases v with
  | leaf k sv m =>
    obtain ⟨-, hs, -⟩ := hw
    cases sv with
    | ref l h => simp [fieldsOf, gDig, tgtDig, tvOf, NodeV3.value, NodeV3.revealed]
    | val l i vl pre po wr =>
      obtain ⟨-, h1, h2, -⟩ := hs
      cases wr <;> simp [fieldsOf, gDig, tgtDig, tvOf, vidOf, vlenOf, twOf, NodeV3.value, NodeV3.revealed, valWin,
        w32, map32 _ h1, map32 _ h2, map32' _ h1, map32' _ h2, digMsg, vpost]
  | ext k kid m =>
    obtain ⟨-, -, hk, -⟩ := hw
    cases kid with
    | none => simp [fieldsOf, gDig, tgtDig, kidWin, NodeV3.value, NodeV3.revealed]
    | hash h => simp [fieldsOf, gDig, tgtDig, kidWin, NodeV3.value, NodeV3.revealed]
    | node c l r pre po =>
      obtain ⟨h1, h2⟩ := hk
      simp [fieldsOf, gDig, tgtDig, kidWin, NodeV3.value, NodeV3.revealed, w32, map32 _ h1, map32 _ h2, map32' _ h1, map32' _ h2, digMsg, npost]
  | branch sv kids m =>
    obtain ⟨-, hs, hk, -⟩ := hw
    have hwin : (branchWins kids).flatMap (fun f => gDig (.branch sv kids m) (f, 0)) =
        kids.flatMap (fun k => match k with
          | .node c l r pre po => [digMsg (msgId K_NPRE c) l pre, digMsg (msgId K_NPOST c) l po] | _ => []) := by
      have := wins_flat kids (fun k => match k with
          | .node c l r pre po => [[msgId K_NPRE c, l] ++ w32 pre, [msgId K_NPRE c + 1, l] ++ w32 po] | _ => [])
        (fun w => gDig (.branch sv kids m) (.ch w, 0)) (fun k w l s => by cases k <;> simp [gDig, kidWin]) rfl
      refine Eq.trans (Eq.trans (ZkFormal.Near.Render.flatMap_congr' (fun f hf => by
          obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_branchWins hf; rfl)) this) ?_
      apply ZkFormal.Near.Render.flatMap_congr'; intro k hkm
      cases hkk : k with
      | node c l' r pre po =>
        have h12 := kid32 (hk k hkm) c l' r pre po hkk
        simp [w32, map32' _ h12.1, map32' _ h12.2, digMsg, npost]
      | _ => rfl
    rw [tgtDig_branch]
    cases sv with
    | none =>
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        NodeV3.value, List.append_nil]
      rw [hwin]
      simp [gDig]
    | some sl =>
      have hs' := hs sl rfl
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        List.append_nil]
      rw [hwin]
      simp only [gDig, List.nil_append, List.append_nil, List.append_assoc]
      refine List.perm_append_comm.trans ?_
      cases sl with
      | ref l h => simp [tvOf, NodeV3.value]
      | val l i vl pre po wr =>
        obtain ⟨-, h1, h2, -⟩ := hs'
        cases wr <;> simp [tvOf, vidOf, vlenOf, twOf, NodeV3.value, valWin, w32, map32' _ h1, map32' _ h2, digMsg,
          vpost]

end NodeGen3
end ZkFormal.NearV3.Render
