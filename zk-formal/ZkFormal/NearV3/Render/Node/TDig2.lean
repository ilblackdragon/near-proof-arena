import ZkFormal.NearV3.Render.Node.TDig

/-!
# ZkFormal.NearV3.Render.Node.TDig2 — record traffic: PARENT (send), VPARENT, DIGS
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

def gPar (s : NodeS3) (fi : F × Nat) : List ZkFormal.Near.Msg :=
  match fi.1 with
  | .ch w => if fi.2 = 0 ∧ w.look = true then [[w.cid, s.tau, s.depth + 1, w.clen, w.cres]] else []
  | _ => []

def gVp (v : NodeV3) (fi : F × Nat) : List ZkFormal.Near.Msg :=
  match fi.1 with
  | .vh _ => if fi.2 = 0 ∧ tvOf v = true then [[vidOf v, vlenOf v]] else []
  | _ => []

def gDigs (s : NodeS3) (fi : F × Nat) : List ZkFormal.Near.Msg :=
  match fi.1 with
  | .ch w => if w.look = true then [[msgId K_NPRE w.cid, s.tau, fi.2, w.pre.getD fi.2 0]] else []
  | .vh w => if tvOf s.v = true then [[msgId K_VPRE (vidOf s.v), s.tau, fi.2, w.pre.getD fi.2 0]] else []
  | _ => []

theorem rowN_parS (vs : List NodeS3) (r : NRec) :
    rowN (rowCell vs r) B_PARENT true = gPar (rec vs r.n) (r.f, r.idx) := by
  rown_simp
  simp only [Rc.c143, Rc.c137, Rc.c163, Rc.c7, Rc.c138, Rc.c154]
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  simp only
  cases f with
  | ch w =>
    by_cases h : j = 0 ∧ w.look = true
    · obtain ⟨rfl, hl⟩ := h; simp [digOf, gPar, hl, gt, NodeGen.F.chw]
    · have : ¬ (j = 0 ∧ w.look = true) := h
      simp only [digOf, gPar, if_neg this, gt]; simp
  | vh w =>
    by_cases h : j = 0 ∧ tvOf (rec vs rn).v = true
    · obtain ⟨rfl, hl⟩ := h; simp [digOf, gPar, hl, gt]
    · have : ¬ (j = 0 ∧ tvOf (rec vs rn).v = true) := h
      simp only [digOf, gPar, if_neg this, gt]; simp
  | _ => simp [digOf, gPar, gt]

theorem rowN_vpS (vs : List NodeS3) (r : NRec) :
    rowN (rowCell vs r) B_VPARENT true = gVp (rec vs r.n).v (r.f, r.idx) := by
  rown_simp
  simp only [Rc.c142, Rc.c143, Rc.c165, Rc.c166]
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  simp only
  cases f with
  | ch w =>
    by_cases h : j = 0 ∧ w.look = true
    · obtain ⟨rfl, hl⟩ := h; simp [digOf, gVp, hl, gt]
    · have : ¬ (j = 0 ∧ w.look = true) := h
      simp only [digOf, gVp, if_neg this, gt]; simp
  | vh w =>
    by_cases h : j = 0 ∧ tvOf (rec vs rn).v = true
    · obtain ⟨rfl, hl⟩ := h; simp [digOf, gVp, hl, gt]
    · have : ¬ (j = 0 ∧ tvOf (rec vs rn).v = true) := h
      simp only [digOf, gVp, if_neg this, gt]; simp
  | _ => simp [digOf, gVp, gt]

theorem rowN_digsS {vs : List NodeS3} (ok : NodeOk vs) {n p : Nat} (hn : n < vs.length) (hp : p < (layN vs n).length) :
    rowN (rowCell vs (mkR vs n p)) B_DIGS true = gDigs (rec vs n) ((layN vs n).getD p default) := by
  rown_simp
  have hb := row_b ok hn hp false
  simp only [Rc.c181, Rc.c182, Rc.c163, Rc.c23, Rc.c8, mkR, hb]
  generalize (layN vs n).getD p default = fi
  obtain ⟨f, j⟩ := fi
  cases f with
  | ch w => cases hl : w.look <;> simp [gDigs, hl, gt, b2n, NodeGen.F.chw, NodeGen.F.isCh, NodeGen.F.isVh, fbytes]
  | vh w =>
    cases ht : tvOf (rec vs n).v <;> simp [gDigs, ht, gt, b2n, NodeGen.F.chw, NodeGen.F.isCh, NodeGen.F.isVh, fbytes]
  | _ => simp [gDigs, gt, b2n, NodeGen.F.chw, NodeGen.F.isCh, NodeGen.F.isVh]

end NodeGen3

end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
namespace NodeGen3

def tgtPar (s : NodeS3) : List ZkFormal.Near.Msg := s.v.revealed.map fun (c, l, r, _, _) => [c, s.tau, s.depth + 1, l, r]
def tgtVp (v : NodeV3) : List ZkFormal.Near.Msg := match v.value with | some (i, l, _, _, _) => [[i, l]] | none => []
def tgtDigs (s : NodeS3) : List ZkFormal.Near.Msg :=
  (s.v.revealed.flatMap fun (c, _, _, pre, _) => (List.range 32).map fun i => [msgId K_NPRE c, s.tau, i, pre.getD i 0]) ++
  (match s.v.value with
   | some (i, _, pre, _, _) => (List.range 32).map fun j => [msgId K_VPRE i, s.tau, j, pre.getD j 0]
   | none => [])

theorem range0 {β : Type} (G : Nat → List β) (L : Nat) (h0 : ∀ i, i ≠ 0 → G i = []) (hL : 1 ≤ L ∨ G 0 = []) :
    (List.range L).flatMap G = G 0 := by
  rcases Nat.eq_zero_or_pos L with rfl | hpos
  · rcases hL with h | h
    · omega
    · simp [h]
  · obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      ZkFormal.Near.Render.flatMap_nil' (fun i _ => h0 (i + 1) (by omega))]
    simp

theorem kidrev {β : Type} (kids : List NKid) (g : Nat × Nat × Nat × List Nat × List Nat → List β) :
    (kids.filterMap fun k => match k with | .node c l r pre po => some (c, l, r, pre, po) | _ => none).flatMap g =
      kids.flatMap (fun k => match k with | .node c l r pre po => g (c, l, r, pre, po) | _ => []) := by
  induction kids with
  | nil => rfl
  | cons k kids ih => cases k <;> simp [List.filterMap_cons, ih]

theorem tgtPar_branch (sv : Option NSlot3) (kids : List NKid) (m : List Nat) (tau d res : Nat) (uses : List Nat)
    (ubm : Nat) (dup hd : Bool) (repE : Nat) :
    tgtPar ⟨.branch sv kids m, tau, d, res, uses, ubm, dup, hd, repE⟩ =
      kids.flatMap (fun k => match k with | .node c l r pre po => [[c, tau, d + 1, l, r]] | _ => []) := by
  simp only [tgtPar, NodeV3.revealed]
  induction kids with
  | nil => rfl
  | cons k kids ih => cases k <;> simp [List.filterMap_cons, ih]

theorem rec_parS {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    (recN vs n B_PARENT true).Perm (tgtPar (rec vs n)) := by
  rw [recN_lay ok hn B_PARENT true (gPar (rec vs n)) (fun p _ => by rw [rowN_parS]; rfl)]
  have hw := rwf ok hn
  generalize rec vs n = s at hw ⊢
  obtain ⟨v, tau, d, res, uses, ubm, dup, hd, repE⟩ := s
  simp only at hw ⊢
  rw [ZkFormal.Near.Render.flatMap_congr' (fun f _ => range0 (fun i => gPar ⟨v, tau, d, res, uses, ubm, dup, hd, repE⟩ (f, i)) _
    (fun i hi => by cases f <;> simp [gPar, hi]) (by cases f <;> first | (left; simp [F.len]; done) | (right; simp [gPar])))]
  cases v with
  | leaf k sv m => simp [fieldsOf, gPar, NodeV3.revealed, tgtPar]
  | ext k kid m => cases kid <;> simp [fieldsOf, gPar, NodeV3.revealed, kidWin, tgtPar]
  | branch sv kids m =>
    have hwin := wins_flat kids (fun k => match k with
        | .node c l r pre po => [[c, tau, d + 1, l, r]] | _ => [])
      (fun w => gPar ⟨.branch sv kids m, tau, d, res, uses, ubm, dup, hd, repE⟩ (.ch w, 0))
      (fun k w l s => by cases k <;> simp [gPar, kidWin]) rfl
    have hw2 : (branchWins kids).flatMap (fun f => gPar ⟨.branch sv kids m, tau, d, res, uses, ubm, dup, hd, repE⟩ (f, 0)) =
        kids.flatMap (fun k => match k with | .node c l r pre po => [[c, tau, d + 1, l, r]] | _ => []) :=
      Eq.trans (ZkFormal.Near.Render.flatMap_congr' (fun f hf => by
          obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_branchWins hf; rfl)) hwin
    rw [tgtPar_branch]
    cases sv with
    | none =>
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil]
      rw [hw2]; simp [gPar]
    | some sl =>
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil]
      rw [hw2]; simp [gPar]

theorem rec_vpS {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    (recN vs n B_VPARENT true).Perm (tgtVp (rec vs n).v) := by
  rw [recN_lay ok hn B_VPARENT true (gVp (rec vs n).v) (fun p _ => by rw [rowN_vpS]; rfl)]
  have hw := rwf ok hn
  generalize (rec vs n).v = v at hw ⊢
  rw [ZkFormal.Near.Render.flatMap_congr' (fun f _ => range0 (fun i => gVp v (f, i)) _
    (fun i hi => by cases f <;> simp [gVp, hi]) (by cases f <;> first | (left; simp [F.len]; done) | (right; simp [gVp])))]
  cases v with
  | leaf k sv m => cases sv <;> simp [fieldsOf, gVp, tgtVp, tvOf, vidOf, vlenOf, NodeV3.value]
  | ext k kid m => simp [fieldsOf, gVp, tgtVp, NodeV3.value]
  | branch sv kids m =>
    have hw2 : (branchWins kids).flatMap (fun f => gVp (.branch sv kids m) (f, 0)) = [] :=
      ZkFormal.Near.Render.flatMap_nil' (fun f hf => by obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_branchWins hf; rfl)
    cases sv with
    | none =>
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, hw2]
      simp [gVp, tgtVp, NodeV3.value]
    | some sl =>
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, hw2]
      cases sl <;> simp [gVp, tgtVp, tvOf, vidOf, vlenOf, NodeV3.value]

end NodeGen3
end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
namespace NodeGen3

@[simp] theorem flatMap_nil_fun {α β : Type} (l : List α) : (l.flatMap fun _ => ([] : List β)) = [] := by
  induction l <;> simp_all

theorem tgtDigs_branch (sv : Option NSlot3) (kids : List NKid) (m : List Nat) (tau d res : Nat) (uses : List Nat)
    (ubm : Nat) (dup hd : Bool) (repE : Nat) :
    tgtDigs ⟨.branch sv kids m, tau, d, res, uses, ubm, dup, hd, repE⟩ =
      kids.flatMap (fun k => match k with
        | .node c l r pre po => (List.range 32).map fun i => [msgId K_NPRE c, tau, i, pre.getD i 0] | _ => []) ++
      (match (NodeV3.branch sv kids m).value with
       | some (i, _, pre, _, _) => (List.range 32).map fun j => [msgId K_VPRE i, tau, j, pre.getD j 0]
       | none => []) := by
  simp only [tgtDigs]; congr 1; simp only [NodeV3.revealed]
  induction kids with
  | nil => rfl
  | cons k kids ih =>
    cases k <;> simp only [List.filterMap_cons, List.flatMap_cons, List.nil_append, ih] <;> rfl

theorem gDigs_ch (s : NodeS3) (w : Win) :
    (List.range 32).flatMap (fun i => gDigs s (.ch w, i)) =
      if w.look = true then (List.range 32).map fun i => [msgId K_NPRE w.cid, s.tau, i, w.pre.getD i 0] else [] := by
  cases h : w.look <;> simp [gDigs, h, ← List.map_eq_flatMap]

theorem gDigs_vh (s : NodeS3) (w : Win) :
    (List.range 32).flatMap (fun i => gDigs s (.vh w, i)) =
      if tvOf s.v = true then (List.range 32).map fun i => [msgId K_VPRE (vidOf s.v), s.tau, i, w.pre.getD i 0] else [] := by
  cases h : tvOf s.v <;> simp [gDigs, h, ← List.map_eq_flatMap]

theorem rec_digsS {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    (recN vs n B_DIGS true).Perm (tgtDigs (rec vs n)) := by
  rw [recN_lay ok hn B_DIGS true (gDigs (rec vs n)) (fun p hp => rowN_digsS ok hn hp)]
  have hw := rwf ok hn
  generalize rec vs n = s at hw ⊢
  obtain ⟨v, tau, d, res, uses, ubm, dup, hd, repE⟩ := s
  simp only at hw ⊢
  cases v with
  | leaf k sv m =>
    simp only [fieldsOf, List.flatMap_cons, List.flatMap_nil, F.len, gDigs_vh]
    cases sv <;> simp [gDigs, tgtDigs, tvOf, vidOf, NodeV3.value, NodeV3.revealed, valWin]
  | ext k kid m =>
    simp only [fieldsOf, List.flatMap_cons, List.flatMap_nil, F.len, gDigs_ch]
    cases kid <;> simp [gDigs, tgtDigs, kidWin, NodeV3.value, NodeV3.revealed]
  | branch sv kids m =>
    rw [tgtDigs_branch]
    have hwin := wins_flat kids (fun k => match k with
        | .node c l r pre po => (List.range 32).map fun i => [msgId K_NPRE c, tau, i, pre.getD i 0] | _ => [])
      (fun w => (List.range 32).flatMap fun i => gDigs ⟨.branch sv kids m, tau, d, res, uses, ubm, dup, hd, repE⟩ (.ch w, i))
      (fun k w l s => by rw [gDigs_ch]; cases k <;> simp [kidWin]) rfl
    have hw2 : (branchWins kids).flatMap (fun f => (List.range (f.len 0)).flatMap fun i =>
        gDigs ⟨.branch sv kids m, tau, d, res, uses, ubm, dup, hd, repE⟩ (f, i)) =
        kids.flatMap (fun k => match k with
          | .node c l r pre po => (List.range 32).map fun i => [msgId K_NPRE c, tau, i, pre.getD i 0] | _ => []) :=
      Eq.trans (ZkFormal.Near.Render.flatMap_congr' (fun f hf => by
          obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_branchWins hf; rfl)) hwin
    cases sv with
    | none =>
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        List.append_nil, show hplenOf (.branch none kids m) = 0 from rfl]
      rw [hw2]; simp [gDigs, NodeV3.value]
    | some sl =>
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        List.append_nil, show hplenOf (.branch (some sl) kids m) = 0 from rfl]
      rw [hw2]; simp only [F.len]; rw [gDigs_vh]
      refine List.Perm.trans ?_ List.perm_append_comm
      cases sl <;> simp [gDigs, tvOf, vidOf, NodeV3.value, valWin]

end NodeGen3
end ZkFormal.NearV3.Render
