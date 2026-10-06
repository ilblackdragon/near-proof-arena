import ZkFormal.NearV3.Render.Node.TDig2

/-!
# ZkFormal.NearV3.Render.Node.TBm — record traffic: BMAP
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

theorem rc_bm (vs : List NodeS3) (r : NRec) (i : Nat) (hi : i < 16) :
    rowCell vs r (37 + i) = bitOf (bmvOf (rec vs r.n).v) i := by
  unfold rowCell
  simp only [show ¬ 37 + i < 29 by omega, show ¬ 37 + i < 33 by omega, show ¬ 37 + i < 37 by omega,
    show 37 + i < 53 by omega, if_false, if_true, Nat.add_sub_cancel_left]

theorem bmN_eq (vs : List NodeS3) (r : NRec) (h : bmvOf (rec vs r.n).v < 2 ^ 16) :
    bmN (rowCell vs r) = bmvOf (rec vs r.n).v := by
  simp only [bmN]
  rw [List.map_congr_left (g := fun i => 2 ^ i * bitOf (bmvOf (rec vs r.n).v) (0 + i))
    (fun i hi => by rw [rc_bm vs r i (List.mem_range.1 hi), Nat.zero_add])]
  rw [ZkFormal.Near.Render.NodeRow.bitsum]; simp; omega

def gBm (n : Nat) (s : NodeS3) (u : Nat) (fi : F × Nat) : List ZkFormal.Near.Msg :=
  match fi.1 with
  | .bm => if fi.2 = 0 then [[n, bmvOf s.v, (typeOf s.v).2.2.2, u]] else []
  | _ => []

theorem rowN_bmS {vs : List NodeS3} (ok : NodeOk vs) {n p : Nat} (hn : n < vs.length) :
    rowN (rowCell vs (mkR vs n p)) B_BMAP true = gBm n (rec vs n) 0 ((layN vs n).getD p default) := by
  rown_simp
  rw [bmN_eq vs _ (bmv_lt _ (rwf ok hn))]
  simp only [Rc.c184, Rc.c4, Rc.c13, mkR]
  generalize (layN vs n).getD p default = fi
  obtain ⟨f, j⟩ := fi
  cases f <;> simp [gBm, gt, b2n, NodeGen.F.isBm]

theorem rowN_bmR {vs : List NodeS3} (ok : NodeOk vs) {n p : Nat} (hn : n < vs.length) :
    rowN (rowCell vs (mkR vs n p)) B_BMAP false = gBm n (rec vs n) (rec vs n).ubm ((layN vs n).getD p default) := by
  rown_simp
  rw [bmN_eq vs _ (bmv_lt _ (rwf ok hn))]
  simp only [Rc.c184, Rc.c4, Rc.c13, Rc.c173, mkR]
  generalize (layN vs n).getD p default = fi
  obtain ⟨f, j⟩ := fi
  cases f <;> simp [gBm, gt, b2n, NodeGen.F.isBm]
  split <;> simp_all

def tgtBm (n : Nat) (v : NodeV3) (u : Nat) : List ZkFormal.Near.Msg :=
  match v.bmap with | some (bm, hv) => [[n, bm, hv, u]] | none => []

theorem rec_bm {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) (sd : Bool) :
    (recN vs n B_BMAP sd).Perm (tgtBm n (rec vs n).v (if sd then 0 else (rec vs n).ubm)) := by
  rw [recN_lay ok hn B_BMAP sd (gBm n (rec vs n) (if sd then 0 else (rec vs n).ubm)) (fun p _ => by
    cases sd
    · exact rowN_bmR ok hn
    · exact rowN_bmS ok hn)]
  generalize (if sd then 0 else (rec vs n).ubm) = u
  generalize rec vs n = s
  obtain ⟨v, tau, d, res, uses, ubm, dup, hd, repE⟩ := s
  have hz : ∀ (fs : List F), (∀ f ∈ fs, f ≠ .bm) →
      (fs.flatMap fun f => (List.range (f.len (hplenOf v))).flatMap fun i =>
        gBm n ⟨v, tau, d, res, uses, ubm, dup, hd, repE⟩ u (f, i)) = [] := by
    intro fs h
    apply ZkFormal.Near.Render.flatMap_nil'; intro f hf
    apply ZkFormal.Near.Render.flatMap_nil'; intro i _
    cases f <;> first | rfl | exact absurd rfl (h _ hf)
  cases v with
  | leaf k sv m =>
    rw [hz _ (by simp [fieldsOf])]; simp [tgtBm, NodeV3.bmap]
  | ext k kid m =>
    rw [hz _ (by simp [fieldsOf])]; simp [tgtBm, NodeV3.bmap]
  | branch sv kids m =>
    have hw : (branchWins kids).flatMap (fun f => (List.range (f.len 0)).flatMap fun i =>
        gBm n ⟨.branch sv kids m, tau, d, res, uses, ubm, dup, hd, repE⟩ u (f, i)) = [] :=
      ZkFormal.Near.Render.flatMap_nil' (fun f hf => by
        obtain ⟨_, _, _, _, _, _, rfl⟩ := mem_branchWins hf; simp [gBm])
    cases sv with
    | none =>
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        show hplenOf (.branch none kids m) = 0 from rfl, hw]
      simp [gBm, F.len, tgtBm, NodeV3.bmap, bmvOf, isLE, kidsOf, typeOf, List.range_succ]
    | some sl =>
      simp only [fieldsOf, List.cons_append, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
        show hplenOf (.branch (some sl) kids m) = 0 from rfl, hw]
      simp [gBm, F.len, tgtBm, NodeV3.bmap, bmvOf, isLE, kidsOf, typeOf, List.range_succ]

end NodeGen3

end ZkFormal.NearV3.Render
