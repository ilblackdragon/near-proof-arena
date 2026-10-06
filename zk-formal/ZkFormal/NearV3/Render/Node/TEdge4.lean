import ZkFormal.NearV3.Render.Node.TEdge3

/-!
# ZkFormal.NearV3.Render.Node.TEdge4 — EDGE: the messages of a record
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

theorem enum_send (u : List Nat) (l : List (List Nat)) :
    (enumL l).map (eMsg u true) = l.map (· ++ [0]) := by
  apply List.ext_getElem (by simp [enumL])
  intro i h1 h2
  simp at h2
  simp [enumL, eMsg, List.getD_eq_getElem?_getD, h2]

theorem enum_recv (u : List Nat) (l : List (List Nat)) (h : u.length = l.length) :
    (enumL l).map (eMsg u false) = (l.zip u).map fun (e, x) => e ++ [x] := by
  apply List.ext_getElem (by simp [enumL, h])
  intro i h1 h2
  simp [enumL] at h1
  simp [enumL, eMsg, List.getD_eq_getElem?_getD, h1, show i < u.length by omega]

theorem rec_pairs {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    (recPairs vs n).Perm (enumL (edgesOf3 n (rec vs n))) := by
  have hw := rwf ok hn
  rcases h : (rec vs n).v with ⟨k, sv, m⟩ | ⟨k, kid, m⟩ | ⟨sv, kids, m⟩
  · rw [rec_pairs_leaf vs n hw k sv m h]
  · rw [rec_pairs_ext vs n hw k kid m h]
  · exact rec_pairs_branch vs n sv kids m h

theorem rec_edge {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) (sd : Bool) :
    (recN vs n B_EDGE sd).Perm ((enumL (edgesOf3 n (rec vs n))).map (eMsg (rec vs n).uses sd)) := by
  rw [recN_lay ok hn B_EDGE sd (fun fi => (gE vs n fi).map (eMsg (rec vs n).uses sd))
    (fun p hp => rowN_edge_lay ok hn hp sd)]
  have : ((fieldsOf (rec vs n).v).flatMap fun f => (List.range (f.len (hplenOf (rec vs n).v))).flatMap
      fun i => (gE vs n (f, i)).map (eMsg (rec vs n).uses sd)) = (recPairs vs n).map (eMsg (rec vs n).uses sd) := by
    simp only [recPairs, List.map_flatMap]
  rw [this]
  exact (rec_pairs ok hn).map _

theorem rec_edgeS {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    (recN vs n B_EDGE true).Perm ((edgesOf3 n (rec vs n)).map (· ++ [0])) := by
  rw [← enum_send (rec vs n).uses]; exact rec_edge ok hn true

theorem rec_edgeR {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    (recN vs n B_EDGE false).Perm (((edgesOf3 n (rec vs n)).zip (rec vs n).uses).map fun (e, x) => e ++ [x]) := by
  have hu : (rec vs n).uses.length = (edgesOf3 n (rec vs n)).length := by
    have := ok.wf.uses n hn
    rw [rec_eq hn]; exact this
  rw [← enum_recv _ _ hu]; exact rec_edge ok hn false

end NodeGen3

end ZkFormal.NearV3.Render
