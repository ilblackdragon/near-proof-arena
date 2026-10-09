import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsSrc
import ZkFormal.NearV3.Extract.Ups.UpsShape
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
attribute [local irreducible] UpsSeg.row UpsSeg.next
theorem ups_srcOk {vs : List NodeS3} {hds : List HeadE} {es : List ValE}
    {others : List Msg} {shaS shaR : Nat → List Fp → Nat} (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hb : Link3.ParentBal vs hds)
    (hvb : Link3.VParentBal vs es) (H : Link3.ShaHyp vs hds es others shaS shaR) {pv : Nat → NearSpec.Bytes}
    (HP : Link3.VPostOk others pv)
    (hpl : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    {v : List UpsSeg} (hw : Wf v) (hbal : UpbBal vs v)
    {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
    (hshape : ∀ k, k < ps.length → SrcShape ci si ti (sdx k) (kd k)
      (srcOf (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) s ps k)) :
    ∀ k, k < ps.length → SrcOk ci si ti (sdx k) (kd k)
      (srcOf (Link3.recsOf (Link3.vpos (Link3.vid0 es)) vs) (Link3.valsPost vs es pv) s ps k) := by
  intro k hk
  have hn := part_sN hN hw hbal hs hL hP k hk
  have hg : ps.getD k (0, 0) = ps[k] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  refine srcOk_of ?_ (hshape k hk)
  simp only [srcOf, hg]
  exact post_nodeOk hN hhw hvw hb hvb H HP hpl hn

end ZkFormal.NearV3.Render.UpsRelay.Extract
