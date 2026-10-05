import ZkFormal.Near.Render.Proof.RcptTr3

/-!
# ZkFormal.Near.Render.Proof.RcptTraffic — `RcptTrafficStmt`

The honest `rcpt` table is locally legal (`rcptLocal`), so the extraction's
`traffic_of` gives its traffic as `rcptTraffic pub (viewOf tr rcs)`; the
extracted view is the honest one (`view_eq`, and `count_ok` for the number of
receipts), which is the traffic of `honestTraffic`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen RcptProof

theorem views_eq {c : WfClaim} {e : Ext} (hg : Good c.1 e)
    (hL : TableLocal Rcpt.table (render c.1 e) T_RCPT (publicOf c)) {rcs : List RS} (S : Shape (render c.1 e) rcs) :
    viewOf (render c.1 e) rcs = rcptViewsOf (mkInfo c.1 e) := by
  have hn : rcs.length = NN e := by
    have := (count_ok hL S (fun x _ => Link.pubNat_lt c _)).1
    rw [viewOf_len, nPubLE, Link.leN'_pub_field (Link.pub_n (hdr hg)) (Link.wf_bounds c).2.2.2.2.1] at this
    rw [this, NN, hg.len]
  apply List.ext_getElem
  · rw [viewOf_len, hn]; simp [rcptViewsOf, rcptData, NN, Info.nRcpt, mkInfo_e]
  · intro i h1 h2
    rw [viewOf_len] at h1
    have hiN : i < NN e := by omega
    simp only [viewOf, List.getElem_map, rcptViewsOf, rcptData]
    rw [view_eq hg hL S h1, Df_eq hiN]
    simp [Info.nRcpt, mkInfo_e]

/-- **`RcptTrafficStmt`**: the `rcpt` table's traffic is the honest one. -/
theorem rcptTraffic_ok : RcptTrafficStmt := by
  intro c e hg hs
  have hL := rcptLocal c e hg hs
  obtain ⟨rcs, S⟩ := shape_of hL
  have T := ZkFormal.Near.RcptProof.traffic_of hL S
  rw [views_eq hg hL S] at T
  exact T

end RcptP

end ZkFormal.Near.Render
