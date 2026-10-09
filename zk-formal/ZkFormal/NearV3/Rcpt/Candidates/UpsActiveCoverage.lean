import ZkFormal.NearV3.Rcpt.Candidates.UpsWalkPhases

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen UpsRows Assembly

theorem native_ups_active_edges (pairs : List (PTrie×PTrie)) (run : TreeRun) (I : Render.UpsInst)
    (ho : InstOk I) (hp : ExactNativeWalkProviders pairs run I) (hci : I.ci=run.terminal.ix)
    (t : Nat) (ht : t<4) (hm : (step I t).mode≤1) :
    (step I t).e∈headEdgeKeys (forestWalkHeads 0 0 pairs)++nodeEdgeKeys (forestStoreViews (pairs.map Prod.fst)).nodes := by
  by_cases h0 : t=0
  · subst t;exact List.mem_append_left _ (exact_native_start_coverage pairs run I hp)
  · have hle:=ups_edge_before_or_terminal I ho t ht hm
    by_cases he : t<I.ts
    · obtain ⟨_,_,_,_,_,_,hf,_⟩:=hp
      obtain ⟨n,s,hs,hkey⟩:=hf t (by omega) he
      exact List.mem_append_right _ (nodeEdgeKeys_of_get hs hkey)
    · have htt : t=I.ts := by omega
      subst t
      obtain ⟨a,s,_,hs,_,_,_,_,hterm⟩:=hp
      rcases hterm with ⟨hcase,_⟩|hkey
      · have hi : I.ci=2 ∨ I.ci=3 := by rcases hcase with hcase|hcase <;> simp [hcase,UCase.ix] at hci <;> omega
        have hmode:=ho.walk.termCase.2.1.mpr hi
        omega
      · exact List.mem_append_right _ (nodeEdgeKeys_of_get hs hkey)

theorem native_ups_active_bmaps (pairs : List (PTrie×PTrie)) (run : TreeRun) (I : Render.UpsInst)
    (ho : InstOk I) (hp : DispatchNativeWalkProviders pairs run I) (hci : I.ci=run.terminal.ix)
    (t : Nat) (ht : t<4) (hm : (step I t).mode=2) :
    [(step I t).e.getD 0 0,(step I t).bm,(step I t).hv]∈nodeBitmapKeys (forestStoreViews (pairs.map Prod.fst)).nodes := by
  have htt:=ups_bitmap_at_terminal I ho t ht hm
  subst t
  have hi:=ho.walk.termCase.2.1.mp hm
  have hc : run.terminal=.BV ∨ run.terminal=.BI := by
    rw [hci] at hi
    cases hterm : run.terminal <;> simp_all [UCase.ix]
  obtain ⟨a,s,_,hs,_,_,_,hid,hbm,_⟩:=hp
  rw [hid]
  exact nodeBitmapKeys_of_get hs (hbm hc)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
