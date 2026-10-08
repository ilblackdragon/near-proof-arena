import ZkFormal.NearV3.Rcpt.Candidates.HeadNodeBalance

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near Render.UpsGen

theorem ups_before_terminal (I : Render.UpsInst) (h : InstOk I) (t : Nat)
    (ht : t<I.ts) : (step I t).mode=0 := by
  have hb:=h.ts
  have hh : t=0 ∨ t=1 ∨ t=2 := by omega
  rcases hh with rfl|rfl|rfl
  · exact h.walk.w0.1
  · exact h.walk.tsStep.1 (by omega)
  · exact h.walk.tsStep.2.1 (by omega)

theorem ups_after_terminal (I : Render.UpsInst) (h : InstOk I) (t : Nat)
    (ht : I.ts<t) (hu : t<4) : (step I t).mode=3 := by
  have hb:=h.ts
  have hh : I.ts=1 ∨ I.ts=2 := by omega
  rcases hh with hs|hs
  · have hm : (step I 1).mode≠0 := by simpa [hs] using h.walk.tsStep.2.2 (by omega)
    have hm2:=h.walk.drain 1 (by omega) (by omega) hm
    have htt : t=2 ∨ t=3 := by omega
    rcases htt with rfl|rfl
    · exact hm2
    · exact h.walk.drain 2 (by omega) (by omega) (by rw [hm2];decide)
  · have hm : (step I 2).mode≠0 := by simpa [hs] using h.walk.tsStep.2.2 (by omega)
    have htt : t=3 := by omega
    subst t
    exact h.walk.drain 2 (by omega) (by omega) hm

theorem ups_bitmap_at_terminal (I : Render.UpsInst) (h : InstOk I) (t : Nat)
    (ht : t<4) (hm : (step I t).mode=2) : t=I.ts := by
  by_cases he : t<I.ts
  · have hh:=ups_before_terminal I h t he;omega
  · by_cases he' : I.ts<t
    · have hh:=ups_after_terminal I h t he' ht;omega
    · omega

theorem ups_edge_before_or_terminal (I : Render.UpsInst) (h : InstOk I) (t : Nat)
    (ht : t<4) (hm : (step I t).mode≤1) : t≤I.ts := by
  by_cases hn : t≤I.ts
  · exact hn
  · have hh:=ups_after_terminal I h t (by omega) ht
    omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
