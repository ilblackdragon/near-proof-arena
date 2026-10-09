import ZkFormal.NearV3.Rcpt.Candidates.WalkRanks

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra

theorem rankWalks_member : ∀(ws : List WalkR)(previous : List WStep3)(v : WalkR),
    v∈rankWalks previous ws → ∃p w,w∈ws ∧ v=rankWalk p w ∧
    p.length+w.steps.length≤previous.length+(ws.flatMap (·.steps)).length
  | [],_,_,h=>by simp [rankWalks] at h
  | w::ws,previous,v,h=>by
    simp only [rankWalks,List.mem_cons] at h
    rcases h with rfl|h
    · refine ⟨previous,w,by simp,rfl,?_⟩
      simp only [List.flatMap_cons,List.length_append];omega
    · obtain ⟨p,w',hw,he,hb⟩:=rankWalks_member ws (previous++w.steps) v h
      refine ⟨p,w',by simp [hw],he,?_⟩
      simp only [List.flatMap_cons,List.length_append] at *;omega

theorem rankWalk_semantics (p : List WStep3) (w : WalkR) (i : Nat) :
    ((rankWalk p w).step i).mode=(w.step i).mode ∧
    ((rankWalk p w).step i).sym=(w.step i).sym ∧
    ((rankWalk p w).step i).e=(w.step i).e ∧
    ((rankWalk p w).step i).bm=(w.step i).bm ∧
    ((rankWalk p w).step i).hv=(w.step i).hv := by
  simpa only [stepShape,Prod.mk.injEq] using rankWalk_shape p w i

theorem rankWalks_wf (ws : List WalkR) (h : WalkWf3 ws) : WalkWf3 (rankWalks [] ws) := by
  have hm : ∀v∈rankWalks [] ws,∃p w,w∈ws ∧ v=rankWalk p w ∧ p.length+w.steps.length<P := by
    intro v hv
    obtain ⟨p,w,hw,he,hb⟩:=rankWalks_member ws [] v hv
    refine ⟨p,w,hw,he,?_⟩
    have hn:=h.nrows
    change p.length+w.steps.length<2013265921
    simp only [List.length_nil,Nat.zero_add] at hb
    omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro v hv;obtain ⟨p,w,hw,rfl,_⟩:=hm v hv
    simpa [rankWalk_length] using h.len w hw
  · intro v hv;obtain ⟨p,w,hw,rfl,hb⟩:=hm v hv
    have hc:=h.canon w hw
    refine ⟨hc.1,hc.2.1,?_⟩
    intro st hst
    obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp hst
    have ho : i<w.steps.length := by simpa [rankWalk_length] using hi
    rw [rankWalk_at p w i ho]
    have hs:=hc.2.2 w.steps[i] (List.getElem_mem ho)
    have hr:=rankWalkStep_bounds (p++w.steps.take i) w.steps[i]
    simp only [List.length_append,List.length_take] at hr
    exact ⟨hs.1,by change _<P;omega,by change _<P;omega,hs.2.2.2⟩
  · intro v hv;obtain ⟨p,w,hw,rfl,_⟩:=hm v hv
    exact rankWalk_rows p w (h.rows w hw)
  · intro v hv;obtain ⟨p,w,hw,rfl,_⟩:=hm v hv
    have hs:=h.start w hw
    have he:=rankWalk_semantics p w 0
    exact ⟨he.1.trans hs.1,he.2.1.trans hs.2.1,by rw [he.2.2.1];exact hs.2.2⟩
  · intro v hv;obtain ⟨p,w,hw,rfl,_⟩:=hm v hv
    intro i hi
    have ho : i+1<w.steps.length := by simpa [rankWalk_length] using hi
    have hs:=h.chain w hw i ho
    have he:=rankWalk_semantics p w i
    have hn:=rankWalk_semantics p w (i+1)
    simpa only [he.1,he.2.2.1,hn.1,hn.2.2.1] using hs
  · rw [rankWalks_rows];exact h.nrows

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
