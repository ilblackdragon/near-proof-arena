import ZkFormal.NearV3.Link.Uniq3
import ZkFormal.NearV3.Rcpt.Candidates.RetainedStoreCount

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Algebra NearSpec NearSpecV3 Link3

/-- Follow actual adjacent duplicate edges to a nonduplicate representative,
retaining the instance tag and exact bytes, including the empty byte string. -/
theorem uniq_representative {us : List UniqE} (h : UniqWf us) (B : Nat → Bytes)
    (hd : ∀ i (hi : i+1<us.length),us[i+1].eq=1 → B us[i+1].eid=B us[i].eid)
    {e : UniqE} (he : e∈us) :
    ∃ f∈us,f.eq=0 ∧ f.tau=e.tau ∧ B f.eid=B e.eid := by
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp he
  induction i with
  | zero =>
    exact ⟨us[0],List.getElem_mem hi,h.first _ (by simp [List.head?_eq_getElem?,hi]),rfl,rfl⟩
  | succ i ih =>
    have him : i<us.length := by omega
    have hm := List.getElem_mem hi
    have hc := (h.canon _ hm).2.2.2.2.1
    by_cases hz : us[i+1].eq=0
    · exact ⟨us[i+1],hm,hz,rfl,rfl⟩
    · have heq : us[i+1].eq=1 := by omega
      obtain ⟨f,hf,hz,ht,hb⟩ := ih him (List.getElem_mem him)
      have hl := h.link i hi
      have hst := (hl.2.2.1 heq).1
      have htau : us[i+1].tau=us[i].tau := by
        rw [hl.2.1,hst,Nat.add_zero,Nat.mod_eq_of_lt (h.canon _ (List.getElem_mem him)).2.2.1]
      exact ⟨f,hf,hz,ht.trans htau.symm,hb.trans (hd i hi heq).symm⟩

/-- Globally derived tagged coverage by the actual nonduplicate uniqueness rows. -/
theorem store_nondup_coverage
    {vs : List NodeS3} {hs : List HeadE} {es : List ValE} {us : List UniqE} {others : List Msg}
    {shaS shaR : Nat → List Fp → Nat}
    (hw : NodeWf3 vs) (hhw : HeadWf hs) (hvw : ValWf es) (huw : UniqWf us)
    (hb : ParentBal vs hs) (hvb : VParentBal vs es) (H : ShaHyp vs hs es others shaS shaR)
    (hD : DigsBal vs hs us) (hDup : DupBal us vs es) (hEnt : EntBal vs es)
    {h : HeadE} (hh : h∈hs) :
    ∀ b∈storeOf (recsOf (vpos (vid0 es)) vs) (valsOf3 vs es) h.tau,
      (h.tau,b)∈(us.filter fun e => e.eq==0).map (fun e => (e.tau,bOf vs es e.eid)) := by
  intro b hbm
  obtain ⟨e,hem,ht,he,_⟩ := store_cov hw hhw hvw huw hb hvb H hD hh b hbm
  obtain ⟨f,hfm,hz,hft,hfb⟩ := uniq_representative huw (bOf vs es)
    (dup_bytes hw hvw huw hDup hEnt) hem
  exact List.mem_map.mpr ⟨f,List.mem_filter.mpr ⟨hfm,by simp [hz]⟩,
    Prod.ext (hft.trans ht) (hfb.trans he)⟩

end ZkFormal.NearV3.Rcpt.Candidates
