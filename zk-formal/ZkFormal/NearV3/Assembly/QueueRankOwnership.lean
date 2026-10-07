import ZkFormal.NearV3.Assembly.QueueRanks

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv

theorem queueRankResolve_lt_total {pre : PTrie} {rs : List ReadRequest} {slot i : Nat}
    {r : ReadRequest} (hr : rs[slot]?=some r) (hi : valueIndex pre r.key=some i) (base : Nat) :
    (queueRankResolve pre rs base slot).2 < queueUsers pre rs i := by
  have hm : (queueRankResolve pre rs base slot).2 ∈ queueUseRanks pre rs base i := by
    exact List.mem_filterMap.mpr ⟨(r,slot),List.mk_mem_zipIdx_iff_getElem?.mpr hr,by simp [hi]⟩
  rw [queueUseRanks_eq] at hm
  simpa [List.mem_range'] using hm

theorem queueForestRankResolve_present (xs : List (PTrie × List ReadRequest)) (start base : Nat)
    {tau slot : Nat} {pre : PTrie} {rs : List ReadRequest} {r : ReadRequest} {b : Bytes}
    (ht : xs[tau]?=some (pre,rs)) (hr : rs[slot]?=some r)
    (hb : pre.find r.key=some (some b)) :
    ∃ p ∈ queueForestProviders start base xs, p.tau=start+tau ∧ p.bytes=b ∧
      (queueForestRankResolve xs base tau slot).1=p.vid ∧
      (queueForestRankResolve xs base tau slot).2<p.users := by
  induction xs generalizing start base tau with
  | nil => simp at ht
  | cons x xs ih =>
    obtain ⟨first,requests⟩ := x
    cases tau with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at ht
      obtain ⟨rfl,rfl⟩ := ht
      obtain ⟨i,hi,_,hp⟩ := queueResolve_present hr hb start base
      refine ⟨_,List.mem_append.mpr (Or.inl hp),by simp,rfl,?_,?_⟩
      · exact congrArg Prod.fst (queueRankResolve_present hr hi base)
      · exact queueRankResolve_lt_total hr hi base
    | succ tau =>
      simp only [List.getElem?_cons_succ] at ht
      obtain ⟨p,hp,hpt,hpb,hvid,hrank⟩ := ih (start+1) (base+(NearSpecV3.valsOf first).length) ht
      exact ⟨p,List.mem_append.mpr (Or.inr hp),by omega,hpb,hvid,hrank⟩

open Qv.Candidates.CombinedWalkGen

theorem plan_rank_provider {pre : PTrie} {v : MainValues} {pres : List PTrie}
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1)
    {w : Walk} (hw : w ∈ plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0))
    {b : Bytes} (hb : w.value=some b) :
    ∃ p ∈ queueForestProviders 0 0 (queueInputs pre v pres),
      p.tau=w.tau ∧ p.bytes=b ∧ w.vid=p.vid ∧ w.users<p.users := by
  obtain ⟨t,rs,ht,hs,hr⟩ := plan_slot hw
  have hh' := (hh (t,rs) (List.mem_of_getElem? ht) _ (List.mem_of_getElem? hs)).1
  change t.find (w.request v.shards).key=some w.value at hh'
  rw [hb] at hh'
  obtain ⟨p,hp,hpt,hpb,hvid,hrank⟩ := queueForestRankResolve_present (queueInputs pre v pres) 0 0 ht hs hh'
  have hv := congrArg Prod.fst hr
  have hu := congrArg Prod.snd hr
  exact ⟨p,hp,by simpa using hpt,hpb,hv.trans hvid,by simpa only [← hu] using hrank⟩

end ZkFormal.NearV3.Assembly
