import ZkFormal.NearV3.Assembly.QueueRankOwnership
import ZkFormal.NearV3.Assembly.QueuePayload
import ZkFormal.NearV3.Qv.Candidates.RecordProviders

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Qv.Candidates

def queueModeCode : ParseMode → Nat
  | .empty => 0
  | .buffered _ => 1
  | .raw => 2

theorem queueRecord_mode (p : QueueProvider) : (queueRecord p).mode=queueModeCode p.mode := by
  cases hm : p.mode with
  | empty => simp [queueRecord,queuePayload,hm,queueModeCode,ValueGen.Record.mode]
  | raw => simp [queueRecord,queuePayload,hm,queueModeCode,ValueGen.Record.mode]
  | buffered shards =>
    simp only [queueRecord,queuePayload,hm,queueModeCode]
    split <;> rfl

theorem walk_request_mode (w : CombinedWalkGen.Walk) (shards : List Nat) :
    queueModeCode (w.request shards).mode=w.mode := by
  unfold CombinedWalkGen.Walk.request CombinedWalkGen.Walk.mode
  split <;> cases w.kind <;> rfl

theorem queueInputs_modes (pre : PTrie) (v : MainValues) (pres : List PTrie) :
    ∀ x ∈ queueInputs pre v pres, QueueModesByKey x.2 := by
  intro x hx
  simp only [queueInputs,List.mem_cons,List.mem_map] at hx
  rcases hx with rfl | ⟨t,ht,rfl⟩
  · exact mainRequests_modes pre v
  · exact missingRequest_modes t

theorem queueForestRankResolve_mode (xs : List (PTrie × List ReadRequest)) (start base : Nat)
    (hm : ∀ x ∈ xs, QueueModesByKey x.2)
    {tau slot : Nat} {pre : PTrie} {rs : List ReadRequest} {r : ReadRequest} {b : Bytes}
    (ht : xs[tau]?=some (pre,rs)) (hr : rs[slot]?=some r)
    (hb : pre.find r.key=some (some b)) :
    ∃ p ∈ queueForestProviders start base xs, p.tau=start+tau ∧ p.bytes=b ∧
      (queueForestRankResolve xs base tau slot).1=p.vid ∧
      (queueForestRankResolve xs base tau slot).2<p.users ∧ p.mode=r.mode := by
  induction xs generalizing start base tau with
  | nil => simp at ht
  | cons x xs ih =>
    obtain ⟨first,requests⟩ := x
    cases tau with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at ht
      obtain ⟨rfl,rfl⟩ := ht
      obtain ⟨i,hi,hs⟩ := queueSelected_complete (List.mem_of_getElem? hr) hb
      refine ⟨⟨start,base+i,b,(queueRepresentative first requests i).mode,queueUsers first requests i⟩,
        List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨(b,i),hs,rfl⟩)),by simp,rfl,?_,?_,?_⟩
      · exact congrArg Prod.fst (queueRankResolve_present hr hi base)
      · exact queueRankResolve_lt_total hr hi base
      · exact queueRepresentative_mode (hm (first,requests) (by simp)) hs (List.mem_of_getElem? hr) hi
    | succ tau =>
      simp only [List.getElem?_cons_succ] at ht
      obtain ⟨p,hp,hpt,hpb,hvid,hrank,hmode⟩ := ih (start+1) (base+(NearSpecV3.valsOf first).length)
        (fun x hx => hm x (by simp [hx])) ht
      exact ⟨p,List.mem_append.mpr (Or.inr hp),by omega,hpb,hvid,hrank,hmode⟩

open CombinedWalkGen

theorem plan_rank_provider_mode {pre : PTrie} {v : MainValues} {pres : List PTrie}
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1)
    {w : Walk} (hw : w ∈ plan pre v pres (queueForestRankResolve (queueInputs pre v pres) 0))
    {b : Bytes} (hb : w.value=some b) :
    ∃ p ∈ queueForestProviders 0 0 (queueInputs pre v pres),
      p.tau=w.tau ∧ p.bytes=b ∧ w.vid=p.vid ∧ w.users<p.users ∧ (queueRecord p).mode=w.mode := by
  obtain ⟨t,rs,ht,hs,hr⟩ := plan_slot hw
  have hh' := (hh (t,rs) (List.mem_of_getElem? ht) _ (List.mem_of_getElem? hs)).1
  change t.find (w.request v.shards).key=some w.value at hh'
  rw [hb] at hh'
  obtain ⟨p,hp,hpt,hpb,hvid,hrank,hmode⟩ := queueForestRankResolve_mode
    (queueInputs pre v pres) 0 0 (queueInputs_modes pre v pres) ht hs hh'
  have hv := congrArg Prod.fst hr
  have hu := congrArg Prod.snd hr
  refine ⟨p,hp,by simpa using hpt,hpb,hv.trans hvid,by simpa only [← hu] using hrank,?_⟩
  rw [queueRecord_mode,hmode,walk_request_mode]

end ZkFormal.NearV3.Assembly
