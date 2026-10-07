import ZkFormal.NearV3.Qv.Extract.CounterProvider
import ZkFormal.NearV3.Qv.Extract.WalkIndex

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link
open Candidates.ValueTable

private theorem selected_map {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    (l.filter p).map f=l.flatMap (fun x => if p x then [f x] else []) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h,ih]

/-- Every present physical queue request has a parser record with the same
canonical value ID, transition ID, and mode. No extra provider premise is used. -/
theorem physical_provider_exists {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    (q : WalkChain tr tt) (v : ParserChain tr tt (segEnd 0 q.segs))
    (hbalance : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tt pub B_QVC true m=
      tableBusCount Candidates.CombinedTable.interactions tr tt pub B_QVC false m) :
    ∀ w∈q.segs, tr.cell tt w.1 Candidates.CombinedTable.absent=0 →
      ∃ p∈v.segs, providerKey tr tt p.1 pub=requestKey tr tt w.1 := by
  let present := q.segs.filter (fun w => decide (tr.cell tt w.1 Candidates.CombinedTable.absent=0))
  let requests := present.map (fun w => (requestKey tr tt w.1,cv tr tt w.1 Candidates.ValueTable.users))
  let providers := v.segs.map (fun p => (providerKey tr tt p.1 pub,cv tr tt p.1 Candidates.ValueTable.users))
  have hp : ∀ p∈providers, p.1.length=3 ∧ Canon p.1 := by
    intro p hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact providerKey_canon _ _ _ _
  have hr : ∀ r∈requests, r.1.length=3 ∧ Canon r.1 ∧ r.2<P := by
    intro r hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    exact ⟨(requestKey_canon _ _ _).1,(requestKey_canon _ _ _).2,cv_lt _ _ _ _⟩
  have hbound : requests.length<P := by
    have hh := q.length_le_height
    have ht := height_le hL
    have hf := List.length_filter_le (fun w => decide (tr.cell tt w.1 Candidates.CombinedTable.absent=0)) q.segs
    simp only [requests,List.length_map]
    dsimp [present]
    unfold P
    omega
  have hn (sd : Bool) :
      ((providers.map (fun p => p.1++[if sd then 0 else p.2]) ++
        requests.map (fun r => r.1++[if sd then r.2+1 else r.2])).map Msg.toFp)=
      v.segs.map (fun p => Parser.endpointMessage tr tt p.1 pub sd) ++
      q.segs.flatMap (fun p => if tr.cell tt p.1 Candidates.CombinedTable.absent=0 then
        [counterMessage tr tt p.1 sd] else []) := by
    simp only [List.map_append,providers,requests,List.map_map]
    have he : (fun x : Nat × Nat => Msg.toFp (providerKey tr tt x.1 pub ++
        [if sd then 0 else cv tr tt x.1 Candidates.ValueTable.users]))=
        (fun x => Parser.endpointMessage tr tt x.1 pub sd) := by
      funext x; exact endpoint_natural _ _ _ _ _
    have hw : (fun x : Nat × Nat => Msg.toFp (requestKey tr tt x.1 ++
        [if sd then cv tr tt x.1 Candidates.ValueTable.users+1 else cv tr tt x.1 Candidates.ValueTable.users]))=
        (fun x => counterMessage tr tt x.1 sd) := by
      funext x; exact request_natural _ _ _ _
    simp only [Function.comp_def] at *
    rw [he,hw]
    congr 1
    simpa only [present,decide_eq_true_eq] using selected_map q.segs
      (fun w => decide (tr.cell tt w.1 Candidates.CombinedTable.absent=0))
      (fun w => counterMessage tr tt w.1 sd)
  have hb := counter_logical_balance hL q v hbalance
  have hperm : ((providers.map (fun p => p.1++[0]) ++ requests.map (fun r => r.1++[r.2+1])).map Msg.toFp).Perm
      ((providers.map (fun p => p.1++[p.2]) ++ requests.map (fun r => r.1++[r.2])).map Msg.toFp) := by
    have ht := hn true
    have hf := hn false
    simp only [Bool.false_eq_true,reduceIte] at ht hf
    rw [ht,hf]
    exact (List.perm_append_comm).trans (hb.trans List.perm_append_comm)
  intro w hw ha
  have hm : (requestKey tr tt w.1,cv tr tt w.1 Candidates.ValueTable.users)∈requests := by
    apply List.mem_map.mpr
    exact ⟨w,List.mem_filter.mpr ⟨hw,by simp [ha]⟩,rfl⟩
  obtain ⟨p,hp',he⟩ := counter_provider_exists providers requests hp hr hbound hperm _ hm
  change p∈v.segs.map (fun p => (providerKey tr tt p.1 pub,cv tr tt p.1 Candidates.ValueTable.users)) at hp'
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp'
  exact ⟨z,hz,he⟩

end ZkFormal.NearV3.Qv.Extract
