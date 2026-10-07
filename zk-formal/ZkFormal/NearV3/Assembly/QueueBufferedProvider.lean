import ZkFormal.NearV3.Assembly.QueueShardPayload

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv

theorem mainRequests_buffered {pre : PTrie} {v : MainValues} {r : ReadRequest} {shards : List Nat}
    (hr : r ∈ mainRequests pre v) (hm : r.mode=.buffered shards) :
    r=⟨keyBufferedIdx,v.buffered,.buffered v.shards⟩ ∧ shards=v.shards := by
  simp only [mainRequests,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hr
  rcases hr with (rfl | rfl | rfl) | ⟨s,hs,rfl⟩
  · contradiction
  · simp only [ParseMode.buffered.injEq] at hm
    exact ⟨rfl,hm.symm⟩
  · contradiction
  · contradiction

theorem queueProviders_mode_request {pre : PTrie} {rs : List ReadRequest} {tau base : Nat}
    {p : QueueProvider} (hp : p ∈ queueProviders pre rs tau base) :
    ∃ r ∈ rs, p.mode=r.mode := by
  obtain ⟨⟨b,i⟩,hi,rfl⟩ := List.mem_map.mp hp
  exact ⟨queueRepresentative pre rs i,(queueRepresentative_spec hi).1,rfl⟩

theorem mainProvider_buffered {pre : PTrie} {v : MainValues} {base : Nat}
    {p : QueueProvider} {shards : List Nat}
    (hp : p ∈ queueProviders pre (mainRequests pre v) 0 base) (hm : p.mode=.buffered shards) :
    p.tau=0 ∧ shards=v.shards ∧ pre.find keyBufferedIdx=some (some p.bytes) ∧
      ∃ i, valueIndex pre keyBufferedIdx=some i ∧ p.vid=base+i := by
  obtain ⟨⟨b,i⟩,hi,rfl⟩ := List.mem_map.mp hp
  obtain ⟨hr,hidx⟩ := queueRepresentative_spec hi
  obtain ⟨he,hs⟩ := mainRequests_buffered hr hm
  rw [he] at hidx
  refine ⟨rfl,hs,?_,i,hidx,rfl⟩
  exact valueIndex_bytes hidx (queueSelected_mem.mp hi).1

theorem queueBuffered_provider {pre : PTrie} {v : MainValues} (pres : List PTrie)
    {p : QueueProvider} {shards : List Nat}
    (hp : p ∈ queueForestProviders 0 0 (queueInputs pre v pres)) (hm : p.mode=.buffered shards) :
    p.tau=0 ∧ shards=v.shards ∧ pre.find keyBufferedIdx=some (some p.bytes) ∧
      valueIndex pre keyBufferedIdx=some p.vid := by
  obtain ⟨j,t,rs,offset,hj,ht,hp',hr⟩ := queueForest_provider_location _ 0 0 p hp
  cases j with
  | zero =>
    simp only [queueInputs,List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hj
    obtain ⟨rfl,rfl⟩ := hj
    simp only [queueInputs,queueForestProviders,List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨ht,hs,hf,i,hi,hvid⟩ := mainProvider_buffered hp hm
      exact ⟨ht,hs,hf,by simpa [hvid] using hi⟩
    · have hb := queueForestProviders_bounds _ _ _ hp
      simp only [Nat.add_zero] at ht
      omega
  | succ j =>
    simp only [queueInputs,List.getElem?_cons_succ,List.getElem?_map] at hj
    obtain ⟨u,hu,he⟩ := Option.map_eq_some_iff.mp hj
    cases he
    obtain ⟨r,hr,hm'⟩ := queueProviders_mode_request hp'
    simp only [List.mem_singleton] at hr
    subst r
    rw [hm] at hm'
    contradiction

theorem queueBuffered_exists {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ r ∈ mainRequests pre v, r.Holds pre) {b : Bytes} (hb : v.buffered=some b) :
    ∃ p ∈ queueForestProviders 0 0 (queueInputs pre v pres),
      p.mode=.buffered v.shards ∧ p.bytes=b := by
  let r : ReadRequest := ⟨keyBufferedIdx,v.buffered,.buffered v.shards⟩
  have hr : (mainRequests pre v)[1]?=some r := rfl
  have hf := (hh r (List.mem_of_getElem? hr)).1
  change pre.find keyBufferedIdx=some v.buffered at hf
  rw [hb] at hf
  obtain ⟨p,hp,_,hbytes,_,_,hmode⟩ := queueForestRankResolve_mode (queueInputs pre v pres) 0 0
    (queueInputs_modes pre v pres) (tau := 0) (by rfl) hr hf
  exact ⟨p,hp,hmode,hbytes⟩

theorem queueBuffered_unique {pre : PTrie} {v : MainValues} (pres : List PTrie)
    {p q : QueueProvider} {ss ts : List Nat}
    (hp : p ∈ queueForestProviders 0 0 (queueInputs pre v pres))
    (hq : q ∈ queueForestProviders 0 0 (queueInputs pre v pres))
    (hpm : p.mode=.buffered ss) (hqm : q.mode=.buffered ts) : p=q := by
  have hp' := (queueBuffered_provider pres hp hpm).2.2.2
  have hq' := (queueBuffered_provider pres hq hqm).2.2.2
  have hv := Option.some.inj (hp'.symm.trans hq')
  exact nodup_key_eq _ QueueProvider.vid (queueForestProviders_ids_nodup _ 0 0) hp hq hv

theorem queueBuffered_absent {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ r ∈ mainRequests pre v, r.Holds pre) (hb : v.buffered=none)
    {p : QueueProvider} (hp : p ∈ queueForestProviders 0 0 (queueInputs pre v pres)) :
    ∀ shards, p.mode≠.buffered shards := by
  intro shards hm
  have hf := (queueBuffered_provider pres hp hm).2.2.1
  have hr := (hh ⟨keyBufferedIdx,v.buffered,.buffered v.shards⟩ (by simp [mainRequests])).1
  change pre.find keyBufferedIdx=some v.buffered at hr
  rw [hb,hf] at hr
  simp at hr

end ZkFormal.NearV3.Assembly
