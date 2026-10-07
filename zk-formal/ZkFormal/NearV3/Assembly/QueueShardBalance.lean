import ZkFormal.NearV3.Assembly.QueueBufferedProvider
import ZkFormal.NearV3.Qv.Candidates.CombinedTraffic

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Qv.Candidates Qv.Candidates.ValueGen

private theorem sole_provider_flatMap {α β γ : Type} (xs : List α) (key : α → β)
    (hn : (xs.map key).Nodup) (p : α) (hp : p ∈ xs) (f : α → List γ)
    (hz : ∀ q ∈ xs, q≠p → f q=[]) : xs.flatMap f=f p := by
  classical
  induction xs with
  | nil => simp at hp
  | cons q xs ih =>
    simp only [List.map_cons,List.nodup_cons] at hn
    simp only [List.mem_cons] at hp
    rw [List.flatMap_cons]
    rcases hp with rfl | hp
    · have ht : xs.flatMap f=[] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro r hr
        apply hz r (by simp [hr])
        intro he
        subst r
        exact hn.1 (List.mem_map.mpr ⟨p,hr,rfl⟩)
      rw [ht,List.append_nil]
    · have hqp : q≠p := by
        intro he
        subst q
        exact hn.1 (List.mem_map.mpr ⟨p,hp,rfl⟩)
      rw [hz q (by simp) hqp,List.nil_append]
      exact ih hn.2 hp (fun r hr => hz r (by simp [hr]))

/-- Only the unique native buffered provider contributes QSH messages. -/
theorem queueRecords_shard_messages {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1) :
    let vs := queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))
    vs.flatMap Record.shardBytes=queueShardBytes 0 v.shards ∧
      vs.flatMap Record.shardCount=(if v.buffered.isSome then [[0,0,8,v.shards.length]] else []) := by
  dsimp only
  let ps := queueForestProviders 0 0 (queueInputs pre v pres)
  have hmain := hh (pre,mainRequests pre v) (by simp [queueInputs])
  have ha := queueForestProviders_accepts (queueInputs pre v pres) 0 0 hh
  simp only [queueRecords,List.flatMap_map]
  cases hb : v.buffered with
  | none =>
    have hs := (hmain ⟨keyBufferedIdx,v.buffered,.buffered v.shards⟩ (by simp [mainRequests])).2
    change BufferedValue v.buffered v.shards at hs
    rw [hb] at hs
    change v.shards=[] at hs
    have hz : ∀ p ∈ ps, (queueRecord p).shardBytes=[] ∧ (queueRecord p).shardCount=[] := by
      intro p hp
      exact queueRecord_other_shards p (queueBuffered_absent pres hmain hb hp)
    constructor
    · rw [hs]; exact List.flatMap_eq_nil_iff.mpr (fun p hp => (hz p hp).1)
    · simp only [hb,Option.isSome_none,Bool.false_eq_true,ite_false]
      exact List.flatMap_eq_nil_iff.mpr (fun p hp => (hz p hp).2)
  | some b =>
    obtain ⟨p,hp,hm,hbytes⟩ := queueBuffered_exists pres hmain hb
    have ht := (queueBuffered_provider pres hp hm).1
    have hmessages := queueRecord_buffered_shards p hm (ha p hp)
    have hz : ∀ q ∈ ps, q≠p → (queueRecord q).shardBytes=[] ∧ (queueRecord q).shardCount=[] := by
      intro q hq hne
      apply queueRecord_other_shards
      intro ss hss
      exact hne (queueBuffered_unique pres hq hp hss hm)
    have hs := sole_provider_flatMap ps QueueProvider.vid (queueForestProviders_ids_nodup _ 0 0) p hp
      (fun q => (queueRecord q).shardBytes) (fun q hq hn => (hz q hq hn).1)
    have hc := sole_provider_flatMap ps QueueProvider.vid (queueForestProviders_ids_nodup _ 0 0) p hp
      (fun q => (queueRecord q).shardCount) (fun q hq hn => (hz q hq hn).2)
    constructor
    · exact hs.trans (by simpa [ht] using hmessages.1)
    · exact hc.trans (by simpa [ht,hb] using hmessages.2)

open CombinedWalkGen ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

theorem plan_qsh_balance {pre : PTrie} {v : MainValues} (pres : List PTrie) (resolve : Resolve)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1) :
    let vs := queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))
    (vs.flatMap Record.shardBytes ++ vs.flatMap Record.shardCount).Perm
      ((plan pre v pres resolve).flatMap Walk.shardWordMessages) := by
  dsimp only
  obtain ⟨hb,hc⟩ := queueRecords_shard_messages pres hh
  rw [hb,hc,plan_shard_messages]
  exact List.perm_append_comm

theorem plan_physical_qsh_balance {pre : PTrie} {v : MainValues} (pres : List PTrie) (resolve : Resolve)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1)
    (log : Nat) (pub : List Fp)
    (hv : ∀ r ∈ queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)), r.Valid)
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length+
      recordsSize (queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)))≤2^log) :
    let ws := plan pre v pres resolve
    let vs := queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))
    ((List.range (2^log)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub B_QSH true)).Perm
    ((List.range (2^log)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub B_QSH false)) := by
  dsimp only
  have hs := mixedTrace_all_messages _ _ hv (plan_group_slot pre v pres resolve) log pub B_QSH true hfit
  have hr := mixedTrace_all_messages _ _ hv (plan_group_slot pre v pres resolve) log pub B_QSH false hfit
  simp only [mixedTraffic,Walk.wordMessages,canonicalTraffic,
    show B_QSH≠ValueTable.B_QVC by decide,show B_QSH≠B_KEYNIB by decide,
    show B_QSH≠B_FINAL by decide,show B_QSH≠B_VBYTES by decide,
    ite_true,ite_false,Bool.false_eq_true,List.flatMap_nil,List.nil_append,List.append_nil] at hs hr
  have hz : (plan pre v pres resolve).flatMap (fun _ => ([] : List Msg))=[] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  rw [hz,List.nil_append] at hs
  exact hs.trans (((plan_qsh_balance pres resolve hh).map Msg.toFp).trans hr.symm)

end ZkFormal.NearV3.Assembly
