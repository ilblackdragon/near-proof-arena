import ZkFormal.NearV3.Public.Index
import ZkFormal.NearV3.Public.SchedulerPrepBytes

/-! Exact scheduler bus records from successful native preparation. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpec NearSpecV3 Sched

theorem natRow_roundtrip (row : List Nat) (hb : ByteRow row) :
    (row.map UInt8.ofNat).map UInt8.toNat = row := by
  induction row with
  | nil => rfl
  | cons n row ih =>
    simp only [List.map_cons]
    rw [UInt8.toNat_ofNat',Nat.mod_eq_of_lt (hb n (by simp)),ih (fun x hx => hb x (by simp [hx]))]

theorem nat_record_roundtrip (plan : PubSeg) (rows : List (List Nat))
    (hp : plan.msgPrefix = []) (hidx : plan.indexBase = none)
    (hb : ∀ row ∈ rows, ByteRow row) {j : Nat} (hj : j < rows.length) :
    recordNats plan j ((natPayload rows).getD j []) = rows.getD j [] := by
  rw [natPayload_getD rows hj]
  simp only [recordNats,hp,hidx,List.nil_append]
  apply natRow_roundtrip
  apply hb
  rw [← List.getElem_eq_getD (h := hj) []]
  exact List.getElem_mem hj

theorem nat_records_roundtrip (plan : PubSeg) (rows : List (List Nat))
    (hp : plan.msgPrefix = []) (hidx : plan.indexBase = none)
    (hb : ∀ row ∈ rows, ByteRow row) :
    (List.range (natPayload rows).length).map
      (fun j => recordNats plan j ((natPayload rows).getD j [])) = rows := by
  apply List.ext_getElem (by simp [natPayload])
  intro j hj hj'
  simp only [List.getElem_map,List.getElem_range]
  rw [nat_record_roundtrip plan rows hp hidx hb hj',← List.getElem_eq_getD (h := hj') []]

theorem preparedOn_pubb (p : Prep) :
    preparedOn p B_SPUBB true = preparedRecords p (descriptor (plainPlan B_SPUBB true 7) 202 3) := by
  change preparedRecords p (descriptor (plainPlan B_SPUBB true 7) 202 3) ++ [] = _
  exact List.append_nil _

theorem preparedOn_par (p : Prep) :
    preparedOn p B_SPAR true = preparedRecords p (descriptor (plainPlan B_SPAR true 11) 202 4) := by
  change preparedRecords p (descriptor (plainPlan B_SPAR true 11) 202 4) ++ [] = _
  exact List.append_nil _

theorem preparedOn_dlSend (p : Prep) :
    preparedOn p B_SDL true = preparedRecords p (descriptor (plainPlan B_SDL true 5) 202 5) := by
  change preparedRecords p (descriptor (plainPlan B_SDL true 5) 202 5) ++ [] = _
  exact List.append_nil _

theorem preparedOn_dlRecv (p : Prep) :
    preparedOn p B_SDL false = preparedRecords p (descriptor (plainPlan B_SDL false 5) 202 6) := by
  change preparedRecords p (descriptor (plainPlan B_SDL false 5) 202 6) ++ [] = _
  exact List.append_nil _

theorem prepared_scheduler_records {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint = .ok p) :
    preparedOn p B_SPUBB true = (schedulerRecords p).pubb ∧
    preparedOn p B_SPAR true = (schedulerRecords p).par ∧
    preparedOn p B_SDL true = (schedulerRecords p).dlSend ∧
    preparedOn p B_SDL false = (schedulerRecords p).dlRecv := by
  obtain ⟨hb,hp',hs,hr⟩ := prep_scheduler_bytes hp
  rw [preparedOn_pubb,preparedOn_par,preparedOn_dlSend,preparedOn_dlRecv]
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    unfold preparedRecords
    rw [descriptor_index]
  · exact nat_records_roundtrip _ _ rfl rfl hb
  · exact nat_records_roundtrip _ _ rfl rfl hp'
  · exact nat_records_roundtrip _ _ rfl rfl hs
  · exact nat_records_roundtrip _ _ rfl rfl hr

theorem prepared_scheduler_index (AP : AirP) {cb : Bytes} {hint : Hint} {p : Prep}
    (witnessOverhead : Nat) (hseg : AP.pubSegs = preparedSegments)
    (hp : prepD0 cb hint = .ok p) (hr : RootsSized p)
    (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (preparedBytes p witnessOverhead).length < 256^4) :
    let I := prepared_pubIdx AP p witnessOverhead hseg hr hs hlen
    I.recs B_SPUBB true = (schedulerRecords p).pubb ∧
    I.recs B_SPAR true = (schedulerRecords p).par ∧
    I.recs B_SDL true = (schedulerRecords p).dlSend ∧
    I.recs B_SDL false = (schedulerRecords p).dlRecv := by
  dsimp only
  simp only [prepared_pubIdx_recs]
  exact prepared_scheduler_records hp

end ZkFormal.NearV3.Public
