import ZkFormal.NearV3.Assembly.SchedulerSizedWitness
import ZkFormal.NearV3.Assembly.ShaRowCost

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen ZkFormal.Sha.Gen

/-- Actual scheduler value plus native node jobs, in transition order. Other
SHA kinds must be composed separately with their own shared-table charges. -/
def schedulerShaJobs (tau : Nat) : List SchedulerUpsertWitness → List Msg
  | [] => []
  | u::us => upsertShaJobs tau u.value u.run ++ schedulerShaJobs (tau+1) us

theorem schedulerShaJobs_bytes (tau : Nat) (us : List SchedulerUpsertWitness) :
    ∀ M∈schedulerShaJobs tau us, ∀ b∈M.bytes,b<256 := by
  induction us generalizing tau with
  | nil => simp [schedulerShaJobs]
  | cons u us ih =>
    intro M hm
    rcases List.mem_append.mp hm with hm|hm
    exact (upsertShaJobs_bytes hm).2
    exact ih (tau+1) M hm

theorem schedulerShaJobs_byte_count (tau : Nat) (us : List SchedulerUpsertWitness) :
    ((schedulerShaJobs tau us).map (fun M => M.bytes.length)).sum=
      (us.map (fun u => u.value.length)).sum+(us.map (fun u => outputByteCharge u.run)).sum := by
  induction us generalizing tau with
  | nil => rfl
  | cons u us ih =>
    simp only [schedulerShaJobs,List.map_append,List.sum_append,upsertShaJobs_byte_count,
      List.map_cons,List.sum_cons,ih]
    unfold outputByteCharge
    omega

theorem schedulerShaJobs_count (tau : Nat) (us : List SchedulerUpsertWitness)
    (hp : ∀ u∈us,u.run.parts.length≤403) :
    (schedulerShaJobs tau us).length≤404*us.length := by
  induction us generalizing tau with
  | nil => simp [schedulerShaJobs]
  | cons u us ih =>
    have hh := hp u (by simp)
    have ht := ih (tau+1) (fun x hx => hp x (by simp [hx]))
    simp only [schedulerShaJobs,List.length_append,upsertShaJobs_length,List.length_cons]
    omega

theorem sha_message_length_le_total (msgs : List Msg) (M : Msg) (hm : M∈msgs) :
    M.bytes.length≤(msgs.map (fun m => m.bytes.length)).sum := by
  induction msgs with
  | nil => simp at hm
  | cons x xs ih =>
    rcases List.mem_cons.mp hm with rfl|hm
    · simp
    · have h := ih hm; simp only [List.map_cons,List.sum_cons]; omega

private theorem upsert_row_arithmetic (rows bytes count : Nat)
    (hr : 64*rows≤17*bytes+1288*count) (hb : bytes≤5277984) (hc : count≤12928) :
    rows≤1662140 := by omega

/-- Every accepted native transition has a concrete upsert-only SHA batch with
fully derived capacity. This does not assert shared capacity for other kinds. -/
theorem checkD0a_upsert_sha_capacity {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ()) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀ u∈us,u.Valid ∧ u.pre.wf=true) ∧
      let jobs := schedulerShaJobs 0 us
      jobs.length≤12928 ∧ (jobs.map (fun M => M.bytes.length)).sum≤5277984 ∧
      (honestRows jobs).length≤1662140 ∧ honestLog jobs≤21 ∧ ZkFormal.Sha.MsgsOk jobs := by
  obtain ⟨us,hpos,hlen,hvalid,hnodes,hvalues⟩ := checkD0a_upsert_byte_budget hk hw h
  have hc := schedulerShaJobs_count 0 us (fun u hu => (hvalid u hu).2.2)
  have hcount : (schedulerShaJobs 0 us).length≤12928 := by omega
  have hb : ((schedulerShaJobs 0 us).map (fun M => M.bytes.length)).sum≤5277984 := by
    rw [schedulerShaJobs_byte_count]; omega
  have hr := upsert_row_arithmetic _ _ _ (sha_rows_cost (schedulerShaJobs 0 us)) hb hcount
  have hlog := ZkFormal.Sha.Complete.clog2_le
    (honestRows (schedulerShaJobs 0 us)).length 21 (by omega)
  have hok : ZkFormal.Sha.MsgsOk (schedulerShaJobs 0 us) := by
    refine ⟨schedulerShaJobs_bytes 0 us,?_,by simp only [ZkFormal.Sha.Table.maxLog]; omega⟩
    intro M hm
    have hi := sha_message_length_le_total _ M hm
    omega
  exact ⟨us,hpos,hlen,fun u hu => ⟨(hvalid u hu).1,(hvalid u hu).2.1⟩,
    hcount,hb,hr,by unfold honestLog; omega,hok⟩

end ZkFormal.NearV3.Assembly
