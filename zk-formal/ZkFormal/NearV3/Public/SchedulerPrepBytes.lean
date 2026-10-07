import ZkFormal.NearV3.Public.SchedulerBytes
import ZkFormal.NearV3.Sched.Pub.Prep

/-! Actual successful preparation supplies every scheduler byte bound; the
UInt8 packing cannot silently truncate a scheduler message. -/
namespace ZkFormal.NearV3.Public
open NearSpec NearSpecV3 Sched

theorem prep_scheduler_bytes {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint = .ok p) :
    (∀ row ∈ (schedulerRecords p).pubb, ByteRow row) ∧
    (∀ row ∈ (schedulerRecords p).par, ByteRow row) ∧
    (∀ row ∈ (schedulerRecords p).dlSend, ByteRow row) ∧
    (∀ row ∈ (schedulerRecords p).dlRecv, ByteRow row) := by
  have hlen := prepD0_len hp
  have hlen' : (p.sched.map instOf).length ≤ 256 := by simp only [List.length_map]; omega
  have hP : ∀ tau, tau < (p.sched.map instOf).length →
      ((p.sched.map instOf).getD tau instD).n ≤ 64 ∧ RawOk ((p.sched.map instOf).getD tau instD) := by
    intro tau htau
    have htau' : tau < p.sched.length := by simpa only [List.length_map] using htau
    rw [← List.getElem_eq_getD (h := htau) instD]
    simp only [List.getElem_map]
    have hm := List.getElem_mem htau'
    exact ⟨(prepD0_sched hp _ hm).n64, prepD0_rawOk hp _ hm⟩
  refine ⟨render_pubb_bytes _ _ hlen', render_par_bytes _ _ hlen' hP, ?_, ?_⟩
  · exact dl_bytes 0 _ (by decide)
  · apply dl_bytes
    simp only [List.length_map]
    omega

end ZkFormal.NearV3.Public
