import ZkFormal.NearV3.Assembly.QueuePayload
import ZkFormal.NearV3.Qv.Candidates.CombinedCapacity

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv
open Qv.Candidates Qv.Candidates.CombinedWalkGen

/-- Actual accepted-input queue rows fit the existing combined table height.
This does not assert global ownership, local acceptance, or protocol admission. -/
theorem checkD0a_queue_rows_fit {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∃ v : MainValues, v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      let pres := steps.map ImplicitStepV3.pre
      let inputs := queueInputs m.pre v pres
      let records := queueRecords (queueForestProviders 0 0 inputs)
      (∀ r ∈ records, r.Valid) ∧
      ((plan m.pre v pres (queueForestResolve inputs 0)).flatMap Walk.rows).length +
        ValueGen.recordsSize records ≤ 2^22 := by
  obtain ⟨v,hvalid,hreads,hr,hbytes,hcount⟩ := checkD0a_queue_records hk hw h hm hv
  have hb : (v.buffered.map List.length).getD 0 ≤ 3000000 := by
    have hB : B0 ≤ 3000000 := by decide
    cases he : v.buffered with
    | none => simp [he]
    | some b =>
      have hf := hreads.2.1
      rw [he] at hf
      have hh := checkD0a_read_bound hk hw h hm hv
        (by simp : m.pre ∈ m.pre :: steps.map ImplicitStepV3.pre) hf
      simpa only [he,Option.map_some,Option.getD_some] using Nat.le_trans hh hB
  have hc := h
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩ := ReexecV3D0.bind_ok' hc
  cases u
  obtain ⟨_,_,_,_,hcnt,hK⟩ := checkD0_native_steps hk hw hc
  have hlen := hv.length
  simp only [List.length_zip] at hlen
  have hs : (steps.map ImplicitStepV3.pre).length ≤ 31 := by simp only [List.length_map]; omega
  refine ⟨v,hvalid,hreads,hr,?_⟩
  exact combined_rows_fit m.pre v (steps.map ImplicitStepV3.pre) _ hvalid hb hs _ hr hbytes (by omega)

end ZkFormal.NearV3.Assembly
