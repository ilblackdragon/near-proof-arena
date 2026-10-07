import ZkFormal.NearV3.Assembly.QueueCapacity
import ZkFormal.NearV3.Assembly.QueuePhysicalBalance
import ZkFormal.NearV3.Qv.Candidates.CombinedPrepared

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Qv.Candidates Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

/-- Accepted native input constructs a fitting, locally valid queue trace with
complete canonical traffic and physical QVC balance using per-use ranks.
Other bus balance and arbitrary accepted-trace soundness remain separate. -/
theorem checkD0a_queue_render {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (p : Prep) (overhead : Nat) (hroots : Public.RootsSized p)
    (hK : p.hdr.K<256^4) (hcount : steps.length=p.hdr.K) :
    ∃ v : MainValues, v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      let pres := steps.map ImplicitStepV3.pre
      let inputs := queueInputs m.pre v pres
      let records := queueRecords (queueForestProviders 0 0 inputs)
      let ws := plan m.pre v pres (queueForestRankResolve inputs 0)
      let pub := ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)
      TableLocal CombinedTable.table (mixedTrace ws records 22) 0 pub ∧
      TableTraffic CombinedTable.interactions (mixedTrace ws records 22) 0 pub (mixedTraffic ws records) ∧
      ((List.range (2^22)).flatMap (fun r =>
        rowTraffic CombinedTable.interactions (mixedTrace ws records 22) 0 r pub ValueTable.B_QVC true)).Perm
      ((List.range (2^22)).flatMap (fun r =>
        rowTraffic CombinedTable.interactions (mixedTrace ws records 22) 0 r pub ValueTable.B_QVC false)) := by
  obtain ⟨v,hvalid,hreads,hrecords,hfit⟩ := checkD0a_queue_rows_fit hk hw h hm hv
  have hh : ∀ x ∈ queueInputs m.pre v (steps.map ImplicitStepV3.pre), ∀ r ∈ x.2, r.Holds x.1 := by
    intro x hx r hr
    simp only [queueInputs,List.mem_cons,List.mem_map] at hx
    rcases hx with rfl | ⟨pre,⟨s,hs,rfl⟩,rfl⟩
    · exact mainRequests_hold m.pre v hvalid hreads r hr
    · have he : r=missingRequest s.pre := by simpa using hr
      subst r
      exact hv.missing_requests s hs
  have hfit' : ((plan m.pre v (steps.map ImplicitStepV3.pre)
      (queueForestRankResolve (queueInputs m.pre v (steps.map ImplicitStepV3.pre)) 0)).flatMap Walk.rows).length +
      ValueGen.recordsSize (queueRecords (queueForestProviders 0 0
        (queueInputs m.pre v (steps.map ImplicitStepV3.pre)))) ≤ 2^22 := by
    simpa only [plan_rows_length] using hfit
  obtain ⟨hl,ht⟩ := plan_prepared_local_and_traffic m.pre v (steps.map ImplicitStepV3.pre)
    (queueForestRankResolve (queueInputs m.pre v (steps.map ImplicitStepV3.pre)) 0)
    hvalid (mainWalk v steps.length (fun _ _ => (0,0)) .delayed 0 v.delayed)
    _ hrecords 22 p overhead (by decide) hfit' hroots hK (by simpa only [List.length_map] using hcount)
  exact ⟨v,hvalid,hreads,hl,ht,plan_physical_qvc_balance _ hh 22 _ hrecords hfit'⟩

end ZkFormal.NearV3.Assembly
