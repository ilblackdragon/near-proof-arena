import ZkFormal.NearV3.Assembly.ShaBinRender

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra

/-- Concrete four-table honest SHA trace for accepted source and scheduler work.
Local constraints and all byte/digest traffic are proved for each physical table;
other hash families and whole-proof bus cancellation remain separate. -/
theorem checkD0a_source_scheduler_sha_render {cb wb raw : Bytes} {codes : List Bytes}
    {k : WalkD0} {w : StateWitness} {hint : Hint} {p : Prep}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w)
    (hc : checkD0a B0 cb wb=.ok ()) (hp : prepD0 cb hint=.ok p)
    (hf : decodeWitnessFile wb=.ok (raw,codes)) (hr : decodeStateWitness raw=.ok w)
    (pub : List Fp) :
    ∃us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀u∈us,u.Valid∧u.pre.wf=true) ∧
      let bins := sourceShaMessageBins (sourceShaMessages p.lists w.entries) ++
        [schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us]
      bins.length=4 ∧
      bins.flatten=sourceShaMessages p.lists w.entries ++
        (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ∧
      ∀t,t<4 →
        Near.TableLocal (Sha.Table.table Near.B_BYTES Near.B_DIGEST) (shaBinTrace bins) t pub ∧
        Near.TableTraffic (Sha.Table.interactions Near.B_BYTES Near.B_DIGEST) (shaBinTrace bins) t pub
          (shaBinTraffic (bins.getD t [])) := by
  obtain ⟨us,hpos,hlen,hvalid,hcount,hrecon,hok⟩ := checkD0a_source_scheduler_sha_ok hk hw hc hp hf hr
  refine ⟨us,hpos,hlen,hvalid,hcount,hrecon,?_⟩
  intro t ht
  have hmem : (sourceShaMessageBins (sourceShaMessages p.lists w.entries) ++
      [schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us]).getD t [] ∈
      sourceShaMessageBins (sourceShaMessages p.lists w.entries) ++
      [schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us] := by
    have hh : t<(sourceShaMessageBins (sourceShaMessages p.lists w.entries) ++
      [schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us]).length := by omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hh,Option.getD_some]
    exact List.getElem_mem hh
  exact ⟨shaBin_local _ t pub (hok _ hmem),shaBin_traffic _ t pub (hok _ hmem)⟩

end ZkFormal.NearV3.Assembly
