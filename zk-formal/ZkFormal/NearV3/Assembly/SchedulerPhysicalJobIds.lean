import ZkFormal.NearV3.Assembly.CompactInstanceJobIds
import ZkFormal.NearV3.Assembly.SchedulerBranchWindows

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Algebra

/-- All DIGEST request IDs in the actual encoded native instance are exactly
its native SHA jobs, with multiplicity. Runtime dispatch and branch nonemptiness
are derived here; payload equality remains a distinct semantic obligation. -/
theorem nativeInstance_physical_job_ids (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] value=some run)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run base=some Qs)
    (hi : InstOk (nativeInstance recordId baseI root run value Qs))
    (hp : NativePartFamily (nativeInstance recordId baseI root run value Qs)) :
    let I:=nativeInstance recordId baseI root run value Qs
    (CompactPhysicalDigests.digestJobIds (CompactPhysicalDigests.digestRowMsgs I (.w 3)++
      (List.range (nQ I)).flatMap (fun k=>(List.range (part I k).q.length).flatMap
        (CompactPhysicalDigests.nodeDigestMsgs I k)))).Perm
      ((upsertShaJobs I.tau value run).map (fun M=>(Fp.ofNat M.id).toNat)) := by
  exact CompactPhysicalDigests.native_instance_job_ids hr
    (nativeInstance_digest_frame recordId baseI hr base he) hi hp
    (fun k hk hkind=>nativeInstance_branch_windows recordId baseI hr base he k hk hkind)

end ZkFormal.NearV3.Assembly
