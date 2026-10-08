import ZkFormal.NearV3.Assembly.SchedulerFreshFieldSlice
import ZkFormal.NearV3.Assembly.CompactDigestSlice

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The physical fresh-value window contains the actual inserted-value SHA
output. Byte and length bindings are ordinary constructor equalities, with no
caller-supplied hash or field-range assumption. -/
theorem native_fresh_physical_digest {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) {p : TreePart} (hp : p∈run.parts)
    (hf : freshDigestKind run.terminal p.kind=true) {I : UpsInst} {k : Nat} {base : UpsPartI}
    (he : encodeTreePart base p=some (part I k))
    (hq : (part I k).q=(nodeEnc p.output).map UInt8.toNat) :
    (CompactPhysicalDigests.digestWindow I k
      (if (part I k).ty=0 then 9+(part I k).qhk else 5) 0 v.length).toFp=
      (digMsg (upsertJobId I.tau 0) v.length ((sha256 v).map UInt8.toNat)).toFp := by
  apply CompactPhysicalDigests.digest_window_slice
  · rw [hq,←List.map_drop,←List.map_take,traceUpsert_fresh_field_slice hr hp hf he]
  · simp [ArenaCore.sha256_length]

end ZkFormal.NearV3.Assembly
