import ZkFormal.NearV3.Rcpt.Candidates.PreparedByteLength
import ZkFormal.NearV3.Rcpt.Candidates.PreparedSchedulerCounts
import ZkFormal.NearV3.Rcpt.Candidates.NativePreparedBody
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountAcceptedOverhead

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly Assembly.RoutingBoundedLayout

/-- The actual native hint and semantics-preserving bounded layout fit u32
public offsets. Arbitrary unrelated hints and expanded boundary arrays are not assumed small. -/
theorem accepted_prepared_length {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {p : Prep}
    (hp : prepD0 cb (nativeHint k w m)=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w) (overhead : Nat) :
    (Public.preparedBytes (boundedPrep p k.L k.H.shardId) overhead).length≤2^26 := by
  have hc : checkD0 cb wb=.ok () := by
    have hc:=((relD0a_iff B0 cb wb).mpr h).1
    unfold RelD0 acceptsD0 at hc
    split at hc <;> simp_all
  have hb:=accepted_native_body_bound hp hk hw h hm
  have hs:=SizeCount.accepted_fixed_overhead hp hk hw hc
  unfold SizeCount.fixedOverhead at hs
  obtain ⟨hpub,hpar,hd,he⟩:=prepared_scheduler_counts hp
  have hbd:=(native_capacity hp hk).1
  have hlen:=prepared_byte_length (boundedPrep p k.L k.H.shardId) overhead
    (prepD0_roots (p:=p) hp) (prepD0_source_roots (p:=p) hp)
  simp only [boundedPrep,Public.schedulerRecords] at hlen hbd
  simp only [Public.schedulerRecords] at hpub hpar hd he
  simp only [boundedPrep]
  rw [hlen]
  omega

theorem accepted_prepared_u32 {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {p : Prep}
    (hp : prepD0 cb (nativeHint k w m)=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w) (overhead : Nat) :
    (Public.preparedBytes (boundedPrep p k.L k.H.shardId) overhead).length<256^4 := by
  have hh:=accepted_prepared_length hp hk hw h hm overhead
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
