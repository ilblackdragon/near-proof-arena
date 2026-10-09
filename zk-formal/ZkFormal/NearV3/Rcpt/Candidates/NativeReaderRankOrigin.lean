import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderOrigin
import ZkFormal.NearV3.Rcpt.Candidates.UpsPhysicalPrefix

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open Assembly NearSpec ZkFormal.Near Render Render.UpsGen UpsRows

/-- Native part encoding and postpayloads are independent of walk use counters. -/
theorem nativeInstance_walk (recordId : PTrie→Nat) (B : UpsInst) (root : PTrie)
    (run : TreeRun) (value : Bytes) (Qs : List UpsPartI) (ws : List WStep3) :
    nativeInstance recordId {B with walk:=ws} root run value Qs=
      {nativeInstance recordId B root run value Qs with walk:=ws} := by
  rfl

theorem NativeReaderOrigin.walk {root : OccurrenceAddress} {run : TreeRun} {value : Bytes}
    {I : UpsInst} (h : NativeReaderOrigin root run value I) (ws : List WStep3) :
    NativeReaderOrigin root run value {I with walk:=ws} := by
  obtain ⟨B,base,Qs,he,rfl⟩:=h
  exact ⟨{B with walk:=ws},base,Qs,he,(nativeInstance_walk _ B _ _ _ _ ws).symm⟩

theorem NativeReaderOrigin.ranked {root : OccurrenceAddress} {run : TreeRun} {value : Bytes}
    {I : UpsInst} (h : NativeReaderOrigin root run value I) (previous : List WStep3) :
    NativeReaderOrigin root run value (syncUps (rankUps previous I)) := by
  exact h.walk _

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
