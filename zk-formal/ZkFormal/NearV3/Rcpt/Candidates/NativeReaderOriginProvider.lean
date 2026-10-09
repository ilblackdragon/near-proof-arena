import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderOrigin
import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderSourceRoom
import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderWindowKey
import ZkFormal.NearV3.Rcpt.Candidates.NodeWindowDistinct

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

theorem NativeReaderOrigin.room {root : OccurrenceAddress} {run : TreeRun} {value : Bytes}
    {I : UpsInst} (origin : NativeReaderOrigin root run value I)
    (hr : traceUpsert root.tree [0,15] value=some run) (hw : root.tree.wf=true)
    (k : Nat) (hk : k<nQ I) : (part I k).phk+9≤(part I k).pb.length := by
  obtain ⟨B,base,Qs,he,rfl⟩:=origin
  rw [nativeInstance_nQ] at hk
  exact native_reader_source_room _ B hr hw _ he k hk

/-- A byte selected from the SAME encoded native instance belongs to the
original initialized, post-updated provider forest. -/
theorem NativeReaderOrigin.provider (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (hbudget : preBytes (rs.map ReplayTree.post)≤2000000)
    {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 (rs.map ReplayTree.post) tau=some root)
    {value : Bytes} {run : TreeRun} (hr : traceUpsert root.tree [0,15] value=some run)
    {I : UpsInst} (origin : NativeReaderOrigin root run value I)
    (k pos : Nat) (hk : k<nQ I) (hkind : (part I k).kind≠8)
    (hpos : pos<(part I k).pb.length) :
    readerSourceKey (part I k) pos∈nodeWindowKeys
      (records (forestOldInputs rs) (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))) := by
  obtain ⟨B,base,Qs,he,rfl⟩:=origin
  rw [nativeInstance_nQ] at hk
  obtain ⟨s,hs,hlen,hkey⟩:=native_reader_window_key rs hv hw hbudget hroot hr B _ he k hk hkind
  rw [hkey]
  exact nodeWindowKeys_mem hs (by omega)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
