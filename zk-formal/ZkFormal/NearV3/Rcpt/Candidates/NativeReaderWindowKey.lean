import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayProviderWf
import ZkFormal.NearV3.Rcpt.Candidates.NodeUsage
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- Complete six-field UPB source key before adding its use counter. -/
def readerSourceKey (Q : UpsPartI) (pos : Nat) : ZkFormal.Near.Msg :=
  [msgId K_NPOST Q.sN,pos,Q.pb.getD pos 0,Q.pb.length,Q.pdep,Q.pcid.getD pos 0]

theorem native_reader_window_key (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (hbudget : preBytes (rs.map ReplayTree.post)≤2000000)
    {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 (rs.map ReplayTree.post) tau=some root)
    {value : Bytes} {run : TreeRun} (hr : traceUpsert root.tree [0,15] value=some run)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      root.tree run (nativeCidBase
        (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run base)=some Qs)
    (k : Nat) (hk : k<Qs.length)
    (hkind : (part (nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs) k).kind≠8) :
    let I:=nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
      baseI root.tree run value Qs
    ∃s,(records (forestOldInputs rs) (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))))[(part I k).sN]?=some s ∧
      (part I k).pb.length=(s.v.ser false).length ∧
      ∀pos,readerSourceKey (part I k) pos=windowKey (part I k).sN pos s := by
  obtain ⟨s,hs,hbytes,hdepth,hcid⟩:=native_reader_window rs hv hw hbudget hroot hr baseI base he k hk hkind
  have hspan:=replay_provider_span rs hv hw hbudget (forestOldInputs rs) hs
  refine ⟨s,hs,?_,?_⟩
  · rw [hbytes,hspan]
  · intro pos
    simp only [readerSourceKey,windowKey,hbytes,hdepth,hcid pos,hspan]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
