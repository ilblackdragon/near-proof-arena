import ZkFormal.NearV3.Candidates.NativeCombinedBytePartition
import ZkFormal.NearV3.Candidates.NativePriorOwnership

namespace ZkFormal.NearV3.Candidates.NativePriorBytePartition
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
open Qv Qv.Candidates Qv.Candidates.CombinedWalkGen ZkFormal.Air ZkFormal.Algebra

/-- Explicit remainder after the main prior parser additionally supplies its
original native value occurrence. Implicit-state providers are still separate. -/
def remaining (pre : PTrie) (rs : List Receipt) (writes : List (List Nat×Bytes))
    (v : MainValues) (pres : List PTrie) (i : Nat) : List Msg :=
  ((NativePriorOwnership.remainingIds pre rs writes v).erase i).flatMap
    (fun j=>emitAt j 0 (((NearSpecV3.valsOf pre).getD j []).map UInt8.toNat))++
  NativeQueueForestPartition.forestRemaining (pres.map (fun t=>(t,[missingRequest t])))
    (NearSpecV3.valsOf pre).length

set_option maxRecDepth 4096

/-- The same accepted global byte equation now includes the actual prior parser.
Its occurrence and capacity are derived; only original native read/decode facts
identify the prior value, and all earlier suppliers retain their exact traces. -/
theorem present {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid : v.Valid) (hreads : v.Reads m.pre m.pre m.pre)
    {post : PTrie} {rs : List Receipt} {as : List AcctV} {writes : List (List Nat×Bytes)}
    (hkeys : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (ha : nativeAccountViews m.pre post rs=some as)
    (hkeyvalid : ∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
      ∀bytes,m.pre.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)→
        bytes.length=9 ∧ bytes.getD 8 0=1)
    (cs : List StoreDuplicateChain.Entry)
    (hval : Render.ValOk (ChainMetadata.assignValues cs
      (seedValuesFrom 0 (forestBytes (m.pre::steps.map ImplicitStepV3.pre)))))
    {bs : Bytes} {old : Bandwidth.State}
    (hr:readKey m.pre keyBwState "bandwidth scheduler state"=.ok (some bs))
    (hd:Bandwidth.State.decode bs=some old)
    (tP : Nat)
    (trA trK : Trace Fp) (tA tK tV : Nat) (pub : List Fp)
    (hta : TableTraffic AccountEmpty.table.interactions trA tA pub (acctV3Traffic as))
    (htk : TableTraffic AkeyV3.interactions trK tK pub
      (akeyTraffic (NativeAccessKeyProviders.providers m.pre rs))) :
    ∃i,valueIndex m.pre keyBwState=some i ∧ (NearSpecV3.valsOf m.pre)[i]?=some bs ∧
    ∀msg : List Fp,
    let pres := steps.map ImplicitStepV3.pre
    tableBusCount AccountEmpty.table.interactions trA tA pub B_VBYTES true msg+
    tableBusCount AkeyV3.interactions trK tK pub B_VBYTES true msg+
    tableBusCount CombinedTable.interactions
      (mixedTrace (plan m.pre v pres (NativeQueueIds.resolve m.pre v pres))
        (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))) 22)
      0 pub B_VBYTES true msg+
    tableBusCount (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      (ProcPriorRawGen.trace old i true) tP pub B_VBYTES true msg+
    cnt (remaining m.pre rs writes v pres i) msg=
    tableBusCount EmptyValue.table.interactions
      (TrieCountHeight.value (ChainMetadata.assignValues cs
        (seedValuesFrom 0 (forestBytes (m.pre::pres)))) pub) tV pub B_VBYTES false msg := by
  obtain ⟨i,hi,hb,htraffic⟩:=NativePriorRawBytes.accepted_present hk hw hc hm hv
    (List.mem_cons_self ..) hr hd 0 tP pub
  refine ⟨i,hi,hb,?_⟩
  intro msg
  have hbase:=NativeCombinedBytePartition.physical_partition hk hw hc hm hv
    v hvalid hreads hkeys ha hkeyvalid cs hval trA trK tA tK tV pub msg hta htk
  have hf:m.pre.find keyBwState=some (some bs):=by
    cases he:m.pre.find keyBwState <;> simp [readKey,he] at hr
    simpa [hr] using he
  have hbound:=checkD0a_read_bound hk hw hc hm hv (List.mem_cons_self ..) hf
  have hp:=NativePriorOwnership.present_partition hi hkeys v hb hd
    (by unfold B0 at hbound; omega) tP pub msg
  dsimp only at hbase ⊢
  simp only [NativeCombinedBytePartition.remaining,remaining,cnt,List.map_append,List.count_append] at hbase ⊢
  unfold NativePriorOwnership.remainingIds at hp ⊢
  simp only [cnt] at hp hbase ⊢
  omega

/-- Missing prior values add a silent physical parser and preserve the residual. -/
theorem absent {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid : v.Valid) (hreads : v.Reads m.pre m.pre m.pre)
    {post : PTrie} {rs : List Receipt} {as : List AcctV} {writes : List (List Nat×Bytes)}
    (hkeys : writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId))
    (ha : nativeAccountViews m.pre post rs=some as)
    (hkeyvalid : ∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
      ∀bytes,m.pre.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)→
        bytes.length=9 ∧ bytes.getD 8 0=1)
    (cs : List StoreDuplicateChain.Entry)
    (hval : Render.ValOk (ChainMetadata.assignValues cs
      (seedValuesFrom 0 (forestBytes (m.pre::steps.map ImplicitStepV3.pre)))))
    (hr:readKey m.pre keyBwState "bandwidth scheduler state"=.ok none)
    (tP : Nat)
    (trA trK : Trace Fp) (tA tK tV : Nat) (pub : List Fp)
    (hta : TableTraffic AccountEmpty.table.interactions trA tA pub (acctV3Traffic as))
    (htk : TableTraffic AkeyV3.interactions trK tK pub
      (akeyTraffic (NativeAccessKeyProviders.providers m.pre rs))) :
    ∀msg : List Fp,
    let pres := steps.map ImplicitStepV3.pre
    tableBusCount AccountEmpty.table.interactions trA tA pub B_VBYTES true msg+
    tableBusCount AkeyV3.interactions trK tK pub B_VBYTES true msg+
    tableBusCount CombinedTable.interactions
      (mixedTrace (plan m.pre v pres (NativeQueueIds.resolve m.pre v pres))
        (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))) 22)
      0 pub B_VBYTES true msg+
    tableBusCount (ProcPriorRawFrame.interactions Sched.B_SPOST 73 B_VBYTES 74 75)
      (ProcPriorRawGen.trace Bandwidth.State.initial 0 false) tP pub B_VBYTES true msg+
    cnt (NativeCombinedBytePartition.remaining m.pre rs writes v pres) msg=
    tableBusCount EmptyValue.table.interactions
      (TrieCountHeight.value (ChainMetadata.assignValues cs
        (seedValuesFrom 0 (forestBytes (m.pre::pres)))) pub) tV pub B_VBYTES false msg := by
  intro msg
  have hzero:=(NativePriorRawBytes.absent hr 0 tP pub msg).2
  have hbase:=NativeCombinedBytePartition.physical_partition hk hw hc hm hv
    v hvalid hreads hkeys ha hkeyvalid cs hval trA trK tA tK tV pub msg hta htk
  dsimp only at hbase ⊢
  rw [hzero,Nat.add_zero]
  exact hbase

end ZkFormal.NearV3.Candidates.NativePriorBytePartition
