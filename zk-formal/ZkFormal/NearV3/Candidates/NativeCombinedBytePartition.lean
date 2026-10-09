import ZkFormal.NearV3.Candidates.NativeQueueForestPartition

namespace ZkFormal.NearV3.Candidates.NativeCombinedBytePartition
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
open Qv Qv.Candidates Qv.Candidates.CombinedWalkGen ZkFormal.Air ZkFormal.Algebra

/-- The explicit remaining byte obligations after all three physical suppliers.
Original-state ownership excludes account writes, access keys and queue slots;
implicit states exclude exactly their queue-selected occurrences. -/
def remaining (pre : PTrie) (rs : List Receipt) (writes : List (List Nat×Bytes))
    (v : MainValues) (pres : List PTrie) : List Msg :=
  (((NativeQueuePartition.residual pre rs writes).filter
    (fun i=>!(decide (i∈NativeQueuePartition.ids pre v)))).flatMap
      (fun i=>emitAt i 0 (((NearSpecV3.valsOf pre).getD i []).map UInt8.toNat)))++
  NativeQueueForestPartition.forestRemaining (pres.map (fun t=>(t,[missingRequest t])))
    (NearSpecV3.valsOf pre).length

/-- SAME accepted queue allocation, actual account and access-key tables, and
actual EmptyValue demand share one byte equation. Only the displayed residual
remains for additional providers; no overlap is hidden by a count inequality. -/
theorem physical_partition {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
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
    (trA trK : Trace Fp) (tA tK tV : Nat) (pub msg : List Fp)
    (hta : TableTraffic AccountEmpty.table.interactions trA tA pub (acctV3Traffic as))
    (htk : TableTraffic AkeyV3.interactions trK tK pub
      (akeyTraffic (NativeAccessKeyProviders.providers m.pre rs))) :
    let pres := steps.map ImplicitStepV3.pre
    tableBusCount AccountEmpty.table.interactions trA tA pub B_VBYTES true msg+
    tableBusCount AkeyV3.interactions trK tK pub B_VBYTES true msg+
    tableBusCount CombinedTable.interactions
      (mixedTrace (plan m.pre v pres (NativeQueueIds.resolve m.pre v pres))
        (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))) 22)
      0 pub B_VBYTES true msg+
    cnt (remaining m.pre rs writes v pres) msg=
    tableBusCount EmptyValue.table.interactions
      (TrieCountHeight.value (ChainMetadata.assignValues cs
        (seedValuesFrom 0 (forestBytes (m.pre::pres)))) pub) tV pub B_VBYTES false msg := by
  have haccount := NativeValueByteInventory.account_partition hkeys ha
    (steps.map ImplicitStepV3.pre) cs hval trA tA tV pub msg hta
  have hkey := NativeQueuePartition.access_queue_partition (v:=v) hkeys hkeyvalid trK tK pub msg htk
  have hqueue := NativeQueuePhysicalBytes.accepted hk hw hc hm hv v hvalid hreads pub msg
  dsimp only at hqueue
  rw [NativeQueuePhysicalBytes.forest_split] at hqueue
  have himp := NativeQueueForestPartition.forest_partition
    ((steps.map ImplicitStepV3.pre).map (fun t=>(t,[missingRequest t]))) 1
    (NearSpecV3.valsOf m.pre).length msg
  dsimp only
  simp only [remaining,cnt,List.map_append,List.count_append] at ⊢
  change _ + cnt ((NativeAccessBytePartition.remaining m.pre writes).flatMap _) msg + _ = _ at haccount
  simp only [cnt,List.map_map,Function.comp_def] at haccount hkey hqueue himp ⊢
  have hproj : (fun x : ImplicitStepV3=>x.pre)=ImplicitStepV3.pre := rfl
  rw [hproj] at himp
  omega

end ZkFormal.NearV3.Candidates.NativeCombinedBytePartition
