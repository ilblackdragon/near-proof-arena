import ZkFormal.NearV3.Rcpt.Candidates.NativeHeadRootRecords
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootWidths

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows Assembly

theorem native_root_balance {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (oldPost : PTrie) (writes : List (List Nat×Bytes))
    (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hvalid : ∀u∈us,u.Valid) (hcount : insts.length=us.length)
    (hi : ∀tau u I,us[tau]?=some u→insts[tau]?=some I→AllocatedNativeInstance us tau u I)
    (hout : us.map (fun u=>u.run.output)=m.result.trie::steps.map ImplicitStepV3.post)
    (p : List WStep3) (keys : List ZkFormal.Near.Msg)
    (hR : compactR (physicalPrefixUps p insts)≤2^22)
    (trh : Trace Fp) (th tu : Nat) (pub : List Fp)
    (hhead : TableTraffic HeadV3.interactions trh th pub
      (headTraffic (assignHeadUses keys (forestWalkHeads 0 0
        ((nativeReplayForest m steps oldPost writes).map (fun r=>(r.pre,r.post)))))))
    (hlocal : TableLocal compactTable (Candidates.CompactHeight.trace (physicalPrefixUps p insts)) tu pub)
    (rank : Nat→Nat) (msg : List Fp) :
    let tru:=patchWindowCounters (Candidates.CompactHeight.trace (physicalPrefixUps p insts)) tu rank
    ([Msg.toFp ([0]++k.slotB2.prevStateRoot.map UInt8.toNat)]).count msg+
      tableBusCount HeadV3.interactions trh th pub B_ROOT true msg+
      tableBusCount compactTable.interactions tru tu pub B_ROOT true msg=
      tableBusCount HeadV3.interactions trh th pub B_ROOT false msg+
      tableBusCount compactTable.interactions tru tu pub B_ROOT false msg+
      ([Msg.toFp ([steps.length+1]++k.H.prevStateRoot.map UInt8.toNat)]).count msg := by
  have hrecords:=allocated_root_records us insts hcount hi
  rw [hout] at hrecords
  have hh:=replay_head_root_records m steps oldPost writes
  have hrecv : headRecvs (assignHeadUses keys (forestWalkHeads 0 0
      ((nativeReplayForest m steps oldPost writes).map (fun r=>(r.pre,r.post))))) B_ROOT=
      nativeInputRoots 0 (m.pre::steps.map ImplicitStepV3.pre) := by
    simpa [headRecvs,assignHeadUses,List.map_map,Function.comp_def,B_ROOT,B_DIGEST,ite_false,ite_true] using hh
  have hsend : headSends (assignHeadUses keys (forestWalkHeads 0 0
      ((nativeReplayForest m steps oldPost writes).map (fun r=>(r.pre,r.post))))) B_ROOT=[] := by
    simp [headSends,B_ROOT,B_MIDROOT,B_EDGE,B_PARENT,B_DIGS,B_DIGEST]
  have he:=congrArg (fun xs : List ZkFormal.Near.Msg => (xs.map Msg.toFp).count msg)
    (accepted_root_chain hk hw hc hm hv)
  dsimp only
  rw [(hhead B_ROOT msg).1,(hhead B_ROOT msg).2,
    compact_physical_root_recv,
    compact_patched_root_send p insts (allocated_post_widths us insts hvalid hcount hi) hR tu pub hlocal rank msg]
  simp only [headTraffic,hsend,hrecv,List.map_nil,List.count_nil,Nat.add_zero,hrecords]
  simpa only [List.map_cons,List.map_append,List.map_nil,List.count_append,List.count_cons,
    List.count_nil,Nat.add_zero,Nat.zero_add,Nat.add_comm] using he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
