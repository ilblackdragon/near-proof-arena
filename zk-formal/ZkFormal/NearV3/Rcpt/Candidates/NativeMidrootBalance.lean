import ZkFormal.NearV3.Rcpt.Candidates.NativeMidrootRecords
import ZkFormal.NearV3.Rcpt.Candidates.CompactMidrootRanks

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows Assembly

theorem native_midroot_balance (rs : List ReplayTree) (us : List SchedulerUpsertWitness)
    (insts : List UpsInst) (hv : ∀r∈rs,r.Valid)
    (hpre : us.map SchedulerUpsertWitness.pre=rs.map ReplayTree.post)
    (hcount : insts.length=us.length) (hw : ∀u∈us,u.pre.wf=true)
    (hi : ∀(tau : Nat)(u : SchedulerUpsertWitness)(I : UpsInst),us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧
      ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
        NativeReaderOrigin root u.run u.value I)
    (p : List WStep3) (keys : List ZkFormal.Near.Msg)
    (hR : compactR (physicalPrefixUps p insts)≤2^22)
    (trh : Trace Fp) (th tu : Nat) (pub : List Fp)
    (hhead : TableTraffic HeadV3.interactions trh th pub
      (headTraffic (assignHeadUses keys (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post)))))))
    (hlocal : TableLocal compactTable (Candidates.CompactHeight.trace (physicalPrefixUps p insts)) tu pub)
    (rank : Nat→Nat) (msg : List Fp) :
    let tru:=patchWindowCounters (Candidates.CompactHeight.trace (physicalPrefixUps p insts)) tu rank
    tableBusCount HeadV3.interactions trh th pub B_MIDROOT true msg+
      tableBusCount compactTable.interactions tru tu pub B_MIDROOT true msg=
    tableBusCount HeadV3.interactions trh th pub B_MIDROOT false msg+
      tableBusCount compactTable.interactions tru tu pub B_MIDROOT false msg := by
  have hl : ∀I∈insts,I.mid.length=32 := by
    intro I hI
    obtain ⟨i,hib,he⟩:=List.mem_iff_getElem.mp hI
    have hui : i<us.length:=by omega
    have ha:=(hi i us[i] I (by simp [hui]) (by simp [hib,he])).1
    rw [ha.2.1,List.length_map]
    exact ZkFormal.Near.Prune.hashOf_length _ (hw _ (List.getElem_mem hui))
  have hrecords:=native_midroot_records rs us insts hv hpre hcount hi
  have hsend : headSends (assignHeadUses keys (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post))))) B_MIDROOT=
      insts.map (fun I=>[I.tau,I.rid]++I.mid) := by
    simpa only [headSends,ite_true,assignHeadUses,List.map_map,Function.comp_def] using hrecords
  have hrecv : headRecvs (assignHeadUses keys (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post))))) B_MIDROOT=[] := by
    simp [headRecvs,B_MIDROOT,B_DIGEST,B_ROOT,B_EDGE]
  dsimp only
  rw [(hhead B_MIDROOT msg).1,(hhead B_MIDROOT msg).2,
    compact_physical_midroot_send,
    compact_patched_midroot_recv p insts hl hR tu pub hlocal rank msg]
  simp only [headTraffic,hsend,hrecv,List.map_nil,List.count_nil,Nat.zero_add,Nat.add_zero]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
