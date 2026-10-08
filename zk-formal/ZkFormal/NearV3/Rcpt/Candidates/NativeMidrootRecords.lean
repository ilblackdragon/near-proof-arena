import ZkFormal.NearV3.Rcpt.Candidates.ReplayHeadRoot
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedReplayHead

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

/-- Exact ordered MIDROOT messages, with the SAME chosen native instances. -/
theorem native_midroot_records (rs : List ReplayTree) (us : List SchedulerUpsertWitness)
    (insts : List UpsInst) (hv : ∀r∈rs,r.Valid)
    (hpre : us.map SchedulerUpsertWitness.pre=rs.map ReplayTree.post)
    (hcount : insts.length=us.length)
    (hi : ∀(tau : Nat)(u : SchedulerUpsertWitness)(I : UpsInst),us[tau]?=some u→insts[tau]?=some I→
      AllocatedNativeInstance us tau u I ∧
      ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
        NativeReaderOrigin root u.run u.value I) :
    headSends (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post)))) B_MIDROOT=
      insts.map (fun I=>[I.tau,I.rid]++I.mid) := by
  let heads:=forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post)))
  have hlen : heads.length=insts.length := by
    have hh:=congrArg List.length (forest_heads_tau (rs.map (fun r=>(r.pre,r.post))) 0 0)
    have hp:=congrArg List.length hpre
    simp only [List.length_map,List.length_range'] at hh hp
    dsimp only [heads]
    omega
  change heads.map (fun h=>[h.tau,h.rid]++h.post)=_
  apply List.ext_getElem
  · simp only [List.length_map,hlen]
  · intro i hh hI
    have hib : i<insts.length := by simpa only [List.length_map] using hI
    have hub : i<us.length := by omega
    obtain ⟨ha,root,hr,ho⟩:=hi i us[i] insts[i] (by simp [hub]) (by simp [hib])
    have ht:=forestRootAt_tree 0 0 (us.map SchedulerUpsertWitness.pre) i
    rw [hr,List.getElem?_map,show us[i]?=some us[i] from by simp [hub]] at ht
    have htree : root.tree=(us[i]).pre:=Option.some.inj ht
    obtain ⟨hd,hhd,htau,hrid,hpost⟩:=replay_head_root rs 0 0 0 i root hv (hpre ▸ hr)
    have hhdi : heads[i]=hd := (List.getElem?_eq_some_iff.mp hhd).2
    simp only [List.getElem_map,hhdi,htau,Nat.zero_add,hrid,hpost,htree,ha.1,ha.2.1,ho.rid]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
