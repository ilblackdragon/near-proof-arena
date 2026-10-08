import ZkFormal.NearV3.Rcpt.Candidates.NativeHeadWf
import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayProviderWf

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render Render.UpsGen Assembly

private theorem root_encoding_bound (ts : List PTrie) (hb : preBytes ts≤2000000)
    (t : PTrie) (ht : t∈ts) : (nodeEnc t).length<Algebra.P := by
  by_cases hn : isNode t=true
  · apply native_forest_node_byte_bound ts hb t
    apply List.mem_flatMap.mpr
    refine ⟨t,ht,?_⟩
    cases t <;> simp_all [occs,isNode]
  · cases t <;> simp_all [isNode,nodeEnc,Algebra.P]

/-- Replay HEADs have accepted native digest widths and canonical scalars;
there is no assumption that receipt replay equals structural UPS output. -/
theorem replay_head_ok (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (hb : preBytes (rs.map ReplayTree.pre)≤2000000)
    (hpos : 0<rs.length) (hlen : rs.length≤32) :
    HeadOk (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post)))) := by
  have hcount:=forest_allocation_counts (rs.map ReplayTree.pre) hb
  have hlength : (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post)))).length=rs.length := by
    have hh:=congrArg List.length (forest_heads_tau (rs.map (fun r=>(r.pre,r.post))) 0 0)
    simpa only [List.length_map,List.length_range'] using hh
  refine ⟨?_,by omega,by omega⟩
  apply forest_head_wf
  · simp only [List.length_map,Nat.zero_add]
    change rs.length<2013265921
    omega
  · simp only [List.map_map,Function.comp_def,Nat.zero_add]
    change ((rs.map ReplayTree.pre).flatMap occs).length<2013265921
    omega
  · intro a b hab
    obtain ⟨r,hr,he⟩:=List.mem_map.mp hab
    have ha : r.pre=a:=congrArg Prod.fst he
    have hb' : r.post=b:=congrArg Prod.snd he
    subst a;subst b
    exact ⟨hw r hr,SizedAccountRun.wf (hv r hr) (hw r hr),root_encoding_bound _ hb r.pre (List.mem_map.mpr ⟨r,hr,rfl⟩)⟩

theorem assigned_replay_head_ok (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (hb : preBytes (rs.map ReplayTree.pre)≤2000000)
    (hpos : 0<rs.length) (hlen : rs.length≤32)
    (keys : List ZkFormal.Near.Msg) (hk : keys.length<Algebra.P) :
    HeadOk (assignHeadUses keys (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post))))) := by
  have hh:=replay_head_ok rs hv hw hb hpos hlen
  exact ⟨assignHeadUses_wf keys _ hh.wf hk,by simpa [assignHeadUses] using hh.pos,
    by simpa [assignHeadUses] using hh.cap⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
