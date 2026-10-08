import ZkFormal.NearV3.Qv.Extract.BalancedWalkKey

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

/-- Every actual queue request has a trie-walk consumer, derived from its first
physical nibble send and complete KEYNIB balance. -/
theorem balanced_queue_walk_exists {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt)
    (i : Nat) (hi : i<q.segs.length) (others : List (List Fp)) {ws : List WalkR}
    (hbal : ((List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true) ++
      others).Perm ((walkRecvs3 ws B_KEYNIB).map Msg.toFp)) :
    ∃ w∈ws, (w.w:Fp)=wid.eval tr tt q.segs[i].1 pub := by
  let id := wid.eval tr tt q.segs[i].1 pub
  let bs := physicalWalkBytes tr tt q.segs[i]
  let m : List Fp := [id,0,(((bs.getD 0 0).toNat/16:Nat):Fp),0]
  have hpos : 0<bs.length := by
    simpa only [bs,physicalWalkBytes,List.length_map,List.length_range] using
      (q.valid _ (List.getElem_mem hi)).1
  have hm : m∈repairedKeyTraffic id bs := by
    apply List.mem_flatMap.mpr
    refine ⟨0,List.mem_range.mpr hpos,?_⟩
    simp [m,repairedKeyRow,Lean.Grind.Semiring.natCast_zero]
    exact Or.inl rfl
  have hp : m∈(List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true) := by
    rw [repaired_key_physical h q]
    exact List.mem_flatMap.mpr ⟨q.segs[i],List.getElem_mem hi,hm⟩
  obtain ⟨mr,hr,he⟩ := List.mem_map.mp (hbal.mem_iff.mp (List.mem_append_left others hp))
  simp only [walkRecvs3,show B_KEYNIB≠B_EDGE by decide,show B_KEYNIB≠B_BMAP by decide,
    ite_false,ite_true] at hr
  obtain ⟨w,hw,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨j,_,hr⟩ := List.mem_map.mp hr
  subst mr
  refine ⟨w,hw,?_⟩
  have hid := congrArg (fun xs : List Fp => xs.getD 0 0) he
  exact hid

end ZkFormal.NearV3.Qv.Extract
