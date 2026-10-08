import ZkFormal.NearV3.Qv.Extract.BalancedWalkKey

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

/-- The KEYNIB repair preserves the complete actual FINAL receive stream. -/
theorem repaired_final_physical {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt) :
    (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_FINAL false)=
      q.segs.map (fun p => finalMessage tr tt p.1 pub) := by
  simp only [Candidates.KeyTrafficRepair.other_bus tr tt _ pub B_FINAL (by decide) false]
  exact final_physical (Candidates.KeyTrafficRepair.local_to_base h) q

/-- Global FINAL balance supplies a walk with the exact requested terminal
metadata, rather than only a walk bearing a matching key ID. -/
theorem balanced_final_walk {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt)
    (i : Nat) (hi : i<q.segs.length) (others : List (List Fp)) {ws : List WalkR}
    (hbal : ((walkSends3 ws B_FINAL).map Msg.toFp).Perm
      ((List.range (tr.height tt)).flatMap
        (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_FINAL false) ++ others)) :
    ∃ w∈ws, Msg.toFp [w.w,w.tau,w.fk,w.k]=finalMessage tr tt q.segs[i].1 pub := by
  have hm : finalMessage tr tt q.segs[i].1 pub∈(List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_FINAL false) := by
    rw [repaired_final_physical h q]
    exact List.mem_map.mpr ⟨q.segs[i],List.getElem_mem hi,rfl⟩
  obtain ⟨m,hm,he⟩ := List.mem_map.mp (hbal.mem_iff.mpr (List.mem_append_left others hm))
  simp only [walkSends3,show B_FINAL≠B_EDGE by decide,show B_FINAL≠B_BMAP by decide,
    ite_false,ite_true] at hm
  obtain ⟨w,hw,hm⟩ := List.mem_map.mp hm
  subst m
  exact ⟨w,hw,he⟩

/-- The same actual trie walk has the native queue key and requested terminal
result. Both facts follow from the two complete global bus permutations. -/
theorem balanced_queue_lookup {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt)
    (i : Nat) (hi : i<q.segs.length) (ls : RcptV3Vs) (hn : (flatR ls).length≤W_AK)
    (hK : (kPublic.eval tr tt 0 pub).toNat<64)
    {ws : List WalkR} (hW : WalkWf3 ws) (others : List (List Fp))
    (hkey : ((List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true) ++
      (rcptSends3 pub ls B_KEYNIB).map Msg.toFp).Perm
      ((walkRecvs3 ws B_KEYNIB).map Msg.toFp))
    (hfinal : ((walkSends3 ws B_FINAL).map Msg.toFp).Perm
      ((List.range (tr.height tt)).flatMap
        (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_FINAL false) ++ others)) :
    ∃ w∈ws, w.key3=NearSpec.nibbles (physicalWalkBytes tr tt (q.segs[i]'hi)) ∧
      Msg.toFp [w.w,w.tau,w.fk,w.k]=finalMessage tr tt (q.segs[i]'hi).1 pub := by
  obtain ⟨w,hw,he⟩ := balanced_final_walk h q i hi others hfinal
  have hid : (w.w:Fp)=wid.eval tr tt (q.segs[i]'hi).1 pub :=
    congrArg (fun xs : List Fp => xs.getD 0 0) he
  have hk := balanced_native_walk_key h q i hi ls hn hK hW hw hid hkey
  exact ⟨w,hw,hk.2,he⟩

end ZkFormal.NearV3.Qv.Extract
