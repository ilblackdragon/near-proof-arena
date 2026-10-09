import ZkFormal.NearV3.Qv.Extract.KeyProviderIds
import ZkFormal.NearV3.Qv.Extract.NativeWalkKey

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

/-- Actual queue and receipt KEYNIB balance fixes each queue walk's complete
native key. This consumes global traffic equality, rather than assuming each
request already belongs to its desired provider. -/
theorem balanced_native_walk_key {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt)
    (i : Nat) (hi : i<q.segs.length) (ls : RcptV3Vs) (hn : (flatR ls).length≤W_AK)
    (hK : (kPublic.eval tr tt 0 pub).toNat<64)
    {ws : List WalkR} (hW : WalkWf3 ws) {w : WalkR} (hw : w∈ws)
    (hid : (w.w:Fp)=wid.eval tr tt (q.segs[i]'hi).1 pub)
    (hbal : ((List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true) ++
      (rcptSends3 pub ls B_KEYNIB).map Msg.toFp).Perm
      ((walkRecvs3 ws B_KEYNIB).map Msg.toFp)) :
    w.steps.length=2*(physicalWalkBytes tr tt (q.segs[i]'hi)).length+2 ∧
      w.key3=NearSpec.nibbles (physicalWalkBytes tr tt (q.segs[i]'hi)) := by
  have hL := Candidates.KeyTrafficRepair.local_to_base h
  have hp := seg_le_end q.segs 0 q.consecutive _ (List.getElem_mem hi)
  have hb : 2*(physicalWalkBytes tr tt (q.segs[i]'hi)).length<P := by
    simp only [physicalWalkBytes,List.length_map,List.length_range]
    have := q.fits
    have := height_le hL
    unfold P
    omega
  apply native_walk_key hW hw (wid.eval tr tt (q.segs[i]'hi).1 pub) _ hb
  intro j h1 h2
  let m : Msg := [w.w,j-1,(w.step j).sym,if j+1=w.steps.length then 1 else 0]
  have hm : m∈walkRecvs3 ws B_KEYNIB := by
    unfold walkRecvs3
    rw [if_neg (by decide),if_neg (by decide),if_pos rfl,List.mem_flatMap]
    refine ⟨w,hw,List.mem_map.mpr ⟨j-1,List.mem_range.mpr (by omega),?_⟩⟩
    simp only [m,show j-1+1=j by omega,show j-1+2=j+1 by omega]
  have hsend := hbal.mem_iff.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  have hmId : (Msg.toFp m).getD 0 0=wid.eval tr tt (q.segs[i]'hi).1 pub := by
    exact hid
  have hown : Msg.toFp m∈repairedKeyTraffic (wid.eval tr tt (q.segs[i]'hi).1 pub)
      (physicalWalkBytes tr tt (q.segs[i]'hi)) := by
    rcases List.mem_append.mp hsend with hsend|hsend
    · exact physical_key_ownership h q i hi hK hsend hmId
    · obtain ⟨mr,hr,he⟩ := List.mem_map.mp hsend
      have hne := receipt_queue_ids_disjoint hL q i hi ls hn hr
      rw [he] at hne
      exact False.elim (hne hmId)
  have he : Msg.toFp m=[(w.w:Fp),((j-1:Nat):Fp),((w.step j).sym:Fp),
      if j+1=w.steps.length then 1 else 0] := by
    simp only [m,Msg.toFp,List.map_cons,List.map_nil]
    split <;> rfl
  rw [he] at hown
  exact hown

end ZkFormal.NearV3.Qv.Extract
