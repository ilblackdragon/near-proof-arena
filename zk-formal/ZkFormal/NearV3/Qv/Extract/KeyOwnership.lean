import ZkFormal.NearV3.Qv.Extract.ImplicitWalkBound

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

theorem repaired_key_owner (id : Fp) (bs : NearSpec.Bytes) {m : List Fp}
    (hm : m∈repairedKeyTraffic id bs) : m.getD 0 0=id := by
  obtain ⟨i,_,hm⟩ := List.mem_flatMap.mp hm
  simp only [repairedKeyRow,List.mem_append] at hm
  rcases hm with hm|hm
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl <;> rfl
  · split at hm
    · simp only [List.mem_singleton] at hm
      subst m
      rfl
    · simp at hm

/-- Actual queue sends bearing one walk ID all belong to that same extracted
request; no per-message choice of a different native key remains. -/
theorem physical_key_ownership {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Candidates.KeyTrafficRepair.table tr tt pub) (q : WalkChain tr tt)
    (i : Nat) (hi : i<q.segs.length) (hK : (kPublic.eval tr tt 0 pub).toNat<64)
    {m : List Fp}
    (hm : m∈(List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.KeyTrafficRepair.interactions tr tt r pub B_KEYNIB true))
    (hid : m.getD 0 0=wid.eval tr tt (q.segs[i]'hi).1 pub) :
    m∈repairedKeyTraffic (wid.eval tr tt (q.segs[i]'hi).1 pub)
      (physicalWalkBytes tr tt (q.segs[i]'hi)) := by
  rw [repaired_key_physical h q] at hm
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨j,hj,hp⟩ := List.getElem_of_mem hp
  subst p
  have ho := repaired_key_owner _ _ hm
  have he := queue_walk_id_unique (Candidates.KeyTrafficRepair.local_to_base h) q i j hi hj hK
    (hid.symm.trans ho)
  subst j
  exact hm

end ZkFormal.NearV3.Qv.Extract
