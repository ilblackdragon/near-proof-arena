import ZkFormal.NearV3.Candidates.ProcPriorEvents
namespace ZkFormal.NearV3.Candidates.ProcPriorEventUniqueness
open NearSpec NearSpec.Bandwidth ProcPriorEvents

theorem zip_order {α : Type} (xs : List α) : xs.zipIdx.Pairwise (fun a b=>a.2<b.2) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [List.getElem_zipIdx, Nat.zero_add]
  exact hij

theorem write_order (ids : List Nat) (rs : List LinkAllowance) :
    (writeEvents ids rs).Pairwise (fun a b=>a.stamp<b.stamp) := by
  apply List.Pairwise.filterMap _ ?_ (zip_order rs)
  intro a b hab u hu v hv
  cases ha:ProcPriorLookup.target ids a.1 with
  | none=>simp [ha] at hu
  | some l=>
    cases hb:ProcPriorLookup.target ids b.1 with
    | none=>simp [hb] at hv
    | some m=>
      simp only [ha,Option.map_some,Option.some.injEq] at hu
      simp only [hb,Option.map_some,Option.some.injEq] at hv
      subst u;subst v
      exact hab

theorem writes_nodup (ids : List Nat) (rs : List LinkAllowance) : (writeEvents ids rs).Nodup := by
  exact (write_order ids rs).imp (fun h he=>by cases he;omega)

theorem queries_nodup (ids : List Nat) (rs : List LinkAllowance) : (queryEvents ids rs).Nodup := by
  apply List.Pairwise.map _ ?_ (List.nodup_range)
  intro a b hab he
  apply hab
  exact congrArg Event.link he

theorem events_nodup (ids : List Nat) (rs : List LinkAllowance) : (events ids rs).Nodup := by
  apply (events_perm ids rs).nodup_iff.mpr
  apply List.nodup_append.mpr
  refine ⟨writes_nodup ids rs,queries_nodup ids rs,?_⟩
  intro a ha b hb he
  have hs:=write_before_queries ids rs a ha
  have hq:=(query_source ids rs b hb).2.1
  subst b
  omega
end ZkFormal.NearV3.Candidates.ProcPriorEventUniqueness
