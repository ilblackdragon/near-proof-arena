import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountQueries

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly ZkFormal.Near

private theorem sum_bounded {α : Type} (f : α→Nat) (n : Nat) (xs : List α)
    (h : ∀x∈xs,f x≤n) : (xs.map f).sum≤n*xs.length := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem account_lookup_rows (rs : List Receipt) (ha : ∀r∈rs,r.receiverId.length≤64) :
    ((accountLookupQueries rs).map (fun q=>q.key.length+2)).sum≤132*rs.length := by
  have hq : ∀q∈accountLookupQueries rs,q.key.length+2≤132 := by
    intro q hq
    obtain ⟨⟨r,i⟩,hr,rfl⟩:=List.mem_map.mp hq
    have hh:=ha r (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hr))
    simp only [accountKeyPath,nibbles_length,List.length_cons]
    omega
  simpa only [accountLookupQueries,List.length_map,List.length_zipIdx] using
    sum_bounded (fun q : NativeLookupQuery=>q.key.length+2) 132 (accountLookupQueries rs) hq

theorem native_account_query_rows (pairs : List (PTrie×PTrie)) (rs : List Receipt)
    (ws : List WalkR) (h : nativeQueryWalks pairs (accountLookupQueries rs)=some ws)
    (ha : ∀r∈rs,r.receiverId.length≤64) : (ws.flatMap (·.steps)).length≤132*rs.length := by
  rw [nativeQueryWalks_rows pairs _ ws h]
  exact account_lookup_rows rs ha

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
