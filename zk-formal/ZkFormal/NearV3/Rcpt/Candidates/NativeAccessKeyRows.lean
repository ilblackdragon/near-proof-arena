import ZkFormal.NearV3.Rcpt.Candidates.NativeAccessKeyQueries
import ZkFormal.NearV3.Rcpt.Candidates.NativeCombinedLookupRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly ZkFormal.Near

theorem receipt_lookup_widths (r : Receipt) (hw : r.wf=true) :
    r.receiverId.length≤64 ∧ r.signerPk.data.length≤64 := by
  simp only [Receipt.wf,PublicKey.wf,AccountId.valid,Bool.and_eq_true,Bool.or_eq_true,
    decide_eq_true_eq,beq_iff_eq] at hw
  omega

private theorem sum_bounded {α : Type} (f : α→Nat) (n : Nat) (xs : List α)
    (h : ∀x∈xs,f x≤n) : (xs.map f).sum≤n*xs.length := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem access_key_lookup_rows (rs : List Receipt) (hw : ∀r∈rs,r.wf=true) :
    ((accessKeyLookupQueries rs).map (fun q=>q.key.length+2)).sum≤264*rs.length := by
  have hq : ∀q∈accessKeyLookupQueries rs,q.key.length+2≤264 := by
    intro q hq
    obtain ⟨⟨r,i⟩,hr,rfl⟩:=List.mem_map.mp hq
    have hr':=List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hr).1)
    obtain ⟨ha,hpk⟩:=receipt_lookup_widths r (hw r hr')
    simp only [keyAccessKey,nibbles_length,List.length_append,List.length_cons,List.length_nil,
      PublicKey.encode,u8,NearSpec.leN_length]
    omega
  have hh:=sum_bounded (fun q : NativeLookupQuery=>q.key.length+2) 264 (accessKeyLookupQueries rs) hq
  have hl : (accessKeyLookupQueries rs).length≤rs.length := by
    unfold accessKeyLookupQueries
    simp only [List.length_map]
    simpa only [List.length_zipIdx] using List.length_filter_le
      (fun p : Receipt×Nat=>p.1.predecessorId==AccountId.system && p.1.signerId==p.1.receiverId) rs.zipIdx
  omega

theorem native_access_key_rows (pairs : List (PTrie×PTrie)) (rs : List Receipt) (ws : List WalkR)
    (h : nativeQueryWalks pairs (accessKeyLookupQueries rs)=some ws) (hw : ∀r∈rs,r.wf=true) :
    (ws.flatMap (·.steps)).length≤264*rs.length := by
  rw [nativeQueryWalks_rows pairs _ ws h]
  exact access_key_lookup_rows rs hw

/-- Includes every receiver and conditional gas-refund access-key query. -/
theorem all_lookup_log22 (pairs : List (PTrie×PTrie)) (rs : List Receipt)
    (pre : PTrie) (v : Qv.MainValues) (pres : List PTrie) (resolve : Qv.Candidates.CombinedWalkGen.Resolve)
    (accounts accesses queues : List WalkR) (Is : List Render.UpsInst)
    (ha : nativeQueryWalks pairs (accountLookupQueries rs)=some accounts)
    (hx : nativeQueryWalks pairs (accessKeyLookupQueries rs)=some accesses)
    (hq : nativeQueryWalks pairs (queueLookupQueries pre v pres resolve)=some queues)
    (hr : ∀r∈rs,r.wf=true) (hn : rs.length≤4481) (hg : 24*v.shards.length≤2000000)
    (hk : pres.length≤32) (hu : Is.length≤32) :
    ((accounts++accesses++queues++upsWalkInventory Is).flatMap (·.steps)).length≤3441404 ∧
    ((accounts++accesses++queues++upsWalkInventory Is).flatMap (·.steps)).length+1≤2^22 := by
  have hac:=native_account_query_rows pairs rs accounts ha (fun r hm=>(receipt_lookup_widths r (hr r hm)).1)
  have hxc:=native_access_key_rows pairs rs accesses hx hr
  have hqc:=native_queue_rows pairs pre v pres resolve queues hq
  simp only [List.flatMap_append,List.length_append,ups_inventory_rows,hqc]
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
