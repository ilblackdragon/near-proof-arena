import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near

theorem indexed_flatMap {α β : Type} [Inhabited α] (xs : List α) (n : Nat)
    (g : Nat→α→List β) :
    (List.range xs.length).flatMap (fun i => g (n+i) (xs.getD i default))=
      (xs.zipIdx n).flatMap (fun p => g p.2 p.1) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      List.getD_cons_zero,List.getD_cons_succ,List.zipIdx_cons,Nat.add_zero]
    rw [←ih]
    simp only [Nat.add_assoc,Nat.add_comm 1]

theorem located_global_order (ls : RcptV3Vs) (n : Nat) (g : Nat→RcptE→List Msg) :
    (List.range ls.length).flatMap (fun j =>
      (located ls j).flatMap (fun (r,_,x) => g (n+r) x))=
      ((flatR ls).zipIdx n).flatMap (fun p => g p.2 p.1) := by
  induction ls generalizing n with
  | nil => simp [flatR]
  | cons L ls ih =>
    simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      located,List.getD_cons_zero,List.getD_cons_succ,baseR,List.take_zero,List.map_nil,
      List.sum_nil,List.take_succ_cons,List.map_cons,List.sum_cons,Nat.zero_add,
      flatR,List.flatMap_cons,List.zipIdx_append,List.flatMap_append]
    rw [←indexed_flatMap L.rs n g]
    congr 1
    have h := ih (n+L.rs.length)
    simpa only [located,List.flatMap_map,baseR,Nat.add_assoc,flatR] using h

end ZkFormal.NearV3.Rcpt.Candidates
