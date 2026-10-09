import ZkFormal.NearV3.Rcpt.Link.SourceVerify

namespace ZkFormal.NearV3
open NearSpec

/-- Two occurrences of one list in a list with distinct mapped ids force it empty. -/
theorem duplicate_list_empty {α β : Type} (f : α → β) (pre rs mid post : List α)
    (hn : ((pre ++ rs ++ mid ++ rs ++ post).map f).Nodup) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons a rest =>
    have hh : ((pre.map f ++ (a :: rest).map f ++ mid.map f) ++
        ((a :: rest).map f ++ post.map f)).Nodup := by
      simpa [List.map_append, List.append_assoc] using hn
    have hsep := (List.nodup_append.mp hh).2.2
    have h1 : f a ∈ pre.map f ++ (a :: rest).map f ++ mid.map f := by simp
    have h2 : f a ∈ (a :: rest).map f ++ post.map f := by simp
    exact False.elim (hsep _ h1 _ h2 rfl)

/-- A2 turns raw receipt lists into the exact routed lists checked by distinct ids. -/
theorem source_duplicate_empty (route : Receipt → Bool) (pre rs mid post : List Receipt)
    (hr : ∀ r ∈ rs, route r = true)
    (hn : ((pre ++ rs.filter route ++ mid ++ rs.filter route ++ post).map Receipt.receiptId).Nodup) :
    rs = [] := by
  have hf : rs.filter route = rs := List.filter_eq_self.mpr hr
  rw [hf] at hn
  exact duplicate_list_empty Receipt.receiptId pre rs mid post hn

/-- Thus the source table's duplicate-list length is exactly the 12-byte empty RC header. -/
theorem source_duplicate_length (route : Receipt → Bool) (pre rs mid post : List Receipt)
    (hr : ∀ r ∈ rs, route r = true)
    (hn : ((pre ++ rs.filter route ++ mid ++ rs.filter route ++ post).map Receipt.receiptId).Nodup)
    (shard : Nat) : (u64 shard ++ encodeReceipts rs).length = 12 := by
  rw [source_duplicate_empty route pre rs mid post hr hn]
  simp [encodeReceipts, concatAll, u64, u32, leN]

end ZkFormal.NearV3
