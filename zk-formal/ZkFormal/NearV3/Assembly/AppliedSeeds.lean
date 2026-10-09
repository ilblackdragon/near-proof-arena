import ZkFormal.NearV3.Assembly.ReceiptSeedDecode
import ZkFormal.NearV3.Assembly.SourceComplete
import ZkFormal.NearV3.Rcpt.Link.WitnessSources

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

private theorem shuffle_getD_mem {α : Type} (xs : List α) (seed : Bytes) {a : α}
    (h : a ∈ (shuffleWithSeed xs seed).getD xs) : a ∈ xs := by
  classical
  cases he : shuffleWithSeed xs seed with
  | none => simpa [he] using h
  | some ys =>
    simp only [he, Option.getD_some] at h
    unfold shuffleWithSeed at he
    cases hs : shuffle xs (Rng.ofSeed seed) with
    | none => simp [hs] at he
    | some p =>
      have hp : p.1 = ys := by simpa [hs] using he
      rw [← hp] at h
      exact (shuffle_perm hs).mem_iff.mp h

theorem appliedReceipts_mem_entry {k : WalkD0} {w : StateWitness} {r : Receipt}
    (h : r ∈ appliedReceipts k w) : ∃ e ∈ w.entries, r ∈ e.receipts := by
  rw [appliedReceipts_eq_flatMap] at h
  obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp h
  unfold blockApplied at hb
  obtain ⟨rs,hrs,hr⟩ := List.mem_flatten.mp hb
  obtain ⟨e,he,heq⟩ := List.mem_map.mp hrs
  subst rs
  have her := (List.mem_filter.mp hr).1
  have he := shuffle_getD_mem _ _ he
  obtain ⟨x,_,hx⟩ := List.mem_filterMap.mp he
  rcases x with ⟨s,ci⟩
  dsimp only at hx
  split at hx
  · exact ⟨e, lookupLast_mem hx, her⟩
  · cases hx

theorem appliedReceipts_seed_exact {k : WalkD0} {w : StateWitness} {bs : Bytes}
    (hw : decodeStateWitness bs = .ok w) :
    ∀ r ∈ appliedReceipts k w, ReceiptSeedExact r := by
  intro r hr
  obtain ⟨e,he,hr⟩ := appliedReceipts_mem_entry hr
  exact decodeStateWitness_receipt_seeds hw e he r hr

theorem receiptListSeed_applied {k : WalkD0} {w : StateWitness} {bs : Bytes}
    (hw : decodeStateWitness bs = .ok w) :
    (receiptListSeed (appliedReceipts k w)).rs.map (fun r => r.toRcptV.toReceipt) =
      appliedReceipts k w := by
  simp only [receiptListSeed, List.map_map]
  conv => rhs; rw [← List.map_id (appliedReceipts k w)]
  apply List.map_congr_left
  intro r hr
  exact appliedReceipts_seed_exact hw r hr

end ZkFormal.NearV3.Assembly
