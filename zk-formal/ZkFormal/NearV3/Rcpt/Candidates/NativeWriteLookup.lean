import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountTouches
import ZkFormal.Near.Spec.CompleteWalk

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.Near

/-- Native writes replayed at the initial trie's stable preorder slot indices. -/
def replaySlotWrites (initial : PTrie) (values : List (Option Bytes))
    (writes : List (List Nat×Bytes)) : List (Option Bytes) :=
  writes.foldl (fun vs w => vs.set (Prune.slotIdx initial w.1) (some w.2)) values

theorem replaySlotWrites_same {a b : PTrie} (h : Prune.Same a b)
    (values : List (Option Bytes)) (writes : List (List Nat×Bytes)) :
    replaySlotWrites b values writes=replaySlotWrites a values writes := by
  unfold replaySlotWrites
  congr 1
  funext vs w
  rw [h.slot]

theorem AccountWriteRun.slot_lookup {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes post) :
    Prune.Same pre post ∧ Prune.vl post=replaySlotWrites pre (Prune.vl pre) writes := by
  induction h with
  | nil t => exact ⟨Prune.Same.refl t,rfl⟩
  | @cons t mid out key bytes rest hs ht ih =>
    obtain ⟨hsame,_,hvalues⟩ := Prune.set_same t key bytes mid hs
    refine ⟨hsame.trans ih.1,?_⟩
    rw [ih.2,replaySlotWrites_same hsame,hvalues]
    rfl

/-- Every successfully processed receipt uses the same initial index space;
repeated account writes update the same position and retain last-write order. -/
theorem native_account_slot_lookup (ctx : ApplyCtx) (rs : List Receipt) (i : Nat)
    (st out : Acc×List Limit) (h : applyReceipts ctx i st rs=.ok out) :
    ∃writes, writes.map Prod.fst=rs.map (fun r => accountKeyPath r.receiverId) ∧
      Prune.Same st.1.trie out.1.trie ∧
      Prune.vl out.1.trie=replaySlotWrites st.1.trie (Prune.vl st.1.trie) writes := by
  obtain ⟨writes,hw,hkeys⟩ := native_account_writes ctx rs i st out h
  exact ⟨writes,hkeys,hw.slot_lookup⟩

mutual
/-- Compact V3 value IDs are obtained by removing non-value preorder slots. -/
theorem compact_native_slots : ∀t : PTrie,
    (Prune.vl t).filterMap id=(occs t).flatMap ownVals
  | .hash h => rfl
  | .leaf k v m => by cases v <;> simp [Prune.vl,Slot.get,occs,ownVals,slotVal]
  | .ext k c m => by simpa [Prune.vl,occs,ownVals] using compact_native_slots c
  | .branch v cs m => by
    cases v with
    | none => simpa [Prune.vl,occs,ownVals,optSlotVal] using compact_native_kid_slots cs
    | some v =>
      cases v <;> simp [Prune.vl,Slot.get,occs,ownVals,optSlotVal,slotVal,
        compact_native_kid_slots cs]
theorem compact_native_kid_slots : ∀cs : Kids,
    (Prune.vlKids cs).filterMap id=(kOccs cs).flatMap ownVals
  | .nil => rfl
  | .none cs => compact_native_kid_slots cs
  | .some c cs => by
    simp only [Prune.vlKids,kOccs,List.filterMap_append,List.flatMap_append,
      compact_native_slots c,compact_native_kid_slots cs]
end

/-- Concrete post-value payload lookup from the initial slot space and ordered
native writes; this is exact, including repeated writes to a single receiver. -/
theorem AccountWriteRun.compact_lookup {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes post) :
    valsOf post=(replaySlotWrites pre (Prune.vl pre) writes).filterMap id := by
  rw [←h.slot_lookup.2,compact_native_slots]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates
