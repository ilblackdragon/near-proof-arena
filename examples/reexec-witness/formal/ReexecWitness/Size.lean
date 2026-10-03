import ReexecWitness.Roundtrip

/-!
# Proof size bound

`|encodeProof w| ≤ 4 + 347·|receipts| + revealedBytes + 33` for every
well-formed witness; with the domain limits (≤ 256 receipts, revealed trie
≤ 3 000 000 bytes) honest proofs are ≤ 3 088 869 bytes.
-/

set_option linter.unusedSimpArgs false

namespace ReexecWitness

open NearSpec NearSpec.TransferV1

theorem encKey_length (k : List Nat) : (encKey k).length = 4 + (k.length + 1) / 2 := by
  simp [encKey, packKey_length]

theorem kids_count_le : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → Kids.count cs ≤ n
  | .nil, _, _ => by simp [Kids.count]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    have := kids_count_le r (n - 1) h.2
    simp [Kids.count]; omega
  | .some _ r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    have := kids_count_le r (n - 1) h.2
    simp [Kids.count]; omega

mutual
theorem encNode_length_le : ∀ t : PTrie, t.wf = true → (encNode t).length ≤ t.revealedBytes + 33
  | .hash h, hw => by
    simp only [PTrie.wf, beq_iff_eq] at hw
    simp [encNode, PTrie.revealedBytes, hw]
  | .leaf k s m, hw => by
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    have hs := hw.1.1.2
    cases s with
    | val v => simp [encNode, PTrie.revealedBytes, encKey_length, hexPrefix_length]; omega
    | ref len h =>
      have := (slot_ref_len hs).2
      simp [encNode, PTrie.revealedBytes, encKey_length, hexPrefix_length]; omega
  | .ext k c m, hw => by
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    have := encNode_length_le c hw.1.1.2
    simp [encNode, PTrie.revealedBytes, encKey_length, hexPrefix_length]; omega
  | .branch v cs m, hw => by
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    have h1 := encKids_length_le cs 16 hw.1.2
    have h2 := kids_count_le cs 16 hw.1.2
    cases v with
    | none => simp [encNode, PTrie.revealedBytes]; omega
    | some s =>
      have hv := hw.1.1
      cases s with
      | val x => simp [encNode, PTrie.revealedBytes]; omega
      | ref len h =>
        have := (slot_ref_len (by simpa using hv)).2
        simp [encNode, PTrie.revealedBytes]; omega
theorem encKids_length_le : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true →
    (encKids cs).length ≤ Kids.revealedBytes cs + 33 * Kids.count cs
  | .nil, _, _ => by simp [encKids]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    have := encKids_length_le r (n - 1) h.2
    simp [encKids, Kids.revealedBytes, Kids.count]; omega
  | .some c r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    have h1 := encKids_length_le r (n - 1) h.2
    have h2 := encNode_length_le c h.1.2
    simp [encKids, Kids.revealedBytes, Kids.count]; omega
end

theorem valid_le64 {s : Bytes} (h : AccountId.valid s = true) : s.length ≤ 64 := by
  simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem receipt_encode_length (r : Receipt) (hw : r.wf = true) : r.encode.length ≤ 347 := by
  obtain ⟨pred, recv, rid, signer, ⟨tag, kd⟩, gp, dep⟩ := r
  simp only [Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨hp, hr⟩, hs⟩, hk⟩, hid⟩, -⟩, -⟩ := hw
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hk
  have := valid_le64 hp; have := valid_le64 hr; have := valid_le64 hs
  have : kd.length ≤ 64 := by omega
  simp [Receipt.encode, PublicKey.encode]; omega

theorem concatAll_length_le (rs : List Receipt) (hw : rs.all Receipt.wf = true) :
    (concatAll (rs.map Receipt.encode)).length ≤ 347 * rs.length := by
  induction rs with
  | nil => simp [concatAll]
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    have := receipt_encode_length r hw.1
    simp only [List.map_cons, concatAll, List.length_append, List.length_cons]
    have := ih hw.2
    omega

theorem encodeProof_length_le (w : Witness) (hr : w.receipts.all Receipt.wf = true)
    (ht : w.trie.wf = true) :
    (encodeProof w).length ≤ 4 + 347 * w.receipts.length + w.trie.revealedBytes + 33 := by
  have := concatAll_length_le w.receipts hr
  have := encNode_length_le w.trie ht
  simp only [encodeProof, encodeReceipts, List.length_append, u32_length]
  omega

end ReexecWitness
