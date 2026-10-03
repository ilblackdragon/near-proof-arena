import ReexecWitness.CodecLemmas

/-!
# Round trip of the proof codec: tries, receipts, proofs
-/

set_option linter.unusedSimpArgs false

namespace ReexecWitness

open NearSpec NearSpec.TransferV1

/-! ## Partial tries -/

theorem kidBits_lt : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → kidBits cs < 2 ^ n
  | .nil, n, h => by simp [Kids.wf] at h; subst h; simp [kidBits]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hn, hr⟩ := h
    have := kidBits_lt r (n - 1) hr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at this
    simp only [kidBits, Nat.pow_succ]; omega
  | .some c r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hn, -⟩, hr⟩ := h
    have := kidBits_lt r (n - 1) hr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at this
    simp only [kidBits, Nat.pow_succ]; omega

/-- Revealed-size budget under which every length field fits its width. -/
def sizeOk (n : Nat) : Prop := n ≤ 3000000

theorem slot_val_len {v : Bytes} (h : slotOk (.val v) = true) : v.length < 4294967296 := by
  simpa [slotOk] using h

theorem slot_ref_len {len : Nat} {h : Bytes} (hs : slotOk (.ref len h) = true) :
    len < 4294967296 ∧ h.length = 32 := by
  simpa [slotOk] using hs

theorem packNibbles_length : ∀ l : List Nat, (packNibbles l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [packNibbles]
  | _ :: _ :: rest => by
    simp only [packNibbles, List.length_cons, packNibbles_length rest]
    omega

theorem hexPrefix_length (k : List Nat) (b : Bool) : (hexPrefix k b).length = 1 + k.length / 2 := by
  rcases k with _ | ⟨n, rest⟩
  · simp [hexPrefix, packNibbles]
  · by_cases h : (rest.length + 1) % 2 = 1
    · simp only [hexPrefix, List.length_cons, h, packNibbles_length]
      omega
    · have h0 : (rest.length + 1) % 2 = 0 := by omega
      simp only [hexPrefix, List.length_cons, h0, packNibbles_length]
      omega

theorem key_len_of_budget (k : List Nat) (b : Bool) (n : Nat) (h : (hexPrefix k b).length ≤ n)
    (hn : n ≤ 3000000) : k.length < 4294967296 := by
  rw [hexPrefix_length] at h; omega

mutual
theorem dec_node : ∀ (t : PTrie), t.wf = true → t.revealedBytes ≤ 3000000 →
    ∀ (f : Nat) (rest : Bytes), (encNode t).length ≤ f →
    decNode f (encNode t ++ rest) = some (t, rest)
  | .hash h, hw, _, f, rest, hf => by
    simp only [PTrie.wf, beq_iff_eq] at hw
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [encNode] at hf; omega⟩
    simp [encNode, decNode, readHash_append h rest hw]
  | .leaf k s m, hw, hb, f, rest, hf => by
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨hk, hs⟩, hm⟩, hl⟩ := hw
    have hkl : k.length < 4294967296 := by
      apply key_len_of_budget k true 3000000 _ (Nat.le_refl _)
      cases s <;> simp [PTrie.revealedBytes] at hb <;> omega
    cases s with
    | val v =>
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [encNode] at hf; omega⟩
      simp only [encNode, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, decNode]
      simp only [show ((1 : UInt8) = 0) = False by decide, show ((1 : UInt8) = 1) = True by decide,
        ite_false, ite_true, decLeaf]
      rw [decKey_encKey k _ hk hkl]
      simp only [decVal]
      rw [readBorsh_append _ _ (slot_val_len hs)]
      simp [readU64_append m rest hm]
    | ref len h =>
      obtain ⟨hlen, hh⟩ := slot_ref_len hs
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [encNode] at hf; omega⟩
      simp only [encNode, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, decNode]
      simp only [show ((2 : UInt8) = 0) = False by decide, show ((2 : UInt8) = 1) = False by decide,
        show ((2 : UInt8) = 2) = True by decide, ite_false, ite_true, decLeaf]
      rw [decKey_encKey k _ hk hkl]
      simp only [decRef]
      rw [readU32_append _ _ hlen]
      simp only
      rw [readHash_append _ _ hh]
      simp [readU64_append m rest hm]
  | .ext k c m, hw, hb, f, rest, hf => by
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨hk, hc⟩, hm⟩, hl⟩ := hw
    have hcb : c.revealedBytes ≤ 3000000 := by simp [PTrie.revealedBytes] at hb; omega
    have hkl : k.length < 4294967296 := by
      apply key_len_of_budget k false 3000000 _ (Nat.le_refl _)
      simp [PTrie.revealedBytes] at hb; omega
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [encNode] at hf; omega⟩
    have hcf : (encNode c).length ≤ g := by simp [encNode] at hf; omega
    simp only [encNode, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, decNode]
    simp only [show ((3 : UInt8) = 0) = False by decide, show ((3 : UInt8) = 1) = False by decide,
      show ((3 : UInt8) = 2) = False by decide, show ((3 : UInt8) = 3) = True by decide,
      ite_false, ite_true]
    rw [decKey_encKey k _ hk hkl]
    simp only
    rw [dec_node c hc hcb g _ hcf]
    simp [readU64_append m rest hm]
  | .branch v cs m, hw, hb, f, rest, hf => by
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨hv, hcs⟩, hm⟩ := hw
    have hkb : Kids.revealedBytes cs ≤ 3000000 := by
      cases v with
      | none => simp [PTrie.revealedBytes] at hb; omega
      | some s => cases s <;> simp [PTrie.revealedBytes] at hb <;> omega
    have hbits := kidBits_lt cs 16 hcs
    have body : ∀ g, (encKids cs).length ≤ g → ∀ (vs : Option Slot),
        decBranch (decNode g) vs (u16 (kidBits cs) ++ (encKids cs ++ (u64 m ++ rest))) =
          some (.branch vs cs m, rest) := by
      intro g hg vs
      simp only [decBranch]
      rw [readU16_append _ _ (by simpa using hbits)]
      simp only
      rw [dec_kids cs 16 hcs hkb g _ hg]
      simp [readU64_append m rest hm]
    cases v with
    | none =>
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [encNode] at hf; omega⟩
      have hg : (encKids cs).length ≤ g := by simp [encNode] at hf; omega
      simp only [encNode, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, decNode]
      simp only [show ((4 : UInt8) = 0) = False by decide, show ((4 : UInt8) = 1) = False by decide,
        show ((4 : UInt8) = 2) = False by decide, show ((4 : UInt8) = 3) = False by decide,
        show ((4 : UInt8) = 4) = True by decide, ite_false, ite_true]
      exact body g hg none
    | some s =>
      cases s with
      | val x =>
        have hx := slot_val_len (by simpa using hv)
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [encNode] at hf; omega⟩
        have hg : (encKids cs).length ≤ g := by simp [encNode] at hf; omega
        simp only [encNode, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, decNode]
        simp only [show ((5 : UInt8) = 0) = False by decide, show ((5 : UInt8) = 1) = False by decide,
          show ((5 : UInt8) = 2) = False by decide, show ((5 : UInt8) = 3) = False by decide,
          show ((5 : UInt8) = 4) = False by decide, show ((5 : UInt8) = 5) = True by decide,
          ite_false, ite_true, decVal]
        rw [readBorsh_append _ _ hx]
        exact body g hg _
      | ref len h =>
        obtain ⟨hlen, hh⟩ := slot_ref_len (by simpa using hv)
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [encNode] at hf; omega⟩
        have hg : (encKids cs).length ≤ g := by simp [encNode] at hf; omega
        simp only [encNode, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, decNode]
        simp only [show ((6 : UInt8) = 0) = False by decide, show ((6 : UInt8) = 1) = False by decide,
          show ((6 : UInt8) = 2) = False by decide, show ((6 : UInt8) = 3) = False by decide,
          show ((6 : UInt8) = 4) = False by decide, show ((6 : UInt8) = 5) = False by decide,
          show ((6 : UInt8) = 6) = True by decide, ite_false, ite_true, decRef]
        rw [readU32_append _ _ hlen]
        simp only
        rw [readHash_append _ _ hh]
        exact body g hg _

theorem dec_kids : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → Kids.revealedBytes cs ≤ 3000000 →
    ∀ (f : Nat) (rest : Bytes), (encKids cs).length ≤ f →
    decKids (decNode f) n (kidBits cs) (encKids cs ++ rest) = some (cs, rest)
  | .nil, n, hw, _, f, rest, _ => by
    simp [Kids.wf] at hw; subst hw; simp [decKids, encKids]
  | .none r, n, hw, hb, f, rest, hf => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
    obtain ⟨hn, hr⟩ := hw
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hr
    have ih := dec_kids r m hr (by simpa [Kids.revealedBytes] using hb) f rest (by simpa [encKids] using hf)
    simp only [decKids, kidBits, encKids]
    have h1 : ¬ (2 * kidBits r % 2 = 1) := by omega
    have h2 : 2 * kidBits r / 2 = kidBits r := by omega
    simp [h1, h2, ih]
  | .some c r, n, hw, hb, f, rest, hf => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
    obtain ⟨⟨hn, hc⟩, hr⟩ := hw
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hr
    simp only [Kids.revealedBytes] at hb
    simp only [encKids, List.length_append] at hf
    have ihc := dec_node c hc (by omega) f (encKids r ++ rest) (by omega)
    have ih := dec_kids r m hr (by omega) f rest (by omega)
    simp only [decKids, kidBits, encKids, List.append_assoc]
    have h1 : (2 * kidBits r + 1) % 2 = 1 := by omega
    have h2 : (2 * kidBits r + 1) / 2 = kidBits r := by omega
    simp [h1, h2, ihc, ih]
end


/-! ## Receipts -/

theorem readU8_cons (b : UInt8) (x : Bytes) : readU8 (b :: x) = some (b.toNat, x) := by
  simp [readU8, readLE, takeN, leNat]

theorem mid_eq (x : Bytes) : u32 0 ++ (u32 0 ++ (u32 1 ++ ([3] ++ x))) = receiptMid ++ x := by
  simp [receiptMid]

theorem valid_len {s : Bytes} (h : AccountId.valid s = true) : s.length < 4294967296 := by
  simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem decReceipt_encode (r : Receipt) (hw : r.wf = true) (rest : Bytes) :
    decReceipt (r.encode ++ rest) = some (r, rest) := by
  obtain ⟨pred, recv, rid, signer, ⟨tag, kd⟩, gp, dep⟩ := r
  simp only [Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨hp, hr⟩, hs⟩, hk⟩, hid⟩, hgp⟩, hdep⟩ := hw
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hk
  have htag : tag < 256 := by omega
  simp only [Receipt.encode, PublicKey.encode, List.append_assoc]
  unfold decReceipt
  rw [readBorsh_append _ _ (valid_len hp)]; simp only
  rw [readBorsh_append _ _ (valid_len hr)]; simp only
  rw [readHash_append _ _ hid]; simp only
  rw [List.singleton_append, readU8_cons]
  simp only [show (0 : UInt8).toNat = 0 from rfl, ne_eq, not_true_eq_false, ite_false]
  rw [readBorsh_append _ _ (valid_len hs)]; simp only
  rw [readU8_append _ _ htag]; simp only
  have hkd : takeN (if tag = 0 then 32 else 64) (kd ++ (u128 gp ++ (u32 0 ++ (u32 0 ++ (u32 1 ++
      ([3] ++ (u128 dep ++ rest))))))) = some (kd, u128 gp ++ (u32 0 ++ (u32 0 ++ (u32 1 ++
      ([3] ++ (u128 dep ++ rest)))))) := by
    have := takeN_append kd (u128 gp ++ (u32 0 ++ (u32 0 ++ (u32 1 ++ ([3] ++ (u128 dep ++ rest))))))
    rcases hk with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ <;> simpa [hl] using this
  have hnt : ¬ (tag ≠ 0 ∧ tag ≠ 1) := by omega
  simp only [hnt, ite_false, hkd]
  rw [readU128_append _ _ hgp]; simp only
  have hmid : ∀ x, takeN 13 (receiptMid ++ x) = some (receiptMid, x) := fun x => takeN_append receiptMid x
  rw [mid_eq, hmid]
  simp only [ne_eq, not_true_eq_false, ite_false]
  rw [readU128_append _ _ hdep]
  rfl

theorem readMany_receipts (rs : List Receipt) (hw : rs.all Receipt.wf = true) (rest : Bytes) :
    readMany decReceipt rs.length (concatAll (rs.map Receipt.encode) ++ rest) = some (rs, rest) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    simp only [List.length_cons, List.map_cons, concatAll, List.append_assoc, readMany]
    rw [decReceipt_encode r hw.1]
    simp only
    rw [ih hw.2]

/-! ## Proofs -/

/-- Conditions under which the codec round-trips (all implied by `DomainStatic`). -/
structure Encodable (w : Witness) : Prop where
  receipts_wf : w.receipts.all Receipt.wf = true
  receipts_len : w.receipts.length < 4294967296
  trie_wf : w.trie.wf = true
  trie_size : w.trie.revealedBytes ≤ 3000000

theorem decodeProof_encodeProof (w : Witness) (h : Encodable w) :
    decodeProof (encodeProof w) = some w := by
  obtain ⟨rs, t⟩ := w
  unfold decodeProof encodeProof
  simp only [encodeReceipts, List.append_assoc]
  rw [readU32_append _ _ h.receipts_len]; simp only
  rw [readMany_receipts rs h.receipts_wf]; simp only
  have := dec_node t h.trie_wf h.trie_size (encNode t ++ []).length []
    (by simp)
  rw [List.append_nil] at this
  rw [this]

end ReexecWitness
