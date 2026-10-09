import NearSpecV3.Logged.TrieDec

/-!
# A revealed subtree re-hashes to its key

Over a store whose keys are the SHA-256 of their values (`HInv`; `mkHStore` has it,
`HInv_mkHStore`), `(revealAll s f h).hashOf = h` for every fuel and hash (`hashOf_revealAll`):
`dec` accepts only canonical encodings, so re-encoding a decoded node gives back its bytes.
-/

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

theorem length_nibbles : ∀ (b : Bytes), (nibbles b).length = 2 * b.length
  | [] => rfl
  | a :: bs => by simp [nibbles, length_nibbles bs]; omega
theorem packNibbles_nibbles : ∀ (b : Bytes), packNibbles (nibbles b) = b
  | [] => rfl
  | a :: bs => by
    simp only [nibbles, packNibbles, packNibbles_nibbles bs]
    have ha := a.toNat_lt
    have : a.toNat / 16 * 16 + a.toNat % 16 = a.toNat := by omega
    rw [this]; simp

theorem u8_eq_of_toNat {a : UInt8} {n : Nat} (h : n = a.toNat) : UInt8.ofNat n = a := by
  subst h; simp

theorem hexPrefix_hpDecode (b : Bytes) (k : List Nat) (leaf : Bool) (h : hpDecode b = some (k, leaf)) :
    hexPrefix k leaf = b := by
  match b, h with
  | f :: rest, h =>
    simp only [hpDecode] at h
    have hf := f.toNat_lt
    split at h
    · cases h
    split at h
    · cases h
    cases h
    rename_i h1 h2
    by_cases hodd : f.toNat / 16 % 2 = 1
    · simp only [hodd]
      simp
      have hlen : ((f.toNat % 16 :: nibbles rest).length) % 2 = 1 := by
        simp [length_nibbles]
      simp only [hexPrefix, hlen, packNibbles_nibbles]
      congr 1
      apply u8_eq_of_toNat
      split <;> rename_i hl <;> simp at hl <;> omega
    · have hodd' : (f.toNat / 16 % 2 == 1) = false := by simpa using hodd
      have h0 : f.toNat % 16 = 0 := by
        simp [hodd'] at h2; exact h2
      simp only [hodd', Bool.false_eq_true, ite_false, List.nil_append]
      have hlen : (nibbles rest).length % 2 = 0 := by simp [length_nibbles]
      simp only [hexPrefix, hlen, packNibbles_nibbles]
      congr 1
      apply u8_eq_of_toNat
      split <;> rename_i hl <;> simp at hl <;> omega

theorem leN_leNat : ∀ (b : Bytes), leN b.length (leNat b) = b
  | [] => rfl
  | a :: bs => by
    simp only [List.length_cons, leN, leNat]
    have ha := a.toNat_lt
    have h1 : (a.toNat + 256 * leNat bs) % 256 = a.toNat := by omega
    have h2 : (a.toNat + 256 * leNat bs) / 256 = leNat bs := by omega
    rw [h1, h2, leN_leNat bs]; simp

theorem leN_leNat' (w : Nat) (b : Bytes) (h : b.length = w) : leN w (leNat b) = b := by
  subst h; exact leN_leNat b

theorem leNat_lt : ∀ (b : Bytes), leNat b < 256 ^ b.length
  | [] => by simp [leNat]
  | a :: bs => by
    have := leNat_lt bs; have ha := a.toNat_lt
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have : 256 * leNat bs ≤ 256 * (256 ^ bs.length - 1) := by
      apply Nat.mul_le_mul_left; omega
    have h2 : 256 * (256 ^ bs.length - 1) = 256 ^ bs.length * 256 - 256 := by
      rw [Nat.mul_sub, Nat.mul_comm]
    omega

def HInv (s : HStore) : Prop := ∀ k v, hGet s k = some v → sha256 v = k

theorem hSlot_valueRef {s : HStore} (hs : HInv s) (len : Nat) (vh : Bytes) :
    (hSlot s len vh).valueRef = u32 len ++ vh := by
  unfold hSlot
  split
  · rename_i v hv
    split
    · rename_i hl
      simp at hl
      simp [Slot.valueRef, hl, hs vh v hv]
    · rfl
  · rfl

theorem kidsBitmap_succ : ∀ (ks : Kids) (i : Nat), kidsBitmap ks (i + 1) = 2 * kidsBitmap ks i
  | .nil, _ => rfl
  | .none r, i => by simp only [kidsBitmap]; exact kidsBitmap_succ r (i + 1)
  | .some _ r, i => by
    simp only [kidsBitmap]; rw [kidsBitmap_succ r (i + 1), Nat.pow_succ]; omega

theorem kidsBitmap_reveal (g : Bytes → PTrie) : ∀ (n bm : Nat) (bs : Bytes),
    kidsBitmap (revealKids g (kidHashes n bm bs)) 0 = bm % 2 ^ n
  | 0, bm, bs => by simp [kidHashes, revealKids, kidsBitmap, Nat.mod_one]
  | n + 1, bm, bs => by
    simp only [kidHashes]
    have key : bm % 2 ^ (n + 1) = bm % 2 + 2 * (bm / 2 % 2 ^ n) := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]
    split
    · rename_i h
      simp only [revealKids, kidsBitmap, kidsBitmap_succ, kidsBitmap_reveal g n (bm / 2)]
      simp at h; rw [key, h]
    · rename_i h
      simp only [revealKids, kidsBitmap, kidsBitmap_succ, kidsBitmap_reveal g n (bm / 2)]
      simp at h; rw [key]; omega

theorem hashes_reveal (g : Bytes → PTrie) (hg : ∀ c, (g c).hashOf = c) : ∀ (n bm : Nat) (bs : Bytes),
    bs.length = 32 * ((kidHashes n bm bs).filter Option.isSome).length →
    Kids.hashes (revealKids g (kidHashes n bm bs)) = bs
  | 0, bm, bs, h => by simp [kidHashes] at h; simp [kidHashes, revealKids, Kids.hashes, h]
  | n + 1, bm, bs, h => by
    simp only [kidHashes] at h ⊢
    split
    · rename_i hb
      simp only [hb, ite_true, List.filter_cons, Option.isSome_some, List.length_cons] at h
      simp only [revealKids, Kids.hashes, hg]
      rw [hashes_reveal g hg n (bm / 2) (bs.drop 32) (by simp; omega)]
      simp
    · rename_i hb
      simp only [hb] at h
      simp only [revealKids, Kids.hashes]
      exact hashes_reveal g hg n (bm / 2) bs (by simpa using h)

theorem node_split (node : Bytes) (h9 : ¬ node.length < 9) :
    node = node.take (node.length - 8) ++ u64 (leNat (node.drop (node.length - 8))) := by
  have : (node.drop (node.length - 8)).length = 8 := by simp; omega
  rw [u64, leN_leNat' 8 _ this, List.take_append_drop]

theorem dec_hash {s : HStore} (hs : HInv s) (g : Bytes → PTrie) (hg : ∀ c, (g c).hashOf = c)
    (node : Bytes) (r : RNode) (hd : dec node = some r) : (buildR s g r).hashOf = sha256 node := by
  simp only [dec] at hd
  split at hd
  · cases hd
  rename_i h9
  conv => rhs; rw [node_split node h9]
  generalize node.take (node.length - 8) = body at hd ⊢
  generalize leNat (node.drop (node.length - 8)) = mem at hd ⊢
  have hu32 : ∀ b : Bytes, b.length = 4 → u32 (leNat b) = b := fun b hb => leN_leNat' 4 b hb
  have hu16 : ∀ b : Bytes, b.length = 2 → u16 (leNat b) = b := fun b hb => leN_leNat' 2 b hb
  split at hd
  · -- leaf
    rename_i rest
    split at hd
    · rename_i k hk
      split at hd
      · cases hd
      rename_i hl
      cases hd
      simp at hl
      generalize hK : leNat (List.take 4 rest) = klen at hk hl ⊢
      simp only [buildR, PTrie.hashOf, hSlot_valueRef hs, hexPrefix_hpDecode _ _ _ hk]
      congr 1
      have h4 : (List.take 4 rest).length = 4 := by simp; omega
      have hkl : (List.take klen (List.drop 4 rest)).length = klen := by simp; omega
      rw [hkl, ← hK, hu32 _ h4, hK, hu32 _ (by simp; omega)]
      have e : List.take 4 rest ++ (List.take klen (List.drop 4 rest) ++ List.drop (4 + klen) rest) = rest := by
        rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
      conv => rhs; rw [← e]
      rw [List.take_append_drop]
      simp
    · cases hd
  · -- extension
    rename_i rest
    split at hd
    · rename_i k hk
      split at hd
      · cases hd
      rename_i hl
      cases hd
      simp at hl
      generalize hK : leNat (List.take 4 rest) = klen at hk hl ⊢
      simp only [buildR, PTrie.hashOf, hg, hexPrefix_hpDecode _ _ _ hk]
      congr 1
      have h4 : (List.take 4 rest).length = 4 := by simp; omega
      have hkl : (List.take klen (List.drop 4 rest)).length = klen := by simp; omega
      rw [hkl, ← hK, hu32 _ h4, hK]
      have e : List.take 4 rest ++ (List.take klen (List.drop 4 rest) ++ List.drop (4 + klen) rest) = rest := by
        rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
      conv => rhs; rw [← e]
      simp
    · cases hd
  · -- branch without value
    rename_i rest
    split at hd
    · cases hd
    rename_i hl
    cases hd
    simp at hl
    have hlen := kidsBitmap_reveal g 16 (leNat (List.take 2 rest)) (List.drop 2 rest)
    have h2 : (List.take 2 rest).length = 2 := by simp; omega
    have hbm : leNat (List.take 2 rest) % 2 ^ 16 = leNat (List.take 2 rest) :=
      Nat.mod_eq_of_lt (by have := leNat_lt (List.take 2 rest); rw [h2] at this; simpa using this)
    simp only [buildR, Option.map_none, PTrie.hashOf, hlen, hbm, hu16 _ h2,
      hashes_reveal g hg 16 (leNat (List.take 2 rest)) (List.drop 2 rest) (by simp; omega)]
    conv => rhs; rw [← List.take_append_drop 2 rest]
    simp
  · -- branch with value
    rename_i rest
    split at hd
    · cases hd
    split at hd
    · cases hd
    rename_i h36 hl
    cases hd
    simp at hl
    have hlen := kidsBitmap_reveal g 16 (leNat (List.take 2 (List.drop 36 rest))) (List.drop 2 (List.drop 36 rest))
    have h2 : (List.take 2 (List.drop 36 rest)).length = 2 := by simp; omega
    have hbm : leNat (List.take 2 (List.drop 36 rest)) % 2 ^ 16 = leNat (List.take 2 (List.drop 36 rest)) :=
      Nat.mod_eq_of_lt (by have := leNat_lt (List.take 2 (List.drop 36 rest)); rw [h2] at this; simpa using this)
    simp only [buildR, Option.map_some, PTrie.hashOf, hlen, hbm, hu16 _ h2, hSlot_valueRef hs,
      hashes_reveal g hg 16 (leNat (List.take 2 (List.drop 36 rest))) (List.drop 2 (List.drop 36 rest)) (by simp; omega)]
    rw [hu32 _ (by simp; omega)]
    have e : List.take 4 rest ++ (List.take 32 (List.drop 4 rest) ++ (List.take 2 (List.drop 36 rest) ++
        List.drop 2 (List.drop 36 rest))) = rest := by
      rw [List.take_append_drop]
      have : List.drop 36 rest = List.drop 32 (List.drop 4 rest) := by simp [List.drop_drop]
      rw [this, List.take_append_drop, List.take_append_drop]
    conv => rhs; rw [← e]
    simp
  · cases hd

theorem hashOf_revealAll {s : HStore} (hs : HInv s) : ∀ (f : Nat) (h : Bytes), (revealAll s f h).hashOf = h
  | 0, h => by rw [revealAll_zero]; rfl
  | f + 1, h => by
    rw [revealAll_succ]
    cases hn : hGet s h with
    | none => rfl
    | some node =>
      simp only
      cases hd : dec node with
      | none => rfl
      | some r =>
        simp only
        rw [dec_hash hs _ (hashOf_revealAll hs f) node r hd]
        exact hs h node hn

theorem cmpBytes_eq : ∀ (a b : Bytes), cmpBytes a b ≠ 0 → cmpBytes a b ≠ 2 → a = b
  | [], [] => fun _ _ => rfl
  | [], _ :: _ => by intro h0 _; simp [cmpBytes] at h0
  | _ :: _, [] => by intro _ h2; simp [cmpBytes] at h2
  | x :: xs, y :: ys => by
    intro h0 h2
    simp only [cmpBytes] at h0 h2
    by_cases h1 : x.toNat < y.toNat
    · simp [h1] at h0
    by_cases h3 : y.toNat < x.toNat
    · simp [h1, h3] at h2
    simp only [h1, h3, ite_false] at h0 h2
    have : x = y := UInt8.toNat_inj.mp (by omega)
    rw [this, cmpBytes_eq xs ys h0 h2]

def hOk : HStore → Prop
  | .tip => True
  | .node k v l r => sha256 v = k ∧ hOk l ∧ hOk r

theorem hGet_ok : ∀ (t : HStore) (k v : Bytes), hOk t → t.get? k = some v → sha256 v = k
  | .tip, _, _, _, h => by cases h
  | .node k' v' l r, k, v, ⟨hk, hl, hr⟩, h => by
    simp only [HStore.get?] at h
    split at h
    · exact hGet_ok l k v hl h
    · exact hGet_ok r k v hr h
    · rename_i h0 h2
      cases h
      rw [hk]; exact (cmpBytes_eq k k' h0 h2).symm

theorem hInsert_ok : ∀ (t : HStore) (k v : Bytes), hOk t → sha256 v = k → hOk (t.insert k v)
  | .tip, _, _, _, hv => ⟨hv, trivial, trivial⟩
  | .node k' v' l r, k, v, ⟨hk, hl, hr⟩, hv => by
    simp only [HStore.insert]
    split
    · exact ⟨hk, hInsert_ok l k v hl hv, hr⟩
    · exact ⟨hk, hl, hInsert_ok r k v hr hv⟩
    · rename_i h0 h2
      exact ⟨by rw [hv]; exact cmpBytes_eq k k' h0 h2, hl, hr⟩

theorem HInv_of_ok {t : HStore} (h : hOk t) : HInv t := fun k v hk => hGet_ok t k v h hk

theorem mkHStore_ok (values : List Bytes) : hOk (mkHStore values) := by
  unfold mkHStore
  suffices ∀ (acc : HStore), hOk acc → hOk (values.foldl (fun m v => m.insert (sha256 v) v) acc) from
    this .tip trivial
  induction values with
  | nil => intro acc h; exact h
  | cons v vs ih => intro acc h; exact ih _ (hInsert_ok acc _ v h rfl)

theorem HInv_mkHStore (values : List Bytes) : HInv (mkHStore values) := HInv_of_ok (mkHStore_ok values)

end NearSpecV3.Logged
