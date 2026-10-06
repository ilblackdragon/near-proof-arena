import ZkFormal.NearV3.Spec.StoreBuild

/-!
# ZkFormal.NearV3.Spec.StoreBuilt — what `buildFor` builds, on any store

For **any** witness store `ws` (no hypothesis on SHA-256 or on the entries),
the partial trie `buildFor (mkStore ws) f h keys` (`h` a 32-byte digest):

* has root hash `h` (decoding then re-encoding a node gives back its bytes);
* is `PTrie.wf`;
* is `Stored` in `mkStore ws`: every revealed node preimage and value is what
  the store returns for its digest (the first match);
* visits at most `f` revealed nodes on any lookup (`fdepth ≤ f`).

`built_spec` is the first half of the completeness direction of
`StoreBuildStmt` (the second half, building hash-consed records, is in
`StoreComplete.lean`).
-/

namespace ZkFormal.NearV3

open NearSpec NearSpecV3

/-! ## Bytes -/

theorem leN_leNat (l : Bytes) : leN l.length (leNat l) = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, leN, leNat]
    have h1 : (b.toNat + 256 * leNat bs) % 256 = b.toNat := by have := b.toNat_lt; omega
    have h2 : (b.toNat + 256 * leNat bs) / 256 = leNat bs := by have := b.toNat_lt; omega
    rw [h1, h2, ih]; simp

theorem leNat_lt (l : Bytes) : leNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [leNat]
  | cons b bs ih =>
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have := b.toNat_lt
    generalize 256 ^ bs.length = P at *
    generalize leNat bs = L at *
    have : 256 * L + 256 ≤ 256 * P := by
      have := Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt ih); simpa [Nat.mul_succ] using this
    rw [Nat.mul_comm P 256]; omega

theorem leN_leNat' {l : Bytes} {w : Nat} (h : l.length = w) : leN w (leNat l) = l := by
  subst h; exact leN_leNat l

theorem take_len {l : Bytes} {n : Nat} (h : n ≤ l.length) : (l.take n).length = n := by
  simp [List.length_take, h]

/-! ## Hex-prefix decoding inverts -/

theorem packNibbles_nibbles : ∀ (b : Bytes), packNibbles (nibbles b) = b
  | [] => rfl
  | x :: xs => by
    simp only [nibbles, packNibbles, packNibbles_nibbles xs]
    have : x.toNat / 16 * 16 + x.toNat % 16 = x.toNat := by omega
    rw [this]; simp

theorem nibbles_length (b : Bytes) : (nibbles b).length = 2 * b.length := by
  induction b with
  | nil => rfl
  | cons x xs ih => simp [nibbles, ih]; omega

theorem nibbles_ok (b : Bytes) : nibblesOk (nibbles b) = true := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    simp only [nibbles, nibblesOk, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
    have := x.toNat_lt
    exact ⟨by omega, by omega, ih⟩

theorem hexPrefix_hpDecode {b : Bytes} {k : List Nat} {leaf : Bool} (h : hpDecode b = some (k, leaf)) :
    hexPrefix k leaf = b ∧ nibblesOk k = true := by
  cases b with
  | nil => simp [hpDecode] at h
  | cons f rest =>
    simp only [hpDecode] at h
    have hf := f.toNat_lt
    by_cases h3 : f.toNat / 16 > 3
    · simp [h3] at h
    · simp only [h3, ↓reduceIte] at h
      by_cases hodd : f.toNat / 16 % 2 = 1
      · simp only [hodd, beq_self_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and,
          Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlen : (f.toNat % 16 :: nibbles rest).length % 2 = 1 := by
          simp [nibbles_length]
        refine ⟨?_, ?_⟩
        · simp only [List.singleton_append]
          unfold hexPrefix
          simp only [hlen, packNibbles_nibbles]
          congr 1
          apply UInt8.toNat.inj
          by_cases hc : f.toNat / 16 / 2 % 2 = 1
          · simp only [hc, beq_self_eq_true, ↓reduceIte]
            rw [toNat_ofNat_lt (by omega)]; omega
          · have hc' : (f.toNat / 16 / 2 % 2 == 1) = false := by simpa using hc
            simp only [hc', Bool.false_eq_true, ↓reduceIte]
            rw [toNat_ofNat_lt (by omega)]; omega
        · simp only [nibblesOk, List.singleton_append, List.all_cons, Bool.and_eq_true,
            decide_eq_true_eq]
          exact ⟨by omega, by simpa [nibblesOk] using nibbles_ok rest⟩
      · have hodd' : (f.toNat / 16 % 2 == 1) = false := by simpa using hodd
        simp only [hodd', ↓reduceIte, List.nil_append] at h
        by_cases hlo : f.toNat % 16 = 0
        · have hlo' : (f.toNat % 16 != 0) = false := by simpa using hlo
          simp only [Bool.not_false, Bool.true_and, hlo', Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hlen : (nibbles rest).length % 2 = 0 := by simp [nibbles_length]
          refine ⟨?_, nibbles_ok rest⟩
          have hhp : hexPrefix (nibbles rest) (f.toNat / 16 / 2 % 2 == 1) =
              UInt8.ofNat (if (f.toNat / 16 / 2 % 2 == 1) = true then 32 else 0) ::
                packNibbles (nibbles rest) := by
            unfold hexPrefix
            rcases hn : nibbles rest with _ | ⟨n0, r0⟩
            · simp
            · rw [hn] at hlen; simp only [hlen]
          simp only [List.nil_append]
          rw [hhp, packNibbles_nibbles]
          congr 1
          apply UInt8.toNat.inj
          by_cases hc : f.toNat / 16 / 2 % 2 = 1
          · simp only [hc, beq_self_eq_true, ↓reduceIte]
            rw [toNat_ofNat_lt (by omega)]; omega
          · have hc' : (f.toNat / 16 / 2 % 2 == 1) = false := by simpa using hc
            simp only [hc', Bool.false_eq_true, ↓reduceIte]
            rw [toNat_ofNat_lt (by omega)]; omega
        · have hlo' : (f.toNat % 16 != 0) = true := by simpa using hlo
          simp [hlo'] at h

/-! ## The store -/

theorem storeGet_some {ws : List Bytes} {h b : Bytes} (hg : storeGet (mkStore ws) h = some b) :
    sha256 b = h ∧ b ∈ ws := by
  unfold storeGet mkStore at hg
  cases hfind : (ws.map (fun v => (sha256 v, v))).find? (fun p => p.1 == h) with
  | none => simp [hfind] at hg
  | some p =>
    simp only [hfind, Option.some.injEq] at hg
    have hp := List.mem_of_find?_eq_some hfind
    have hpe := List.find?_some hfind
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hp
    simp only [beq_iff_eq] at hpe
    subst hg
    exact ⟨hpe, hv⟩

/-! ## Value slots -/

theorem mkSlot_facts (ws : List Bytes) (len : Nat) (vh : Bytes) (want : Bool) :
    (mkSlot (mkStore ws) len vh want).valueRef = u32 len ++ vh ∧
    SlotStored (mkStore ws) (mkSlot (mkStore ws) len vh want) ∧
    (len < 4294967296 → vh.length = 32 → slotOk (mkSlot (mkStore ws) len vh want) = true) := by
  unfold mkSlot
  cases want with
  | false => simp [Slot.valueRef, SlotStored, slotOk]; exact fun a b => ⟨a, b⟩
  | true =>
    simp only [↓reduceIte]
    cases hg : storeGet (mkStore ws) vh with
    | none => simp [Slot.valueRef, SlotStored, slotOk]; exact fun a b => ⟨a, b⟩
    | some v =>
      obtain ⟨hsv, -⟩ := storeGet_some hg
      by_cases hl : v.length = len
      · simp only [hl, beq_self_eq_true, ↓reduceIte, Slot.valueRef, hsv, SlotStored, Found, hg,
          slotOk, true_and]
        intro h1 _; simpa using h1
      · have hl' : (v.length == len) = false := by simpa using hl
        simp [hl', Slot.valueRef, SlotStored, slotOk]; exact fun a b => ⟨a, b⟩

/-! ## Children -/

/-- What `buildFor s f` produces for a 32-byte digest. -/
def BuiltOk (s : Store) (f : Nat) (h : Bytes) (t : PTrie) : Prop :=
  t.hashOf = h ∧ t.wf = true ∧ Stored s t ∧ ∀ k, fdepth t k ≤ f

theorem builtOk_hash {s : Store} {f : Nat} {h : Bytes} (hl : h.length = 32) : BuiltOk s f h (.hash h) :=
  ⟨rfl, by simp [PTrie.wf, hl], trivial, fun _ => by simp [fdepth]⟩

theorem kids_built (s : Store) (f : Nat) (g : Bytes → List (List Nat) → PTrie)
    (hg : ∀ h ks, h.length = 32 → BuiltOk s f h (g h ks)) :
    ∀ (n bm : Nat) (bs : Bytes) (i : Nat) (keys : List (List Nat)), bm < 2 ^ n →
      bs.length = 32 * ((kidHashes n bm bs).filter Option.isSome).length →
      Kids.wf (buildKidsWith g i (kidHashes n bm bs) keys) n = true ∧
      kidsBitmap (buildKidsWith g i (kidHashes n bm bs) keys) 0 = bm ∧
      Kids.hashes (buildKidsWith g i (kidHashes n bm bs) keys) = bs ∧
      KidsStored s (buildKidsWith g i (kidHashes n bm bs) keys) ∧
      ∀ j key, kfdepth (buildKidsWith g i (kidHashes n bm bs) keys) j key ≤ f
  | 0, bm, bs, i, keys, hb, hl => by
    simp [kidHashes] at hl hb; subst hb
    simp [kidHashes, buildKidsWith, Kids.wf, kidsBitmap, Kids.hashes, hl, KidsStored, kfdepth]
  | n + 1, bm, bs, i, keys, hb, hl => by
    have hb2 : bm / 2 < 2 ^ n := by rw [Nat.pow_succ] at hb; generalize 2 ^ n = P at *; omega
    by_cases hbit : bm % 2 = 1
    · have hbit' : (bm % 2 == 1) = true := by simpa using hbit
      simp only [kidHashes, hbit', ↓reduceIte, List.filter_cons, Option.isSome_some,
        List.length_cons] at hl ⊢
      have hl32 : 32 ≤ bs.length := by omega
      have hrest : (bs.drop 32).length =
          32 * ((kidHashes n (bm / 2) (bs.drop 32)).filter Option.isSome).length := by
        simp; omega
      obtain ⟨w, bmp, hh, st, dp⟩ := kids_built s f g hg n (bm / 2) (bs.drop 32) (i + 1) keys hb2 hrest
      have hc := hg (bs.take 32) ((keys.filter (fun k => k.head? == some i)).map (·.drop 1))
        (take_len hl32)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [buildKidsWith, Kids.wf, hc.2.1, Nat.add_sub_cancel, w]; simp
      · simp only [buildKidsWith]; rw [kidsBitmap_some, bmp]; omega
      · simp only [buildKidsWith, Kids.hashes, hc.1, hh]; exact List.take_append_drop 32 bs
      · simp only [buildKidsWith, KidsStored]; exact ⟨hc.2.2.1, st⟩
      · intro j key
        cases j with
        | zero => simp only [buildKidsWith, kfdepth]; exact hc.2.2.2 key
        | succ j => simp only [buildKidsWith, kfdepth]; exact dp j key
    · have hbit' : (bm % 2 == 1) = false := by simpa using hbit
      simp only [kidHashes, hbit', Bool.false_eq_true, ↓reduceIte, List.filter_cons,
        Option.isSome_none] at hl ⊢
      obtain ⟨w, bmp, hh, st, dp⟩ := kids_built s f g hg n (bm / 2) bs (i + 1) keys hb2 hl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [buildKidsWith, Kids.wf, Nat.add_sub_cancel, w]; simp
      · simp only [buildKidsWith]; rw [kidsBitmap_none, bmp]; omega
      · simp only [buildKidsWith, Kids.hashes, hh]
      · simp only [buildKidsWith, KidsStored]; exact st
      · intro j key
        cases j with
        | zero => simp [buildKidsWith, kfdepth]
        | succ j => simp only [buildKidsWith, kfdepth]; exact dp j key

theorem branchWith_built (s : Store) (f : Nat) (g : Bytes → List (List Nat) → PTrie)
    (hg : ∀ h ks, h.length = 32 → BuiltOk s f h (g h ks)) (h : Bytes) (hl : h.length = 32)
    (v : Option Slot) (rest : Bytes) (keys : List (List Nat)) (mem : Nat) :
    branchWith g h v rest keys mem = .hash h ∨
    (2 ≤ rest.length ∧ ∃ K, branchWith g h v rest keys mem = .branch v K mem ∧
      Kids.wf K 16 = true ∧ u16 (kidsBitmap K 0) ++ Kids.hashes K = rest ∧ KidsStored s K ∧
      ∀ j key, kfdepth K j key ≤ f) := by
  unfold branchWith
  dsimp only
  split
  · exact Or.inl rfl
  · rename_i hlen
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
    have hlt : leNat (rest.take 2) < 2 ^ 16 := by
      have := leNat_lt (rest.take 2); simp [List.length_take] at this ⊢
      have h2 : min 2 rest.length ≤ 2 := Nat.min_le_left _ _
      calc leNat (rest.take 2) < 256 ^ min 2 rest.length := this
        _ ≤ 256 ^ 2 := Nat.pow_le_pow_right (by omega) h2
        _ = 65536 := by decide
    have hdl : (rest.drop 2).length =
        32 * ((kidHashes 16 (leNat (rest.take 2)) (rest.drop 2)).filter Option.isSome).length := by
      simp; omega
    obtain ⟨w, bmp, hh, st, dp⟩ := kids_built s f g hg 16 _ (rest.drop 2) 0 keys hlt hdl
    refine Or.inr ⟨by omega, _, rfl, w, ?_, st, dp⟩

    rw [bmp, hh]
    have : u16 (leNat (rest.take 2)) = rest.take 2 := leN_leNat' (by simp; omega)
    rw [this, List.take_append_drop]

/-! ## The main induction -/

theorem split3 (rest : Bytes) (a b : Nat) :
    rest = rest.take a ++ (rest.drop a).take b ++ rest.drop (a + b) := by
  calc rest = rest.take a ++ rest.drop a := (List.take_append_drop a rest).symm
    _ = rest.take a ++ ((rest.drop a).take b ++ (rest.drop a).drop b) := by
      congr 1; exact (List.take_append_drop b _).symm
    _ = rest.take a ++ (rest.drop a).take b ++ rest.drop (a + b) := by
      rw [List.drop_drop, List.append_assoc]

theorem enc_ok {ws : List Bytes} {h node : Bytes} (t : PTrie) (hn : isNode t = true)
    (hst : storeGet (mkStore ws) h = some node) (he : nodeEnc t = node) :
    t.hashOf = h ∧ Found (mkStore ws) (nodeEnc t) := by
  obtain ⟨hsha, -⟩ := storeGet_some hst
  rw [hashOf_eq_enc t hn, he, hsha]
  exact ⟨rfl, by rw [Found, hsha, hst]⟩

theorem leNat4_lt (l : Bytes) : leNat (l.take 4) < 4294967296 := by
  have := leNat_lt (l.take 4)
  have h2 : (l.take 4).length ≤ 4 := by simp [List.length_take]; exact Nat.min_le_left _ _
  calc leNat (l.take 4) < 256 ^ (l.take 4).length := this
    _ ≤ 256 ^ 4 := Nat.pow_le_pow_right (by omega) h2
    _ = 4294967296 := by decide

/-- **What `buildFor` builds** on any store, for a 32-byte digest. -/
theorem built_spec (ws : List Bytes) : ∀ (f : Nat) (h : Bytes) (keys : List (List Nat)), h.length = 32 →
    BuiltOk (mkStore ws) f h (buildFor (mkStore ws) f h keys) := by
  intro f
  induction f with
  | zero => intro h keys hl; simpa [buildFor] using builtOk_hash hl
  | succ f ih =>
    intro h keys hl
    rw [buildFor]
    split
    · exact builtOk_hash hl
    · split
      · exact builtOk_hash hl
      · rename_i node hst
        split
        · exact builtOk_hash hl
        · rename_i hn9
          dsimp only
          have hsplit : node = node.take (node.length - 8) ++ node.drop (node.length - 8) :=
            (List.take_append_drop _ _).symm
          have hd8 : (node.drop (node.length - 8)).length = 8 := by simp; omega
          have hmem : u64 (leNat (node.drop (node.length - 8))) = node.drop (node.length - 8) :=
            leN_leNat' hd8
          have hmemlt : leNat (node.drop (node.length - 8)) < 18446744073709551616 := by
            have := leNat_lt (node.drop (node.length - 8)); rw [hd8] at this; simpa using this
          generalize leNat (node.drop (node.length - 8)) = mem at hmem hmemlt ⊢
          split
          · -- leaf
            rename_i rest hb
            split
            · rename_i k hdec
              split
              · exact builtOk_hash hl
              · rename_i h36
                simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h36
                generalize hkl : leNat (rest.take 4) = klen at hdec h36 ⊢
                obtain ⟨hhp, hnk⟩ := hexPrefix_hpDecode hdec
                have hrl : 4 + klen ≤ rest.length := by
                  have := List.length_drop (i := 4 + klen) (l := rest); omega
                have hhpl : ((rest.drop 4).take klen).length = klen := by simp; omega
                have h4 : u32 klen = rest.take 4 := by rw [← hkl]; exact leN_leNat' (by simp; omega)
                obtain ⟨hvr, hss, hok⟩ := mkSlot_facts ws (leNat ((rest.drop (4 + klen)).take 4))
                  ((rest.drop (4 + klen)).drop 4) (keys.any (· == k))
                have h36' : rest.length - (4 + klen) = 36 := by simpa using h36
                have hr2 : u32 (leNat ((rest.drop (4 + klen)).take 4)) ++ (rest.drop (4 + klen)).drop 4 =
                    rest.drop (4 + klen) := by
                  have e : u32 (leNat ((rest.drop (4 + klen)).take 4)) = (rest.drop (4 + klen)).take 4 :=
                    leN_leNat' (by simp; omega)
                  rw [e]; exact List.take_append_drop _ _
                have henc : nodeEnc (.leaf k (mkSlot (mkStore ws) (leNat ((rest.drop (4 + klen)).take 4))
                    ((rest.drop (4 + klen)).drop 4) (keys.any (· == k))) mem) = node := by
                  simp only [nodeEnc, hhp, hhpl, h4, hvr, hr2, hmem]
                  conv => rhs; rw [hsplit, hb, split3 rest 4 klen]
                  simp
                obtain ⟨hh, hF⟩ := enc_ok _ rfl hst henc
                refine ⟨hh, ?_, ⟨hF, hss⟩, fun _ => by simp [fdepth]⟩
                have hsl := hok (leNat4_lt _) (by simp; omega)
                have hkl' : klen < 4294967296 := hkl ▸ leNat4_lt rest
                simp only [PTrie.wf, hnk, hsl, Bool.true_and]
                simp [hmemlt, hhp, hhpl, hkl']
            · exact builtOk_hash hl
          · -- extension
            rename_i rest hb
            split
            · rename_i k hdec
              split
              · exact builtOk_hash hl
              · rename_i h32
                simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h32
                generalize hkl : leNat (rest.take 4) = klen at hdec h32 ⊢
                obtain ⟨hhp, hnk⟩ := hexPrefix_hpDecode hdec
                have hrl : 4 + klen ≤ rest.length := by
                  have := List.length_drop (i := 4 + klen) (l := rest); omega
                have hhpl : ((rest.drop 4).take klen).length = klen := by simp; omega
                have h4 : u32 klen = rest.take 4 := by rw [← hkl]; exact leN_leNat' (by simp; omega)
                have hc := ih (rest.drop (4 + klen)) ((keys.filter (isPrefix k)).map (·.drop k.length)) h32
                obtain ⟨hch, hcw, hcs, hcd⟩ := hc
                have henc : nodeEnc (.ext k (buildFor (mkStore ws) f (rest.drop (4 + klen))
                    ((keys.filter (isPrefix k)).map (·.drop k.length))) mem) = node := by
                  simp only [nodeEnc, hhp, hhpl, h4, hch, hmem]
                  conv => rhs; rw [hsplit, hb, split3 rest 4 klen]
                  simp
                obtain ⟨hh, hF⟩ := enc_ok _ rfl hst henc
                refine ⟨hh, ?_, ⟨hF, hcs⟩, ?_⟩
                · have hkl' : klen < 4294967296 := hkl ▸ leNat4_lt rest
                  simp [PTrie.wf, hnk, hcw, hmemlt, hhp, hhpl, hkl']
                · intro key; simp only [fdepth]; split
                  · have := hcd (key.drop k.length); omega
                  · omega
            · exact builtOk_hash hl
          · -- branch without value
            rename_i rest hb
            rcases branchWith_built (mkStore ws) f (buildFor (mkStore ws) f)
                (fun h' ks hl' => ih h' ks hl') h hl none rest keys mem with e | ⟨_, K, e, hw, hr, hs, hd⟩
            · rw [e]; exact builtOk_hash hl
            · rw [e]
              have henc : nodeEnc (.branch none K mem) = node := by
                simp only [nodeEnc, hmem]
                conv => rhs; rw [hsplit, hb, ← hr]
                simp
              obtain ⟨hh, hF⟩ := enc_ok _ rfl hst henc
              refine ⟨hh, by simp [PTrie.wf, hw, hmemlt], ⟨hF, trivial, hs⟩, ?_⟩
              intro key
              cases key with
              | nil => simp [fdepth]
              | cons n r => simp only [fdepth]; have := hd n r; omega
          · -- branch with value
            rename_i rest hb
            split
            · exact builtOk_hash hl
            · rename_i h36
              obtain ⟨hvr, hss, hok⟩ := mkSlot_facts ws (leNat (rest.take 4)) ((rest.drop 4).take 32)
                (keys.any (· == []))
              rcases branchWith_built (mkStore ws) f (buildFor (mkStore ws) f)
                  (fun h' ks hl' => ih h' ks hl') h hl
                  (some (mkSlot (mkStore ws) (leNat (rest.take 4)) ((rest.drop 4).take 32)
                    (keys.any (· == [])))) (rest.drop 36) keys mem with e | ⟨_, K, e, hw, hr, hs, hd⟩
              · rw [e]; exact builtOk_hash hl
              · rw [e]
                have h4 : u32 (leNat (rest.take 4)) = rest.take 4 := leN_leNat' (by simp; omega)
                have henc : nodeEnc (.branch (some (mkSlot (mkStore ws) (leNat (rest.take 4))
                    ((rest.drop 4).take 32) (keys.any (· == [])))) K mem) = node := by
                  simp only [nodeEnc, hmem, hvr, h4]
                  conv => rhs; rw [hsplit, hb, split3 rest 4 32, ← hr]
                  simp
                obtain ⟨hh, hF⟩ := enc_ok _ rfl hst henc
                refine ⟨hh, ?_, ⟨hF, hss, hs⟩, ?_⟩
                · simp only [PTrie.wf, hok (leNat4_lt _) (by simp; omega), hw, hmemlt]; simp
                · intro key
                  cases key with
                  | nil => simp [fdepth]
                  | cons n r => simp only [fdepth]; have := hd n r; omega
          · exact builtOk_hash hl

end ZkFormal.NearV3
