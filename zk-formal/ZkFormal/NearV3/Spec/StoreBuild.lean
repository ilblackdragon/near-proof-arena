import ZkFormal.NearV3.Spec.Codec

/-!
# ZkFormal.NearV3.Spec.StoreBuild — `buildFor` reconstructs a stored trie

The PTrie-level core of `StoreBuildStmt` (V3-D0-DESIGN §3.3, §6.2).

`Stored s t`: every revealed node of `t` and every revealed value is the
*first match* of its own digest in the hash-indexed store `s` (what
`storeGet` returns).  `fdepth t k` is the number of revealed nodes the lookup
of `k` visits.  Then, for any fuel `f` and key set `keys` whose lookups in `t`
are determined (`t.find k ≠ none`):

* `buildFor_refinedBy` — `buildFor s f t.hashOf keys` is a hash-pruning of `t`
  (`PTrie.refinedBy`), hence has the same root hash (`buildFor_hashOf`), and
  every `upsert`/`find` on it agrees with `t` (NearSpec's refinement lemmas);
* `buildFor_find` — for every `k ∈ keys` with `fdepth t k ≤ f`, the built
  trie answers `find k` exactly as `t` does.

No hypothesis on SHA-256 is used: `Stored` is a statement about which bytes the
store returns, which the record layer (`Records.lean`) derives from
`HashFunctional`.
-/

namespace ZkFormal.NearV3

open NearSpec NearSpecV3

/-- `b` is what the store returns for its own digest. -/
def Found (s : Store) (b : Bytes) : Prop := storeGet s (sha256 b) = some b

def SlotStored (s : Store) : Slot → Prop
  | .val v => Found s v
  | .ref _ _ => True

def OptSlotStored (s : Store) : Option Slot → Prop
  | some v => SlotStored s v
  | none => True

mutual
/-- Every revealed node preimage and revealed value of `t` is found in `s`. -/
def Stored (s : Store) : PTrie → Prop
  | .hash _ => True
  | .leaf k v m => Found s (nodeEnc (.leaf k v m)) ∧ SlotStored s v
  | .ext k c m => Found s (nodeEnc (.ext k c m)) ∧ Stored s c
  | .branch v cs m => Found s (nodeEnc (.branch v cs m)) ∧ OptSlotStored s v ∧ KidsStored s cs
def KidsStored (s : Store) : Kids → Prop
  | .nil => True
  | .none r => KidsStored s r
  | .some c r => Stored s c ∧ KidsStored s r
end

mutual
/-- Number of revealed nodes the lookup of `key` visits. -/
def fdepth : PTrie → List Nat → Nat
  | .hash _, _ => 0
  | .leaf _ _ _, _ => 1
  | .ext k c _, key => if isPrefix k key then 1 + fdepth c (key.drop k.length) else 1
  | .branch _ _ _, [] => 1
  | .branch _ cs _, n :: rest => 1 + kfdepth cs n rest
def kfdepth : Kids → Nat → List Nat → Nat
  | .nil, _, _ => 0
  | .none _, 0, _ => 0
  | .some c _, 0, key => fdepth c key
  | .none r, i + 1, key => kfdepth r i key
  | .some _ r, i + 1, key => kfdepth r i key
end

/-! ## Value slots -/

/-- Hash field of a value reference. -/
def slotHash : Slot → Bytes
  | .val v => sha256 v
  | .ref _ h => h

theorem valueRef_eq (v : Slot) : v.valueRef = u32 v.len ++ slotHash v := by
  cases v <;> rfl

theorem slotHash_len (v : Slot) (h : slotOk v = true) : (slotHash v).length = 32 := by
  cases v with
  | val b => simp [slotHash]
  | ref len hh => simp [slotOk] at h; simp [slotHash, h.2]

theorem slot_len_lt (v : Slot) (h : slotOk v = true) : v.len < 4294967296 := by
  cases v with
  | val b => simpa [slotOk, Slot.len] using h
  | ref len hh => simp [slotOk] at h; simpa [Slot.len] using h.1

/-- The slot `mkSlot` builds from a stored slot `v`: `v` itself when wanted
(its lookup is determined), a `ValueRef` refining `v` otherwise. -/
theorem mkSlot_spec (s : Store) (v : Slot) (want : Bool) (hs : SlotStored s v)
    (hw : want = true → v.get ≠ none) :
    SlotRefines (mkSlot s v.len (slotHash v) want) v ∧ (want = true → mkSlot s v.len (slotHash v) want = v) := by
  cases v with
  | val b =>
    simp only [SlotStored, Found] at hs
    cases want
    · simp [mkSlot, SlotRefines, slotHash, Slot.len]
    · simp [mkSlot, slotHash, Slot.len, hs, SlotRefines]
  | ref len h =>
    cases want
    · simp [mkSlot, SlotRefines, slotHash, Slot.len]
    · simp [Slot.get] at hw

/-! ## Unfolding `buildFor` on a stored node -/

theorem enc_split (A : Bytes) (t : UInt8) (m : Nat) :
    (([t] ++ A ++ u64 m).drop (([t] ++ A ++ u64 m).length - 8)) = u64 m ∧
    (([t] ++ A ++ u64 m).take (([t] ++ A ++ u64 m).length - 8)) = t :: A := by
  constructor <;> simp

theorem buildFor_node (s : Store) (f : Nat) (keys : List (List Nat)) (hk : keys.isEmpty = false)
    (t : UInt8) (A : Bytes) (m : Nat) (hm : m < 18446744073709551616)
    (hg : storeGet s (sha256 ([t] ++ A ++ u64 m)) = some ([t] ++ A ++ u64 m)) :
    buildFor s (f + 1) (sha256 ([t] ++ A ++ u64 m)) keys =
      (match t :: A with
      | 0 :: rest =>
        let klen := leNat (rest.take 4)
        match hpDecode ((rest.drop 4).take klen) with
        | some (k, true) =>
          let r2 := rest.drop (4 + klen)
          if r2.length != 36 then .hash (sha256 ([t] ++ A ++ u64 m)) else
          .leaf k (mkSlot s (leNat (r2.take 4)) (r2.drop 4) (keys.any (· == k))) m
        | _ => .hash (sha256 ([t] ++ A ++ u64 m))
      | 3 :: rest =>
        let klen := leNat (rest.take 4)
        match hpDecode ((rest.drop 4).take klen) with
        | some (k, false) =>
          let child := rest.drop (4 + klen)
          if child.length != 32 then .hash (sha256 ([t] ++ A ++ u64 m)) else
          let keys' := (keys.filter (isPrefix k)).map (·.drop k.length)
          .ext k (buildFor s f child keys') m
        | _ => .hash (sha256 ([t] ++ A ++ u64 m))
      | 1 :: rest => branchWith (buildFor s f) (sha256 ([t] ++ A ++ u64 m)) none rest keys m
      | 2 :: rest =>
        if rest.length < 36 then .hash (sha256 ([t] ++ A ++ u64 m)) else
        branchWith (buildFor s f) (sha256 ([t] ++ A ++ u64 m))
          (some (mkSlot s (leNat (rest.take 4)) ((rest.drop 4).take 32) (keys.any (· == []))))
          (rest.drop 36) keys m
      | _ => .hash (sha256 ([t] ++ A ++ u64 m))) := by
  have ⟨hd, ht⟩ := enc_split A t m
  have hlen : ¬ ([t] ++ A ++ u64 m).length < 9 := by simp
  rw [buildFor]
  simp only [hk, hg, Bool.false_eq_true, ↓reduceIte, hlen]
  rw [hd, ht, leNat_u64 hm]
  rfl

/-! ## Branch children -/

theorem kids_spec (s : Store) (f : Nat) (g : Bytes → List (List Nat) → PTrie)
    (hg : ∀ (c : PTrie) (ks : List (List Nat)), c.wf = true → Stored s c →
      (∀ k ∈ ks, c.find k ≠ none) →
      (g c.hashOf ks).refinedBy c ∧ ∀ k ∈ ks, fdepth c k ≤ f → (g c.hashOf ks).find k = c.find k) :
    ∀ (cs : Kids) (i : Nat) (keys : List (List Nat)), Kids.all (fun c => c.wf = true) cs →
      KidsStored s cs → (∀ n rest, (i + n) :: rest ∈ keys → Kids.find cs n rest ≠ none) →
      Kids.refinedBy (buildKidsWith g i (Kids.optHashes cs) keys) cs ∧
      ∀ n rest, (i + n) :: rest ∈ keys → kfdepth cs n rest ≤ f →
        Kids.find (buildKidsWith g i (Kids.optHashes cs) keys) n rest = Kids.find cs n rest
  | .nil, i, keys, _, _, _ => by
    refine ⟨by simp [Kids.optHashes, buildKidsWith, Kids.refinedBy], ?_⟩
    intro n rest _ _
    simp [Kids.optHashes, buildKidsWith]
  | .none r, i, keys, hw, hs, hp => by
    have ih := kids_spec s f g hg r (i + 1) keys hw hs (fun n rest h => by
      have := hp (n + 1) rest (by rwa [show i + (n + 1) = i + 1 + n by omega])
      simpa [Kids.find] using this)
    refine ⟨by simpa [Kids.optHashes, buildKidsWith, Kids.refinedBy] using ih.1, ?_⟩
    intro n rest hm hd
    cases n with
    | zero => simp [Kids.optHashes, buildKidsWith, Kids.find]
    | succ n =>
      simp only [Kids.optHashes, buildKidsWith, Kids.find]
      exact ih.2 n rest (by rwa [show i + 1 + n = i + (n + 1) by omega]) (by simpa [kfdepth] using hd)
  | .some c r, i, keys, hw, hs, hp => by
    have ih := kids_spec s f g hg r (i + 1) keys hw.2 hs.2 (fun n rest h => by
      have := hp (n + 1) rest (by rwa [show i + (n + 1) = i + 1 + n by omega])
      simpa [Kids.find] using this)
    let ks := (keys.filter (fun k => k.head? == some i)).map (·.drop 1)
    have hmem : ∀ k ∈ ks, i :: k ∈ keys := by
      intro k hk
      simp only [ks, List.mem_map, List.mem_filter, beq_iff_eq] at hk
      obtain ⟨key, ⟨hkey, hhd⟩, rfl⟩ := hk
      cases key with
      | nil => simp at hhd
      | cons x xs => simp at hhd; subst hhd; simpa using hkey
    have hmem' : ∀ k, i :: k ∈ keys → k ∈ ks := by
      intro k hk
      simp only [ks, List.mem_map, List.mem_filter, beq_iff_eq]
      exact ⟨i :: k, ⟨hk, rfl⟩, rfl⟩
    have hc := hg c ks hw.1 hs.1 (fun k hk => by
      have := hp 0 k (by simpa using hmem k hk)
      simpa [Kids.find] using this)
    refine ⟨?_, ?_⟩
    · simp only [Kids.optHashes, buildKidsWith, Kids.refinedBy]
      exact ⟨hc.1, ih.1⟩
    · intro n rest hm hd
      cases n with
      | zero =>
        simp only [Kids.optHashes, buildKidsWith, Kids.find]
        exact hc.2 rest (hmem' rest (by simpa using hm)) (by simpa [kfdepth] using hd)
      | succ n =>
        simp only [Kids.optHashes, buildKidsWith, Kids.find]
        exact ih.2 n rest (by rwa [show i + 1 + n = i + (n + 1) by omega]) (by simpa [kfdepth] using hd)

theorem branchWith_spec (s : Store) (f : Nat) (h : Bytes) (v : Option Slot) (cs : Kids) (tail : Bytes)
    (keys : List (List Nat)) (m : Nat) (hw : Kids.wf cs 16 = true) (htl : tail = []) :
    branchWith (buildFor s f) h v (u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ tail) keys m =
      .branch v (buildKidsWith (buildFor s f) 0 (Kids.optHashes cs) keys) m := by
  subst htl
  have hbm := kidsBitmap_lt cs 16 hw
  have hall := kids_all_wf cs 16 hw
  have hkh := kidHashes_hashes cs 16 [] hw
  simp only [List.append_nil] at hkh
  simp only [branchWith, List.append_nil]
  have e1 : (u16 (kidsBitmap cs 0) ++ Kids.hashes cs).take 2 = u16 (kidsBitmap cs 0) := by simp
  have e2 : (u16 (kidsBitmap cs 0) ++ Kids.hashes cs).drop 2 = Kids.hashes cs := by simp
  rw [e1, e2, leNat_u16 (by simpa using hbm), hkh, count_optHashes]
  simp [hashes_len cs hall]

/-! ## Per-node decoding -/

theorem buildFor_leaf (s : Store) (f : Nat) (keys : List (List Nat)) (hk : keys.isEmpty = false)
    (k : List Nat) (v : Slot) (m : Nat) (hw : (PTrie.leaf k v m).wf = true)
    (hf : Found s (nodeEnc (.leaf k v m))) :
    buildFor s (f + 1) (PTrie.leaf k v m).hashOf keys =
      .leaf k (mkSlot s v.len (slotHash v) (keys.any (· == k))) m := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨hnk, hso⟩, hmw⟩, hhp⟩ := hw
  have hgt := hf
  simp only [Found, nodeEnc] at hgt
  have hA : [(0 : UInt8)] ++ u32 (hexPrefix k true).length ++ hexPrefix k true ++ v.valueRef ++ u64 m =
      [0] ++ (u32 (hexPrefix k true).length ++ hexPrefix k true ++ v.valueRef) ++ u64 m := by simp
  rw [hA] at hgt
  have hh : (PTrie.leaf k v m).hashOf =
      sha256 ([0] ++ (u32 (hexPrefix k true).length ++ hexPrefix k true ++ v.valueRef) ++ u64 m) := by
    simp [PTrie.hashOf]
  rw [hh, buildFor_node s f keys hk 0 _ m hmw hgt]
  have hL := leNat_u32 hhp
  have hd := hpDecode_hexPrefix k true hnk
  have hvl : v.valueRef.length = 36 := by
    rw [valueRef_eq]; simp [slotHash_len v hso]
  have e1 : (u32 (hexPrefix k true).length ++ hexPrefix k true ++ v.valueRef).take 4 =
      u32 (hexPrefix k true).length := by simp
  have e2 : ((u32 (hexPrefix k true).length ++ hexPrefix k true ++ v.valueRef).drop 4).take
      (hexPrefix k true).length = hexPrefix k true := by simp
  have e3 : (u32 (hexPrefix k true).length ++ hexPrefix k true ++ v.valueRef).drop
      (4 + (hexPrefix k true).length) = v.valueRef := by simp [List.drop_append]
  simp only [e1, hL, e2, hd, e3, hvl]
  rw [valueRef_eq]
  have e4 : (u32 v.len ++ slotHash v).take 4 = u32 v.len := by simp
  have e5 : (u32 v.len ++ slotHash v).drop 4 = slotHash v := by simp
  simp [e4, e5, leNat_u32 (slot_len_lt v hso)]

theorem buildFor_ext (s : Store) (f : Nat) (keys : List (List Nat)) (hk : keys.isEmpty = false)
    (k : List Nat) (c : PTrie) (m : Nat) (hw : (PTrie.ext k c m).wf = true)
    (hf : Found s (nodeEnc (.ext k c m))) :
    buildFor s (f + 1) (PTrie.ext k c m).hashOf keys =
      .ext k (buildFor s f c.hashOf ((keys.filter (isPrefix k)).map (·.drop k.length))) m := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨hnk, hcw⟩, hmw⟩, hhp⟩ := hw
  have hgt := hf
  simp only [Found, nodeEnc] at hgt
  have hA : [(3 : UInt8)] ++ u32 (hexPrefix k false).length ++ hexPrefix k false ++ c.hashOf ++ u64 m =
      [3] ++ (u32 (hexPrefix k false).length ++ hexPrefix k false ++ c.hashOf) ++ u64 m := by simp
  rw [hA] at hgt
  have hh : (PTrie.ext k c m).hashOf =
      sha256 ([3] ++ (u32 (hexPrefix k false).length ++ hexPrefix k false ++ c.hashOf) ++ u64 m) := by
    simp [PTrie.hashOf]
  rw [hh, buildFor_node s f keys hk 3 _ m hmw hgt]
  have hL := leNat_u32 hhp
  have hd := hpDecode_hexPrefix k false hnk
  have hcl := hashOf_len_of_wf c hcw
  have e1 : (u32 (hexPrefix k false).length ++ hexPrefix k false ++ c.hashOf).take 4 =
      u32 (hexPrefix k false).length := by simp
  have e2 : ((u32 (hexPrefix k false).length ++ hexPrefix k false ++ c.hashOf).drop 4).take
      (hexPrefix k false).length = hexPrefix k false := by simp
  have e3 : (u32 (hexPrefix k false).length ++ hexPrefix k false ++ c.hashOf).drop
      (4 + (hexPrefix k false).length) = c.hashOf := by simp [List.drop_append]
  simp only [e1, hL, e2, hd, e3, hcl]
  rfl

theorem buildFor_branch (s : Store) (f : Nat) (keys : List (List Nat)) (hk : keys.isEmpty = false)
    (cs : Kids) (m : Nat) (hw : (PTrie.branch none cs m).wf = true)
    (hf : Found s (nodeEnc (.branch none cs m))) :
    buildFor s (f + 1) (PTrie.branch none cs m).hashOf keys =
      .branch none (buildKidsWith (buildFor s f) 0 (Kids.optHashes cs) keys) m := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨-, hcw⟩, hmw⟩ := hw
  have hgt := hf
  simp only [Found, nodeEnc] at hgt
  have hA : [(1 : UInt8)] ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 m =
      [1] ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs) ++ u64 m := by simp
  rw [hA] at hgt
  have hh : (PTrie.branch none cs m).hashOf =
      sha256 ([1] ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs) ++ u64 m) := by
    simp [PTrie.hashOf]
  rw [hh, buildFor_node s f keys hk 1 _ m hmw hgt]
  have := branchWith_spec s f (sha256 ([1] ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs) ++ u64 m))
    none cs [] keys m hcw rfl
  simp only [List.append_nil] at this
  exact this

theorem buildFor_branchV (s : Store) (f : Nat) (keys : List (List Nat)) (hk : keys.isEmpty = false)
    (v : Slot) (cs : Kids) (m : Nat) (hw : (PTrie.branch (some v) cs m).wf = true)
    (hf : Found s (nodeEnc (.branch (some v) cs m))) :
    buildFor s (f + 1) (PTrie.branch (some v) cs m).hashOf keys =
      .branch (some (mkSlot s v.len (slotHash v) (keys.any (· == []))))
        (buildKidsWith (buildFor s f) 0 (Kids.optHashes cs) keys) m := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨hso, hcw⟩, hmw⟩ := hw
  have hgt := hf
  simp only [Found, nodeEnc] at hgt
  rw [valueRef_eq] at hgt
  have hA : [(2 : UInt8)] ++ (u32 v.len ++ slotHash v) ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 m =
      [2] ++ (u32 v.len ++ slotHash v ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs)) ++ u64 m := by simp
  rw [hA] at hgt
  have hh : (PTrie.branch (some v) cs m).hashOf =
      sha256 ([2] ++ (u32 v.len ++ slotHash v ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs)) ++ u64 m) := by
    simp [PTrie.hashOf, valueRef_eq]
  rw [hh, buildFor_node s f keys hk 2 _ m hmw hgt]
  have hsl := slotHash_len v hso
  have e0 : ¬ (u32 v.len ++ slotHash v ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs)).length < 36 := by
    simp [hsl]; omega
  have e1 : (u32 v.len ++ slotHash v ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs)).take 4 = u32 v.len := by
    simp
  have e2 : ((u32 v.len ++ slotHash v ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs)).drop 4).take 32 =
      slotHash v := by simp [hsl]
  have e3 : (u32 v.len ++ slotHash v ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs)).drop 36 =
      u16 (kidsBitmap cs 0) ++ Kids.hashes cs := by simp [List.drop_append, hsl]
  simp only [e0, ↓reduceIte, e1, e2, e3, leNat_u32 (slot_len_lt v hso)]
  have := branchWith_spec s f
    (sha256 ([2] ++ (u32 v.len ++ slotHash v ++ (u16 (kidsBitmap cs 0) ++ Kids.hashes cs)) ++ u64 m))
    (some (mkSlot s v.len (slotHash v) (keys.any (· == [])))) cs [] keys m hcw rfl
  simp only [List.append_nil] at this
  exact this

/-! ## The main induction -/

theorem find_hash_none (h : Bytes) (k : List Nat) : (PTrie.hash h).find k = none := by
  simp [PTrie.find]

/-- **`buildFor` on a stored trie.** For determined lookups, the built trie
refines `t` and, within fuel, answers `find` exactly as `t`. -/
theorem buildFor_spec (s : Store) : ∀ (f : Nat) (t : PTrie) (keys : List (List Nat)),
    t.wf = true → Stored s t → (∀ k ∈ keys, t.find k ≠ none) →
    (buildFor s f t.hashOf keys).refinedBy t ∧
    ∀ k ∈ keys, fdepth t k ≤ f → (buildFor s f t.hashOf keys).find k = t.find k := by
  intro f
  induction f with
  | zero =>
    intro t keys _ _ hp
    refine ⟨by simp [buildFor, PTrie.refinedBy], ?_⟩
    intro k hk hd
    cases t with
    | hash h => exact absurd (find_hash_none h k) (hp k hk)
    | leaf => simp [fdepth] at hd
    | ext k' c m => simp only [fdepth] at hd; split at hd <;> omega
    | branch v cs m => cases k <;> simp [fdepth] at hd
  | succ f ih =>
    intro t keys hw hs hp
    -- empty key set: `.hash`
    cases hke : keys.isEmpty with
    | true =>
      have : keys = [] := List.isEmpty_iff.1 hke
      subst this
      refine ⟨?_, by simp⟩
      simp [buildFor, PTrie.refinedBy]
    | false =>
    obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∈ keys := by
      cases keys with
      | nil => simp at hke
      | cons a _ => exact ⟨a, by simp⟩
    cases t with
    | hash h => exact absurd (find_hash_none h k0) (hp k0 hk0)
    | leaf k v m =>
      rw [buildFor_leaf s f keys hke k v m hw hs.1]
      have hsl := mkSlot_spec s v (keys.any (· == k)) hs.2 (by
        intro hw'
        obtain ⟨k', hk', he⟩ := List.any_eq_true.1 hw'
        have he' : k' = k := by simpa using he
        subst he'
        have := hp k' hk'
        simp only [PTrie.find, ↓reduceIte] at this
        intro hn; simp [hn] at this)
      refine ⟨⟨rfl, rfl, hsl.1⟩, ?_⟩
      intro key hkey _
      simp only [PTrie.find]
      by_cases e : k = key
      · subst e
        rw [hsl.2 (List.any_eq_true.2 ⟨k, hkey, by simp⟩)]
      · simp [e]
    | ext k c m =>
      rw [buildFor_ext s f keys hke k c m hw hs.1]
      have hcw : c.wf = true := (wf_ext hw).2
      let ks := (keys.filter (isPrefix k)).map (·.drop k.length)
      have ihc := ih c ks hcw hs.2 (by
        intro k' hk'
        simp only [ks, List.mem_map, List.mem_filter] at hk'
        obtain ⟨key, ⟨hkey, hpre⟩, rfl⟩ := hk'
        have := hp key hkey
        simpa [PTrie.find, hpre] using this)
      refine ⟨⟨rfl, rfl, ihc.1⟩, ?_⟩
      intro key hkey hd
      simp only [PTrie.find]
      by_cases hpre : isPrefix k key = true
      · simp only [hpre, ↓reduceIte]
        apply ihc.2
        · simp only [ks, List.mem_map, List.mem_filter]; exact ⟨key, ⟨hkey, hpre⟩, rfl⟩
        · simp only [fdepth, hpre, ↓reduceIte] at hd; omega
      · simp [hpre]
    | branch bv cs m =>
      have hcw : Kids.wf cs 16 = true := wf_branch hw
      have hks := kids_spec s f (buildFor s f) (fun c ks h1 h2 h3 => ih c ks h1 h2 h3) cs 0 keys
        (kids_all_wf cs 16 hcw) hs.2.2 (by
          intro n rest hm
          have := hp (n :: rest) (by simpa using hm)
          simpa [PTrie.find] using this)
      cases bv with
      | none =>
        rw [buildFor_branch s f keys hke cs m hw hs.1]
        refine ⟨⟨rfl, trivial, hks.1⟩, ?_⟩
        intro key hkey hd
        cases key with
        | nil => simp [PTrie.find]
        | cons n rest =>
          simp only [PTrie.find]
          exact hks.2 n rest (by simpa using hkey) (by simp only [fdepth] at hd; omega)
      | some v =>
        rw [buildFor_branchV s f keys hke v cs m hw hs.1]
        have hsl := mkSlot_spec s v (keys.any (· == [])) hs.2.1 (by
          intro hw'
          obtain ⟨k', hk', he⟩ := List.any_eq_true.1 hw'
          have he' : k' = [] := by simpa using he
          subst he'
          have := hp [] hk'
          simp only [PTrie.find] at this
          intro hn; simp [hn] at this)
        refine ⟨⟨rfl, hsl.1, hks.1⟩, ?_⟩
        intro key hkey hd
        cases key with
        | nil =>
          simp only [PTrie.find]
          rw [hsl.2 (List.any_eq_true.2 ⟨[], hkey, by simp⟩)]
        | cons n rest =>
          simp only [PTrie.find]
          exact hks.2 n rest (by simpa using hkey) (by simp only [fdepth] at hd; omega)

/-- The built trie has the stored trie's root hash. -/
theorem buildFor_hashOf (s : Store) (f : Nat) (t : PTrie) (keys : List (List Nat))
    (hw : t.wf = true) (hs : Stored s t) (hp : ∀ k ∈ keys, t.find k ≠ none) :
    (buildFor s f t.hashOf keys).hashOf = t.hashOf :=
  PTrie.hashOf_refinedBy _ _ (buildFor_spec s f t keys hw hs hp).1

end ZkFormal.NearV3
