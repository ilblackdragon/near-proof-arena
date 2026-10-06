import NearSpecV3.TrieBuild
import NearSpec.TrieUpsertProofs

/-!
# ZkFormal.NearV3.Spec.Codec — node preimages and their decoding by `buildFor`

`PTrie.enc t` is the `RawTrieNodeWithSize` borsh serialization of a revealed
node (`t.hashOf = sha256 t.enc`, `hashOf_eq_enc`).  The lemmas here show that
the byte-level decoder inside `NearSpecV3.buildFor` inverts `enc` on
well-formed nodes: `hpDecode_hexPrefix`, `kidHashes_hashes`, and the field
round trips `leNat (leN w x) = x`.
-/

namespace ZkFormal.NearV3

open NearSpec NearSpecV3

/-! ## Little-endian integers -/

theorem leN_len (w x : Nat) : (leN w x).length = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih => simp [leN, ih]

theorem leNat_leN' (w x : Nat) (h : x < 256 ^ w) : leNat (leN w x) = x := by
  induction w generalizing x with
  | zero => simp at h; simp [leN, leNat, h]
  | succ w ih =>
    simp only [leN, leNat]
    have h' : x / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    rw [ih _ h']
    have : (UInt8.ofNat (x % 256)).toNat = x % 256 := by simp
    rw [this]; omega

@[simp] theorem u16_len (x : Nat) : (u16 x).length = 2 := leN_len 2 x
@[simp] theorem u32_len (x : Nat) : (u32 x).length = 4 := leN_len 4 x
@[simp] theorem u64_len (x : Nat) : (u64 x).length = 8 := leN_len 8 x
@[simp] theorem sha256_len (m : Bytes) : (sha256 m).length = 32 := ArenaCore.sha256_length m

theorem leNat_u16 {x : Nat} (h : x < 65536) : leNat (u16 x) = x := leNat_leN' 2 x (by simpa using h)
theorem leNat_u32 {x : Nat} (h : x < 4294967296) : leNat (u32 x) = x := leNat_leN' 4 x (by simpa using h)
theorem leNat_u64 {x : Nat} (h : x < 18446744073709551616) : leNat (u64 x) = x :=
  leNat_leN' 8 x (by simpa using h)

/-! ## Nibbles and hex-prefix -/

theorem nibbles_packNibbles : ∀ (l : List Nat), nibblesOk l = true → l.length % 2 = 0 →
    nibbles (packNibbles l) = l
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | a :: b :: rest, hok, hl => by
    have ha : a < 16 := (nibblesOk_cons.1 hok).1
    have hb : b < 16 := (nibblesOk_cons.1 (nibblesOk_cons.1 hok).2).1
    have hr := (nibblesOk_cons.1 (nibblesOk_cons.1 hok).2).2
    have hl' : rest.length % 2 = 0 := by simp at hl; omega
    have hv : (UInt8.ofNat (a * 16 + b)).toNat = a * 16 + b := by
      simp; omega
    simp only [packNibbles, nibbles, hv, nibbles_packNibbles rest hr hl']
    have h1 : (a * 16 + b) / 16 = a := by omega
    have h2 : (a * 16 + b) % 16 = b := by omega
    rw [h1, h2]

theorem toNat_ofNat_lt {x : Nat} (h : x < 256) : (UInt8.ofNat x).toNat = x := by
  simp; omega

theorem hpDecode_hexPrefix (k : List Nat) (b : Bool) (hk : nibblesOk k = true) :
    hpDecode (hexPrefix k b) = some (k, b) := by
  have hb : (if b then 32 else 0) < 33 := by split <;> omega
  rcases Nat.mod_two_eq_zero_or_one k.length with he | ho
  · -- even length
    have hhp : hexPrefix k b = UInt8.ofNat (if b then 32 else 0) :: packNibbles k := by
      unfold hexPrefix
      rcases k with _ | ⟨n, rest⟩
      · simp
      · simp only [he]
    rw [hhp]
    have hv : (UInt8.ofNat (if b then 32 else 0)).toNat = (if b then 32 else 0) := by
      split <;> rfl
    simp only [hpDecode, hv, nibbles_packNibbles k hk he]
    cases b <;> simp
  · rcases k with _ | ⟨n, rest⟩
    · simp at ho
    · have hn : n < 16 := (nibblesOk_cons.1 hk).1
      have hr := (nibblesOk_cons.1 hk).2
      have hre : rest.length % 2 = 0 := by simp at ho; omega
      cases b
      · have hhp : hexPrefix (n :: rest) false = UInt8.ofNat (16 + n) :: packNibbles rest := by
          unfold hexPrefix; simp only [ho]; rfl
        rw [hhp]
        have hv : (UInt8.ofNat (16 + n)).toNat = 16 + n := toNat_ofNat_lt (by omega)
        simp only [hpDecode, hv, nibbles_packNibbles rest hr hre]
        have e1 : (16 + n) / 16 = 1 := by omega
        have e2 : (16 + n) % 16 = n := by omega
        simp [e1, e2]
      · have hhp : hexPrefix (n :: rest) true = UInt8.ofNat (16 + n + 32) :: packNibbles rest := by
          unfold hexPrefix; simp only [ho]; rfl
        rw [hhp]
        have hv : (UInt8.ofNat (16 + n + 32)).toNat = 16 + n + 32 := toNat_ofNat_lt (by omega)
        simp only [hpDecode, hv, nibbles_packNibbles rest hr hre]
        have e1 : (16 + n + 32) / 16 = 3 := by omega
        have e2 : (16 + n + 32) % 16 = n := by omega
        simp [e1, e2]

/-! ## Node preimages -/

/-- `borsh(RawTrieNodeWithSize)` of a revealed node (`[]` for `.hash`). -/
def nodeEnc : PTrie → Bytes
  | .hash _ => []
  | .leaf k v mem => [0] ++ u32 (hexPrefix k true).length ++ hexPrefix k true ++ v.valueRef ++ u64 mem
  | .ext k c mem => [3] ++ u32 (hexPrefix k false).length ++ hexPrefix k false ++ c.hashOf ++ u64 mem
  | .branch none cs mem => [1] ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem
  | .branch (some v) cs mem => [2] ++ v.valueRef ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem

/-- Is `t` a revealed node (not `.hash`)? -/
def isNode : PTrie → Bool
  | .hash _ => false
  | _ => true

theorem hashOf_eq_enc : ∀ (t : PTrie), isNode t = true → t.hashOf = sha256 (nodeEnc t)
  | .hash _, h => by simp [isNode] at h
  | .leaf .., _ => by simp [PTrie.hashOf, nodeEnc]
  | .ext .., _ => by simp [PTrie.hashOf, nodeEnc]
  | .branch none .., _ => by simp [PTrie.hashOf, nodeEnc]
  | .branch (some _) .., _ => by simp [PTrie.hashOf, nodeEnc]

theorem hashOf_len_of_wf : ∀ (t : PTrie), t.wf = true → t.hashOf.length = 32
  | .hash h, hw => by simpa [PTrie.wf, PTrie.hashOf] using hw
  | .leaf .., _ => by simp [PTrie.hashOf]
  | .ext .., _ => by simp [PTrie.hashOf]
  | .branch none .., _ => by simp [PTrie.hashOf]
  | .branch (some _) .., _ => by simp [PTrie.hashOf]

/-! ## Children: bitmap and hash list -/

/-- Child slots as optional hashes, index order. -/
def Kids.optHashes : Kids → List (Option Bytes)
  | .nil => []
  | .none r => none :: Kids.optHashes r
  | .some c r => some c.hashOf :: Kids.optHashes r

/-- All children of a `Kids` list. -/
def Kids.all (p : PTrie → Prop) : Kids → Prop
  | .nil => True
  | .none r => Kids.all p r
  | .some c r => p c ∧ Kids.all p r

theorem kidsBitmap_shift : ∀ (cs : Kids) (i : Nat), kidsBitmap cs i = 2 ^ i * kidsBitmap cs 0
  | .nil, _ => by simp [kidsBitmap]
  | .none r, i => by
    simp only [kidsBitmap]
    rw [kidsBitmap_shift r (i + 1), kidsBitmap_shift r 1]
    simp [Nat.pow_succ, Nat.mul_assoc]
  | .some _ r, i => by
    simp only [kidsBitmap]
    rw [kidsBitmap_shift r (i + 1), kidsBitmap_shift r 1]
    simp [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc]

theorem kidsBitmap_none (r : Kids) : kidsBitmap (.none r) 0 = 2 * kidsBitmap r 0 := by
  simp only [kidsBitmap]; rw [kidsBitmap_shift r 1]

theorem kidsBitmap_some (c : PTrie) (r : Kids) : kidsBitmap (.some c r) 0 = 1 + 2 * kidsBitmap r 0 := by
  simp only [kidsBitmap]; rw [kidsBitmap_shift r 1]

theorem kidsBitmap_lt : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → kidsBitmap cs 0 < 2 ^ n
  | .nil, n, h => by simp [Kids.wf] at h; subst h; simp [kidsBitmap]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hn, hr⟩ := h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ih := kidsBitmap_lt r m (by simpa using hr)
    rw [kidsBitmap_none, Nat.pow_succ]
    generalize 2 ^ m = P at *; generalize kidsBitmap r 0 = K at *; omega
  | .some _ r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hn, -⟩, hr⟩ := h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ih := kidsBitmap_lt r m (by simpa using hr)
    rw [kidsBitmap_some, Nat.pow_succ]
    generalize 2 ^ m = P at *; generalize kidsBitmap r 0 = K at *; omega

theorem kidHashes_hashes : ∀ (cs : Kids) (n : Nat) (tail : Bytes), Kids.wf cs n = true →
    kidHashes n (kidsBitmap cs 0) (Kids.hashes cs ++ tail) = Kids.optHashes cs
  | .nil, n, _, h => by simp [Kids.wf] at h; subst h; simp [kidHashes, Kids.optHashes]
  | .none r, n, tail, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hn, hr⟩ := h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [kidsBitmap_none]
    have h1 : 2 * kidsBitmap r 0 % 2 = 0 := by omega
    have h2 : 2 * kidsBitmap r 0 / 2 = kidsBitmap r 0 := by omega
    simp only [kidHashes, h1, h2, Kids.hashes, Kids.optHashes]
    simpa using kidHashes_hashes r m tail (by simpa using hr)
  | .some c r, n, tail, h => by
    simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hn, hc⟩, hr⟩ := h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [kidsBitmap_some]
    have h1 : (1 + 2 * kidsBitmap r 0) % 2 = 1 := by omega
    have h2 : (1 + 2 * kidsBitmap r 0) / 2 = kidsBitmap r 0 := by omega
    have hl := hashOf_len_of_wf c hc
    simp only [kidHashes, h1, h2, Kids.hashes, Kids.optHashes, List.append_assoc]
    simp [hl, kidHashes_hashes r m tail (by simpa using hr)]

theorem hashes_len : ∀ (cs : Kids), Kids.all (fun c => c.wf = true) cs →
    (Kids.hashes cs).length = 32 * Kids.count cs
  | .nil, _ => by simp [Kids.hashes, Kids.count]
  | .none r, h => by simpa [Kids.hashes, Kids.count] using hashes_len r h
  | .some c r, h => by
    simp only [Kids.hashes, Kids.count, List.length_append, hashOf_len_of_wf c h.1,
      hashes_len r h.2]
    omega

theorem count_optHashes : ∀ (cs : Kids),
    ((Kids.optHashes cs).filter Option.isSome).length = Kids.count cs
  | .nil => rfl
  | .none r => by simp [Kids.optHashes, Kids.count, count_optHashes r]
  | .some c r => by simp [Kids.optHashes, Kids.count, count_optHashes r]; omega

theorem kids_all_wf : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → Kids.all (fun c => c.wf = true) cs
  | .nil, _, _ => trivial
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h; exact kids_all_wf r _ h.2
  | .some c r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h; exact ⟨h.1.2, kids_all_wf r _ h.2⟩

end ZkFormal.NearV3
