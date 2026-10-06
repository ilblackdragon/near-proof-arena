import ZkFormal.NearV3.Extract.Ups.QNodes

/-!
# ZkFormal.NearV3.Extract.Ups.MoveKey — the hex prefix of a shortened key (spec side)

For a key `k` of nibbles (`< 16`) of length `n` and `d ≤ n`, the hex prefix of `k.drop d` is the
hex prefix of `k` with `δ = n/2 − (n−d)/2` packed bytes dropped (`hp_drop`), and its flag byte is
`leafBit + 16·odd + odd·(byte δ of hp k mod 16)` with `odd = (n − d) mod 2`: the new first nibble
is the low nibble of the byte just before the kept packed bytes (the old flag byte when `δ = 0`).
This is what a moved-key part (`MVL`, `MVE`) emits: the flag byte from the low nibble it reads,
and the key bytes copied `δ` bytes further on.
-/

namespace ZkFormal.NearV3.UpsSpec

open NearSpec

theorem pack_drop2 : ∀ (t : Nat) (l : List Nat), packNibbles (l.drop (2 * t)) = (packNibbles l).drop t
  | 0, l => by simp
  | t + 1, [] => by simp [packNibbles]
  | t + 1, [a] => by rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega]; simp [packNibbles]
  | t + 1, a :: b :: rest => by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega]
    simp only [List.drop_succ_cons, packNibbles]
    exact pack_drop2 t rest

theorem pack_len : ∀ (l : List Nat), (packNibbles l).length = l.length / 2
  | [] => by simp [packNibbles]
  | [a] => by simp [packNibbles]
  | a :: b :: rest => by simp [packNibbles, pack_len rest]; omega

theorem toNat_pack (a b : Nat) (ha : a < 16) (hb : b < 16) : (UInt8.ofNat (a * 16 + b)).toNat = a * 16 + b := by
  simp; omega

/-- The packed byte `t`. -/
theorem pack_get (l : List Nat) (hl : ∀ x ∈ l, x < 16) (t : Nat) (ht : 2 * t + 1 < l.length) :
    ((packNibbles l).map UInt8.toNat).getD t 0 = l.getD (2 * t) 0 * 16 + l.getD (2 * t + 1) 0 := by
  have h := pack_drop2 t l
  obtain ⟨a, b, rest, hr⟩ : ∃ a b rest, l.drop (2 * t) = a :: b :: rest := by
    rcases hd : l.drop (2 * t) with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · have := congrArg List.length hd; simp at this; omega
    · have := congrArg List.length hd; simp at this; omega
    · exact ⟨a, b, rest, rfl⟩
  have ga : l.getD (2 * t) 0 = a := by
    have := congrArg (fun x => x.getD 0 0) hr; simpa [List.getD_eq_getElem?_getD] using this
  have gb : l.getD (2 * t + 1) 0 = b := by
    have := congrArg (fun x => x.getD 1 0) hr
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at this
    simpa [show 2 * t + 1 = 2 * t + 1 from rfl] using this
  have ha : a < 16 := hl a (by
    have : a ∈ l.drop (2 * t) := by rw [hr]; simp
    exact List.mem_of_mem_drop this)
  have hb : b < 16 := hl b (by
    have : b ∈ l.drop (2 * t) := by rw [hr]; simp
    exact List.mem_of_mem_drop this)
  rw [hr] at h
  simp only [packNibbles] at h
  rw [ga, gb, List.getD_eq_getElem?_getD, List.getElem?_map]
  have : (packNibbles l)[t]? = some (UInt8.ofNat (a * 16 + b)) := by
    rw [show t = t + 0 from rfl, ← List.getElem?_drop, ← h]; rfl
  rw [this]; simp; omega

def lb (f : Bool) : Nat := if f then 32 else 0

theorem toNat_u8 (x : Nat) : (UInt8.ofNat x).toNat = x % 256 := by simp

theorem hp_eq (k : List Nat) (f : Bool) :
    hexPrefix k f = if k.length % 2 = 1 then UInt8.ofNat (16 + k.headD 0 + lb f) :: packNibbles k.tail
      else UInt8.ofNat (lb f) :: packNibbles k := by
  cases k with
  | nil => simp [hexPrefix, lb]
  | cons a rest =>
    by_cases h : (a :: rest).length % 2 = 1
    · rw [if_pos h]; unfold hexPrefix; simp only [h, lb]; rfl
    · rw [if_neg h]
      have h0 : (a :: rest).length % 2 = 0 := by omega
      unfold hexPrefix; simp only [h0, lb]

theorem hp_len (k : List Nat) (f : Bool) : (hexPrefix k f).length = k.length / 2 + 1 := by
  rw [hp_eq]; split
  · next h => cases k with
    | nil => simp at h
    | cons a rest => simp [pack_len] at h ⊢; omega
  · simp [pack_len]

/-- **The hex prefix of a shortened key.** -/
theorem hp_drop (k : List Nat) (f : Bool) (d : Nat) (hd : d ≤ k.length) (hk : ∀ x ∈ k, x < 16) :
    ((hexPrefix (k.drop d) f).map UInt8.toNat).drop 1 =
      (((hexPrefix k f).map UInt8.toNat).drop 1).drop (k.length / 2 - (k.length - d) / 2) ∧
    ((hexPrefix (k.drop d) f).map UInt8.toNat).getD 0 0 = lb f + 16 * ((k.length - d) % 2) +
      ((k.length - d) % 2) * (((hexPrefix k f).map UInt8.toNat).getD (k.length / 2 - (k.length - d) / 2) 0 % 16) := by
  have hlen : (k.drop d).length = k.length - d := by simp
  have hmap : ∀ (t : Nat) (l : List Nat), ((packNibbles (l.drop (2 * t))).map UInt8.toNat) =
      ((packNibbles l).map UInt8.toNat).drop t := fun t l => by rw [pack_drop2, List.map_drop]
  have hk16 : ∀ i, k.getD i 0 < 16 := fun i => by
    simp only [List.getD_eq_getElem?_getD]
    cases h : k[i]? with
    | none => simp
    | some x => simpa using hk x (List.mem_of_getElem? h)
  have hlb : lb f = 0 ∨ lb f = 32 := by unfold lb; split <;> simp
  rw [hp_eq (k.drop d), hp_eq k, hlen]
  rcases Nat.mod_two_eq_zero_or_one (k.length - d) with hm | hm
  · -- the shortened key is even
    rw [if_neg (by omega)]
    simp only [List.map_cons, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero, hm, Nat.mul_zero,
      Nat.zero_mul, Nat.add_zero]
    refine ⟨?_, by simp; rcases hlb with h | h <;> rw [h] <;> omega⟩
    rcases Nat.mod_two_eq_zero_or_one k.length with hn | hn
    · rw [if_neg (by omega)]
      simp only [List.map_cons, List.drop_succ_cons, List.drop_zero]
      rw [show d = 2 * (k.length / 2 - (k.length - d) / 2) by omega, hmap]
      congr 2; omega
    · rw [if_pos hn]
      simp only [List.map_cons, List.drop_succ_cons, List.drop_zero]
      rw [show k.drop d = k.tail.drop (2 * (k.length / 2 - (k.length - d) / 2)) by
        rw [List.drop_tail]; congr 1; omega, hmap]
  · -- the shortened key is odd: its first nibble moves into the flag byte
    rw [if_pos hm]
    have hd' : d < k.length := by omega
    simp only [List.map_cons, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero, hm, Nat.one_mul]
    have hhead : (k.drop d).headD 0 = k.getD d 0 := by
      simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]
    have htail : (k.drop d).tail = k.drop (d + 1) := by simp [List.tail_drop]
    rw [hhead, htail]
    have hx := hk16 d
    rcases Nat.mod_two_eq_zero_or_one k.length with hn | hn
    · rw [if_neg (by omega)]
      simp only [List.map_cons, List.drop_succ_cons, List.drop_zero]
      refine ⟨?_, ?_⟩
      · rw [show d + 1 = 2 * (k.length / 2 - (k.length - d) / 2) by omega, hmap]
      · rw [show k.length / 2 - (k.length - d) / 2 = (d - 1) / 2 + 1 by omega, List.getD_cons_succ,
          pack_get k hk ((d - 1) / 2) (by omega), show 2 * ((d - 1) / 2) + 1 = d by omega]
        simp only [toNat_u8]
        have := hk16 (2 * ((d - 1) / 2))
        rcases hlb with h | h <;> rw [h] <;> omega
    · rw [if_pos hn]
      simp only [List.map_cons, List.drop_succ_cons, List.drop_zero]
      refine ⟨?_, ?_⟩
      · rw [show k.drop (d + 1) = k.tail.drop (2 * (k.length / 2 - (k.length - d) / 2)) by
          rw [List.drop_tail]; congr 1; omega, hmap]
      · rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0
          rw [show k.length / 2 - (k.length - 0) / 2 = 0 by omega, List.getD_cons_zero]
          simp only [toNat_u8]
          have : k.headD 0 = k.getD 0 0 := by cases k <;> simp
          rw [this]
          rcases hlb with h | h <;> rw [h] <;> omega
        · rw [show k.length / 2 - (k.length - d) / 2 = (d / 2 - 1) + 1 by omega, List.getD_cons_succ,
            pack_get k.tail (fun x hx => hk x (List.mem_of_mem_tail hx)) (d / 2 - 1) (by simp; omega)]
          have e1 : k.tail.getD (2 * (d / 2 - 1) + 1) 0 = k.getD d 0 := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_tail]; congr 2; omega
          rw [e1, toNat_u8]
          have := hk16 (2 * (d / 2 - 1) + 1)
          have : k.tail.getD (2 * (d / 2 - 1)) 0 < 16 := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_tail]; exact hk16 _
          rcases hlb with h | h <;> rw [h] <;> omega


end ZkFormal.NearV3.UpsSpec
