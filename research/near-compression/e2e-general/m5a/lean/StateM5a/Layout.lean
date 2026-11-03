import NearSpec.Trie

/-!
# StateM5a.Layout — the node rows' byte layout is `PTrie.hashOf`'s preimage

`BR` holds a branch as 16 slot flags `f_i`, 16 × 32 child-hash bytes and sends the hash bytes of
slot `i` at offset `32 · rank_i` (`rank_i = Σ_{i'<i} f_{i'}`) of the children block, and the
bitmap as `Σ f_i 2^i`.  `SN` holds a key as nibbles `k_j` with prefix flags and sends `hexPrefix`
bytes computed by the formula `hpAt`.  The lemmas:

* `kidsBitmap_eq` / `hashes_eq` / `hashes_block`: the spec's `kidsBitmap cs 0` and `Kids.hashes cs`
  (the bitmap and children block of `PTrie.hashOf (.branch …)`) are exactly those expressions in
  the slot view `slots cs`;
* `hexPrefix_eq`: `hexPrefix k leaf` (the key bytes of `PTrie.hashOf (.leaf …)` / `(.ext …)`) is
  `hpAt k leaf m` for `m < 1 + |k|/2`, the length the row's `hplen` counts.
-/

namespace StateM5a.Layout

open NearSpec

/-! ## Branch: slots, bitmap, children block -/

def slots : Kids → List (Option PTrie)
  | .nil => []
  | .none r => none :: slots r
  | .some c r => some c :: slots r

/-- `Σ_t [slot t present] · 2^(j+t)`. -/
def bmOf : List (Option PTrie) → Nat → Nat
  | [], _ => 0
  | o :: r, j => (if o.isSome then 2 ^ j else 0) + bmOf r (j + 1)

theorem kidsBitmap_eq : ∀ (cs : Kids) (j : Nat), kidsBitmap cs j = bmOf (slots cs) j
  | .nil, _ => rfl
  | .none r, j => by simp [kidsBitmap, slots, bmOf, kidsBitmap_eq r]
  | .some c r, j => by simp [kidsBitmap, slots, bmOf, kidsBitmap_eq r]

theorem hashes_eq : ∀ cs : Kids,
    Kids.hashes cs = ((slots cs).filterMap (Option.map PTrie.hashOf)).flatten
  | .nil => rfl
  | .none r => by simp [Kids.hashes, slots, hashes_eq r]
  | .some c r => by simp [Kids.hashes, slots, hashes_eq r]

/-- The 32 bytes of slot `i` sit at offset `32 · rank_i` of the children block. -/
theorem block_at {β : Type} (g : PTrie → List β) :
    ∀ (L : List (Option PTrie)) (i : Nat) (a : PTrie), L[i]? = some (some a) →
      (∀ o ∈ L, ∀ x, o = some x → (g x).length = 32) →
      (((L.filterMap (Option.map g)).flatten.drop (32 * ((L.take i).filter Option.isSome).length)).take 32)
        = g a
  | [], _, _, h, _ => by simp at h
  | o :: r, 0, a, h, hl => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have : (g a).length = 32 := hl _ (List.mem_cons_self) a rfl
    simp [List.take_left' this]
  | none :: r, i + 1, a, h, hl => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.filterMap_cons, Option.map_none, List.take_succ_cons, List.filter_cons,
      Option.isSome_none, Bool.false_eq_true, ite_false]
    exact block_at g r i a h (fun o ho => hl o (List.mem_cons_of_mem _ ho))
  | some c :: r, i + 1, a, h, hl => by
    simp only [List.getElem?_cons_succ] at h
    have hc : (g c).length = 32 := hl _ (List.mem_cons_self) c rfl
    simp only [List.filterMap_cons, Option.map_some, List.flatten_cons, List.take_succ_cons,
      List.filter_cons, Option.isSome_some, ite_true, List.length_cons]
    rw [show 32 * ((List.filter Option.isSome (List.take i r)).length + 1) =
      (g c).length + 32 * (List.filter Option.isSome (List.take i r)).length by rw [hc]; omega]
    rw [← List.drop_drop, List.drop_left]
    exact block_at g r i a h (fun o ho => hl o (List.mem_cons_of_mem _ ho))

/-! ## Short nodes: `hexPrefix` -/

/-- The row's formula for `hexPrefix` byte `m` (`hp_0 = 32·leaf + odd·(16 + k_0)`, then nibble
pairs at an offset fixed by the parity). -/
def hpAt (k : List Nat) (leaf : Bool) (m : Nat) : Nat :=
  let odd := k.length % 2
  let g := fun j => k.getD j 0
  if m = 0 then 32 * (if leaf then 1 else 0) + odd * (16 + g 0)
  else odd * (16 * g (2 * m - 1) + g (2 * m)) + (1 - odd) * (16 * g (2 * m - 2) + g (2 * m - 1))

theorem packNibbles_eq : ∀ (l : List Nat), (∀ x ∈ l, x < 16) →
    (packNibbles l).map UInt8.toNat =
      (List.range (l.length / 2)).map fun m => 16 * l.getD (2 * m) 0 + l.getD (2 * m + 1) 0
  | [], _ => rfl
  | [_], _ => by simp [packNibbles]
  | a :: b :: r, h => by
    have ha : a < 16 := h a (by simp)
    have hb : b < 16 := h b (by simp)
    have hr : ∀ x ∈ r, x < 16 := fun x hx => h x (by simp [hx])
    simp only [packNibbles, List.map_cons, List.length_cons]
    rw [packNibbles_eq r hr]
    have e : (r.length + 1 + 1) / 2 = r.length / 2 + 1 := by omega
    rw [e, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
    · have : a * 16 + b < 256 := by omega
      simp only [UInt8.toNat_ofNat', List.getD_cons_succ, Nat.mul_zero, List.getD_cons_zero]
      omega
    all_goals (apply List.map_congr_left; intro m _; simp [Function.comp, Nat.mul_succ, List.getD_cons_succ])

theorem hexPrefix_eq (k : List Nat) (leaf : Bool) (hk : ∀ x ∈ k, x < 16) :
    (hexPrefix k leaf).map UInt8.toNat = (List.range (1 + k.length / 2)).map (hpAt k leaf) := by
  rw [Nat.add_comm, List.range_succ_eq_map]
  rcases Nat.mod_two_eq_zero_or_one k.length with hev | hodd
  · have hp : hexPrefix k leaf = UInt8.ofNat (if leaf then 32 else 0) :: packNibbles k := by
      cases k with
      | nil => rfl
      | cons n rest =>
        unfold hexPrefix
        rw [hev]
        rfl
    rw [hp]
    simp only [List.map_cons, List.map_map]
    rw [packNibbles_eq k hk]
    congr 1
    · simp only [hpAt, hev, ite_true]
      cases leaf <;> simp
    · apply List.map_congr_left
      intro m _
      simp only [Function.comp, hpAt, hev, Nat.succ_ne_zero, ite_false]
      have e1 : 2 * (m + 1) - 2 = 2 * m := by omega
      have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      simp [e1, e2]
  · obtain ⟨n, rest, rfl⟩ : ∃ n rest, k = n :: rest := by
      cases k with
      | nil => simp at hodd
      | cons n rest => exact ⟨n, rest, rfl⟩
    have hn : n < 16 := hk n (by simp)
    have hr : ∀ x ∈ rest, x < 16 := fun x hx => hk x (by simp [hx])
    have hp : hexPrefix (n :: rest) leaf =
        UInt8.ofNat (16 + n + (if leaf then 32 else 0)) :: packNibbles rest := by
      unfold hexPrefix
      rw [hodd]
      rfl
    rw [hp]
    simp only [List.map_cons, List.map_map]
    rw [packNibbles_eq rest hr]
    have e : (n :: rest).length / 2 = rest.length / 2 := by simp at hodd ⊢; omega
    rw [e]
    congr 1
    · simp only [hpAt, hodd, ite_true, List.getD_cons_zero, UInt8.toNat_ofNat']
      cases leaf <;> simp <;> omega
    · apply List.map_congr_left
      intro m _
      simp only [Function.comp, hpAt, hodd, Nat.succ_ne_zero, ite_false]
      have e1 : 2 * (m + 1) - 1 = (2 * m) + 1 := by omega
      have e2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      simp [e1, e2, List.getD_cons_succ]

/-- **Continuation chunks** (`SNC`): `hexPrefix` byte `32c + m` (`c ≥ 1`, `m < 32`) is the nibble
pair at key offset `64c − 2 + odd + 2m`; so chunk `c` holds the 64 key nibbles from `64c − 2 + odd`
on and sends bytes `32c .. 32c + 31` as `16·k_{2m} + k_{2m+1}` of its own nibbles, and the head
row (`62 + odd` nibbles) sends bytes `0 .. 31`. -/
theorem hpAt_chunk (k : List Nat) (leaf : Bool) (c m : Nat) (hc : 1 ≤ c) :
    hpAt k leaf (32 * c + m) =
      16 * k.getD (64 * c - 2 + k.length % 2 + 2 * m) 0 + k.getD (64 * c - 2 + k.length % 2 + 2 * m + 1) 0 := by
  unfold hpAt
  have h0 : 32 * c + m ≠ 0 := by omega
  simp only [h0, ite_false]
  rcases Nat.mod_two_eq_zero_or_one k.length with hev | hodd
  · rw [hev]
    have e1 : 2 * (32 * c + m) - 2 = 64 * c - 2 + 0 + 2 * m := by omega
    have e2 : 2 * (32 * c + m) - 1 = 64 * c - 2 + 0 + 2 * m + 1 := by omega
    rw [e1, e2]; omega
  · rw [hodd]
    have e1 : 2 * (32 * c + m) - 1 = 64 * c - 2 + 1 + 2 * m := by omega
    have e2 : 2 * (32 * c + m) = 64 * c - 2 + 1 + 2 * m + 1 := by omega
    rw [e1, e2]; omega

end StateM5a.Layout
