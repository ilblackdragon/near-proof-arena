import ZkFormal.NearV3.Sched.Model

/-!
# ZkFormal.NearV3.Sched.Spec.Canon — canonical previous state (index lookup, `allow0`, borsh round trip)

Lane `v3-sched`. Facts about the previous `0x0f` state that let the AIR read it canonically:

* `indexOf_nodup` — on a duplicate-free shard id list, `indexOf` of the `i`-th id is `i`;
* `allow0_canon` / `allow0_canon_get` — when the previous state lists every link of the layout
  exactly once in sender-major order (record `l` = link `(ids[l / n], ids[l % n])`), the spec's
  `allow0` fold is the array of the records' allowances in order;
* `decode_encode` — `State.decode` inverts `State.encode` on in-range states.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-! ## `indexOf` on a duplicate-free list -/

theorem indexOf_go_nodup (s : Nat) :
    ∀ (ids : List Nat) (i k : Nat), ids.Nodup → (hi : i < ids.length) → ids[i] = s →
      indexOf.go s ids k = some (k + i)
  | [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | x :: xs, 0, k, _, _, hs => by
    simp only [List.getElem_cons_zero] at hs
    simp [indexOf.go, hs]
  | x :: xs, j + 1, k, hnd, hi, hs => by
    simp only [List.getElem_cons_succ] at hs
    have hj : j < xs.length := by simp at hi; omega
    have hx : x ≠ s := by
      intro h
      rw [List.nodup_cons] at hnd
      exact hnd.1 (h ▸ hs ▸ List.getElem_mem hj)
    simp only [indexOf.go, hx, ↓reduceIte]
    rw [indexOf_go_nodup s xs j (k + 1) (List.nodup_cons.mp hnd).2 hj hs]
    congr 1; omega

theorem indexOf_nodup {ids : List Nat} {i : Nat} (hnd : ids.Nodup) (hi : i < ids.length) :
    indexOf ids (ids.getD i 0) = some i := by
  have h := indexOf_go_nodup (ids.getD i 0) ids i 0 hnd hi (by simp [List.getD_eq_getElem?_getD, hi])
  simpa [indexOf] using h

/-! ## `allow0` of a canonical previous state -/

theorem foldl_congr_mem' {α β : Type} (f g : α → β → α) :
    ∀ (l : List β) (init : α), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: xs, init, h => by
    simp only [List.foldl_cons]
    rw [h x List.mem_cons_self init]
    exact foldl_congr_mem' f g xs _ (fun y hy acc => h y (List.mem_cons_of_mem _ hy) acc)

/-- The fold of `allow0` after the canonical records reduce to `set! l (a l)`. -/
theorem foldl_set_range (N : Nat) (a : Nat → Nat) :
    ∀ k, k ≤ N → (List.range k).foldl (fun (arr : Array Nat) l => arr.set! l (a l))
        (Array.replicate N 0) = Array.ofFn (n := N) fun l => if l.1 < k then a l else 0
  | 0, _ => by
    apply Array.ext
    · simp
    · intro i h1 h2; simp
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, foldl_set_range N a k (by omega)]
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [List.foldl_cons, List.foldl_nil, Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds (by simp at h2 ⊢; omega)]
      simp only [Array.getElem_ofFn]
      by_cases hik : k = i
      · subst hik; simp
      · simp only [hik, ↓reduceIte]
        by_cases hi : i < k
        · simp [hi, show i < k + 1 by omega]
        · simp [hi, show ¬ i < k + 1 by omega]

theorem allow0_canon (ids : List Nat) (hnd : ids.Nodup) (a : Nat → Nat) :
    let n := ids.length
    let links : List NearSpec.Bandwidth.LinkAllowance :=
      (List.range (n * n)).map fun l => ⟨ids.getD (l / n) 0, ids.getD (l % n) 0, a l⟩
    links.foldl (fun (arr : Array Nat) la =>
        match indexOf ids la.sender, indexOf ids la.receiver with
        | some s, some r => arr.set! (s * n + r) la.allowance
        | _, _ => arr) (Array.replicate (n * n) 0)
      = (List.range (n * n)).toArray.map a := by
  intro n links
  have hstep : ∀ l ∈ List.range (n * n), ∀ arr : Array Nat,
      (match indexOf ids (ids.getD (l / n) 0), indexOf ids (ids.getD (l % n) 0) with
        | some s, some r => arr.set! (s * n + r) (a l)
        | _, _ => arr) = arr.set! l (a l) := by
    intro l hl arr
    rw [List.mem_range] at hl
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at hl; simp at hl
      · exact h
    have hs : l / n < n := (Nat.div_lt_iff_lt_mul hn).2 hl
    have hr : l % n < n := Nat.mod_lt _ hn
    rw [indexOf_nodup hnd hs, indexOf_nodup hnd hr]
    simp only [Nat.div_add_mod']
  simp only [links, List.foldl_map]
  rw [foldl_congr_mem' _ (fun (arr : Array Nat) l => arr.set! l (a l)) _ _
    (fun l hl arr => hstep l hl arr)]
  rw [foldl_set_range (n * n) a (n * n) (Nat.le_refl _)]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp at h1
    simp

/-- Pointwise form of `allow0_canon`. -/
theorem allow0_canon_get (ids : List Nat) (hnd : ids.Nodup) (a : Nat → Nat) :
    let n := ids.length
    let links : List NearSpec.Bandwidth.LinkAllowance :=
      (List.range (n * n)).map fun l => ⟨ids.getD (l / n) 0, ids.getD (l % n) 0, a l⟩
    let arr := links.foldl (fun (arr : Array Nat) la =>
        match indexOf ids la.sender, indexOf ids la.receiver with
        | some s, some r => arr.set! (s * n + r) la.allowance
        | _, _ => arr) (Array.replicate (n * n) 0)
    arr.size = n * n ∧ ∀ l, l < n * n → arr[l]! = a l := by
  intro n links arr
  have h : arr = (List.range (n * n)).toArray.map a := allow0_canon ids hnd a
  rw [h]
  refine ⟨by simp, fun l hl => ?_⟩
  simp [hl]

/-! ## Borsh round trip of the scheduler state -/

theorem canon_leNat_leN (w x : Nat) (h : x < 256 ^ w) : leNat (leN w x) = x := by
  induction w generalizing x with
  | zero => simp at h; simp [leN, leNat, h]
  | succ w ih =>
    simp only [leN, leNat]
    have h' : x / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    rw [ih _ h']
    have : (UInt8.ofNat (x % 256)).toNat = x % 256 := by simp
    rw [this]; omega

theorem canon_leN_length (w x : Nat) : (leN w x).length = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih => simp [leN, ih]

theorem canon_takeN_append (a b : Bytes) : takeN a.length (a ++ b) = some (a, b) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [takeN, ih]

theorem canon_readLE_append (w x : Nat) (rest : Bytes) (h : x < 256 ^ w) :
    readLE w (leN w x ++ rest) = some (x, rest) := by
  have := canon_takeN_append (leN w x) rest
  rw [canon_leN_length] at this
  simp [readLE, this, canon_leNat_leN w x h]

theorem canon_readU64 (x : Nat) (rest : Bytes) (h : x < 2 ^ 64) :
    readU64 (u64 x ++ rest) = some (x, rest) :=
  canon_readLE_append 8 x rest (by simpa using h)

theorem canon_readU32 (x : Nat) (rest : Bytes) (h : x < 2 ^ 32) :
    readU32 (u32 x ++ rest) = some (x, rest) :=
  canon_readLE_append 4 x rest (by simpa using h)

/-- In-range link: every field fits in a `u64`. -/
def LinkOk (la : NearSpec.Bandwidth.LinkAllowance) : Prop :=
  la.sender < 2 ^ 64 ∧ la.receiver < 2 ^ 64 ∧ la.allowance < 2 ^ 64

theorem canon_readLink (la : NearSpec.Bandwidth.LinkAllowance) (h : LinkOk la) (rest : Bytes) :
    NearSpec.Bandwidth.readLink (la.encode ++ rest) = some (la, rest) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [NearSpec.Bandwidth.LinkAllowance.encode, List.append_assoc,
    NearSpec.Bandwidth.readLink, canon_readU64 _ _ h1, canon_readU64 _ _ h2, canon_readU64 _ _ h3]

theorem canon_readMany_links :
    ∀ (ls : List NearSpec.Bandwidth.LinkAllowance), (∀ la ∈ ls, LinkOk la) → ∀ rest : Bytes,
      readMany NearSpec.Bandwidth.readLink ls.length
        (concatAll (ls.map NearSpec.Bandwidth.LinkAllowance.encode) ++ rest) = some (ls, rest)
  | [], _, rest => rfl
  | la :: ls, h, rest => by
    simp only [List.length_cons, List.map_cons, concatAll, List.append_assoc, readMany,
      canon_readLink la (h la List.mem_cons_self),
      canon_readMany_links ls (fun x hx => h x (List.mem_cons_of_mem _ hx)) rest]

theorem decode_encode (st : NearSpec.Bandwidth.State)
    (hlinks : ∀ la ∈ st.links, la.sender < 2 ^ 64 ∧ la.receiver < 2 ^ 64 ∧ la.allowance < 2 ^ 64)
    (hhash : st.sanityHash.length = 32) (hlen : st.links.length < 2 ^ 32) :
    NearSpec.Bandwidth.State.decode st.encode = some st := by
  obtain ⟨links, h⟩ := st
  simp only at hlinks hhash hlen
  have h0 : ∀ rest : Bytes, readU8 ([0] ++ rest) = some (0, rest) := by
    intro rest; simp [readU8, readLE, takeN, leNat]
  simp only [NearSpec.Bandwidth.State.encode, NearSpec.Bandwidth.State.decode, List.append_assoc]
  rw [h0]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, canon_readU32 _ _ hlen,
    canon_readMany_links links hlinks]
  have hh : readHash h = some (h, []) := by
    have := canon_takeN_append h []
    rw [hhash, List.append_nil] at this
    exact this
  simp [hh]

end ZkFormal.NearV3.Sched
