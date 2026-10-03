import ReexecNpai.Spec.RecAux16

/-!
# Record parse: branch combinatorics (bitmaps, slot lists, `mkKids`, `popN`)
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-- Bit `i` of `x`. -/
def bitOf (x i : Nat) : Nat := x / 2 ^ i % 2

theorem bitOf_zero (x : Nat) : bitOf x 0 = x % 2 := by simp [bitOf]

theorem bitOf_succ (x i : Nat) : bitOf x (i + 1) = bitOf (x / 2) i := by
  simp only [bitOf, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem bitOf_lt (x i : Nat) : bitOf x i < 2 := Nat.mod_lt _ (by omega)

theorem popc_succ (n x : Nat) : popc (n + 1) x = x % 2 + popc n (x / 2) := rfl

theorem popc_le : ∀ n x, popc n x ≤ n
  | 0, _ => Nat.le_refl _
  | n + 1, x => by rw [popc_succ]; have := popc_le n (x / 2); have : x % 2 < 2 := Nat.mod_lt _ (by omega); omega

/-- The 16 child slots from the bitmaps and the present-slot hashes. -/
def ksOf : Nat → Nat → Nat → List Bytes → List (Option (Option Bytes))
  | 0, _, _, _ => []
  | n + 1, bm, ex, hs =>
    if bm % 2 = 1 then
      (if ex % 2 = 1 then some none else some (some (hs.headD []))) :: ksOf n (bm / 2) (ex / 2) hs.tail
    else none :: ksOf n (bm / 2) (ex / 2) hs

theorem ksOf_length : ∀ n bm ex hs, (ksOf n bm ex hs).length = n
  | 0, _, _, _ => rfl
  | n + 1, bm, ex, hs => by
    simp only [ksOf]; split <;> simp [ksOf_length n]

/-- `ex ⊆ bm` on the low `n` bits. -/
def SubB (n bm ex : Nat) : Prop := ∀ i, i < n → bitOf ex i = 1 → bitOf bm i = 1

/-- Revealed slots hold zeros. -/
def ZeroB (n bm ex : Nat) (hs : List Bytes) : Prop :=
  ∀ i, i < n → bitOf bm i = 1 → bitOf ex i = 1 → hs.getD (popc i bm) [] = zeros 32

theorem SubB_succ (n bm ex : Nat) : SubB (n + 1) bm ex ↔ (ex % 2 = 1 → bm % 2 = 1) ∧ SubB n (bm / 2) (ex / 2) := by
  constructor
  · intro h
    refine ⟨fun h1 => ?_, fun i hi h1 => ?_⟩
    · have := h 0 (by omega) (by rw [bitOf_zero]; exact h1); rwa [bitOf_zero] at this
    · have := h (i + 1) (by omega) (by rw [bitOf_succ]; exact h1); rwa [bitOf_succ] at this
  · rintro ⟨h0, h⟩ i hi h1
    cases i with
    | zero => rw [bitOf_zero] at h1 ⊢; exact h0 h1
    | succ i => rw [bitOf_succ] at h1 ⊢; exact h i (by omega) h1

theorem getD_tail {α : Type} (l : List α) (k : Nat) (d : α) : l.tail.getD k d = l.getD (k + 1) d := by
  cases l <;> simp

theorem ZeroB_succ (n bm ex : Nat) (hs : List Bytes) :
    ZeroB (n + 1) bm ex hs ↔ (bm % 2 = 1 → ex % 2 = 1 → hs.headD [] = zeros 32) ∧
      ZeroB n (bm / 2) (ex / 2) (if bm % 2 = 1 then hs.tail else hs) := by
  have hb : bm % 2 < 2 := Nat.mod_lt _ (by omega)
  have hidx : ∀ i, hs.getD (popc (i + 1) bm) [] = (if bm % 2 = 1 then hs.tail else hs).getD (popc i (bm / 2)) [] := by
    intro i
    rw [popc_succ]
    split
    · rename_i h1; rw [h1, getD_tail, Nat.add_comm]
    · rename_i h1; rw [show bm % 2 = 0 by omega, Nat.zero_add]
  have h0 : hs.getD (popc 0 bm) [] = hs.headD [] := by cases hs <;> rfl
  constructor
  · intro h
    refine ⟨fun h1 h2 => ?_, fun i hi h1 h2 => ?_⟩
    · have := h 0 (by omega) (by rw [bitOf_zero]; exact h1) (by rw [bitOf_zero]; exact h2)
      rwa [h0] at this
    · have := h (i + 1) (by omega) (by rw [bitOf_succ]; exact h1) (by rw [bitOf_succ]; exact h2)
      rwa [hidx] at this
  · rintro ⟨hz, h⟩ i hi h1 h2
    cases i with
    | zero => rw [bitOf_zero] at h1 h2; rw [h0]; exact hz h1 h2
    | succ i => rw [bitOf_succ] at h1 h2; rw [hidx]; exact h i (by omega) h1 h2

/-- Decoder direction: what `mkKids` success means. -/
theorem mkKids_some : ∀ (n bm ex : Nat) (hs : List Bytes) (cs pre : List PTrie) (k : Kids),
    mkKids n bm ex hs cs = some k →
    SubB n bm ex ∧ ZeroB n bm ex hs ∧ hs.length = popc n bm ∧ cs.length = popc n ex ∧
      k = kidsOf (fun q => (pre ++ cs).getD q (.hash [])) (ksOf n bm ex hs) pre.length
  | 0, bm, ex, hs, cs, pre, k, h => by
    match hs, cs, h with
    | [], [], h =>
      simp only [mkKids, Option.some.injEq] at h
      subst h
      exact ⟨fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega), rfl, rfl, rfl⟩
  | n + 1, bm, ex, hs, cs, pre, k, h => by
    have hb : bm % 2 < 2 := Nat.mod_lt _ (by omega)
    have he : ex % 2 < 2 := Nat.mod_lt _ (by omega)
    simp only [mkKids] at h
    split at h
    · rename_i hb1
      match hs, h with
      | [], h => simp at h
      | hh :: hs', h =>
      simp only at h
      split at h
      · rename_i he1
        split at h
        · simp at h
        rename_i hz
        match cs, h with
        | [], h => simp at h
        | c :: cs', h =>
        simp only at h
        cases hk : mkKids n (bm / 2) (ex / 2) hs' cs' with
        | none => rw [hk] at h; simp at h
        | some k' =>
        rw [hk] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨s1, z1, l1, l2, e1⟩ := mkKids_some n (bm / 2) (ex / 2) hs' cs' (pre ++ [c]) k' hk
        refine ⟨(SubB_succ _ _ _).mpr ⟨fun _ => hb1, s1⟩,
          (ZeroB_succ _ _ _ _).mpr ⟨fun _ _ => by simpa using hz, by simpa [hb1] using z1⟩,
          by simp [popc_succ, hb1, l1]; omega, by simp [popc_succ, he1, l2]; omega, ?_⟩
        simp only [ksOf, hb1, he1, ↓reduceIte, kidsOf, List.tail_cons]
        rw [e1]
        simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
        congr 1
        simp
      · rename_i he1
        cases hk : mkKids n (bm / 2) (ex / 2) hs' cs with
        | none => rw [hk] at h; simp at h
        | some k' =>
        rw [hk] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨s1, z1, l1, l2, e1⟩ := mkKids_some n (bm / 2) (ex / 2) hs' cs pre k' hk
        refine ⟨(SubB_succ _ _ _).mpr ⟨fun h' => absurd h' he1, s1⟩,
          (ZeroB_succ _ _ _ _).mpr ⟨fun _ h' => absurd h' he1, by simpa [hb1] using z1⟩,
          by simp [popc_succ, hb1, l1]; omega, by simp [popc_succ, l2]; omega, ?_⟩
        simp only [ksOf, hb1, he1, ↓reduceIte, kidsOf, List.tail_cons, List.headD_cons]
        rw [e1]
    · rename_i hb1
      split at h
      · simp at h
      rename_i he1
      cases hk : mkKids n (bm / 2) (ex / 2) hs cs with
      | none => rw [hk] at h; simp at h
      | some k' =>
      rw [hk] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨s1, z1, l1, l2, e1⟩ := mkKids_some n (bm / 2) (ex / 2) hs cs pre k' hk
      refine ⟨(SubB_succ _ _ _).mpr ⟨fun h' => absurd h' he1, s1⟩,
        (ZeroB_succ _ _ _ _).mpr ⟨fun h' => absurd h' hb1, by simpa [hb1] using z1⟩,
        by simp [popc_succ, l1]; omega, by simp [popc_succ, l2]; omega, ?_⟩
      simp only [ksOf, hb1, ↓reduceIte, kidsOf]
      rw [e1]

/-- Encoder direction: `mkKids` succeeds on well-formed input. -/
theorem mkKids_of : ∀ (n bm ex : Nat) (hs : List Bytes) (cs pre : List PTrie),
    hs.length = popc n bm → SubB n bm ex → ZeroB n bm ex hs → cs.length = popc n ex →
    mkKids n bm ex hs cs = some (kidsOf (fun q => (pre ++ cs).getD q (.hash [])) (ksOf n bm ex hs) pre.length)
  | 0, bm, ex, hs, cs, pre, hl, _, _, hc => by
    simp only [popc, List.length_eq_zero_iff] at hl hc
    subst hl hc; rfl
  | n + 1, bm, ex, hs, cs, pre, hl, hsub, hz, hc => by
    have hb : bm % 2 < 2 := Nat.mod_lt _ (by omega)
    have he : ex % 2 < 2 := Nat.mod_lt _ (by omega)
    obtain ⟨s0, s1⟩ := (SubB_succ _ _ _).mp hsub
    obtain ⟨z0, z1⟩ := (ZeroB_succ _ _ _ _).mp hz
    rw [popc_succ] at hl hc
    simp only [mkKids]
    by_cases hb1 : bm % 2 = 1
    · rw [if_pos hb1]
      match hs, hl with
      | [], hl => simp at hl; omega
      | hh :: hs', hl =>
      simp only [List.length_cons] at hl
      simp only [hb1, ↓reduceIte, List.tail_cons] at z1
      simp only
      by_cases he1 : ex % 2 = 1
      · rw [if_pos he1, if_neg (by simpa using z0 hb1 he1)]
        match cs, hc with
        | [], hc => simp at hc; omega
        | c :: cs', hc =>
        simp only [List.length_cons] at hc
        simp only
        rw [mkKids_of n (bm / 2) (ex / 2) hs' cs' (pre ++ [c]) (by omega) s1 z1 (by omega)]
        simp only [Option.map_some, ksOf, hb1, he1, ↓reduceIte, kidsOf, List.tail_cons, List.append_assoc,
          List.singleton_append, List.length_append, List.length_singleton, Option.some.injEq]
        congr 1
        simp
      · rw [if_neg he1, mkKids_of n (bm / 2) (ex / 2) hs' cs pre (by omega) s1 z1 (by omega)]
        simp [ksOf, hb1, he1, kidsOf]
    · rw [if_neg hb1, if_neg (fun h1 => hb1 (s0 h1))]
      simp only [hb1, ↓reduceIte] at z1
      have he1 : ex % 2 = 0 := by have := fun h1 => hb1 (s0 h1); omega
      rw [mkKids_of n (bm / 2) (ex / 2) hs cs pre (by omega) s1 z1 (by omega)]
      simp [ksOf, hb1, kidsOf]

theorem nRev_ksOf : ∀ (n bm ex : Nat) (hs : List Bytes), SubB n bm ex → nRev (ksOf n bm ex hs) = popc n ex
  | 0, _, _, _, _ => rfl
  | n + 1, bm, ex, hs, hsub => by
    obtain ⟨s0, s1⟩ := (SubB_succ _ _ _).mp hsub
    have he : ex % 2 < 2 := Nat.mod_lt _ (by omega)
    rw [popc_succ]
    simp only [ksOf]
    split
    · split
      · rename_i h1 h2; rw [nRev_cons, nRev_ksOf n _ _ _ s1, h2]; simp; omega
      · rename_i h1 h2; rw [nRev_cons, nRev_ksOf n _ _ _ s1]; simp; omega
    · rename_i h1
      have : ex % 2 = 0 := by have := fun h => h1 (s0 h); omega
      rw [nRev_cons, nRev_ksOf n _ _ _ s1, this]; simp

theorem bitsPres_ksOf : ∀ (n bm ex : Nat) (hs : List Bytes) (i : Nat),
    bitsPres (ksOf n bm ex hs) i = 2 ^ i * (bm % 2 ^ n)
  | 0, _, _, _, i => by simp [ksOf, bitsPres, Nat.mod_one]
  | n + 1, bm, ex, hs, i => by
    have hm : bm % 2 ^ (n + 1) = bm % 2 + 2 * (bm / 2 % 2 ^ n) := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul, Nat.add_comm]
    simp only [ksOf]
    split
    · rename_i h1
      split <;> (simp only [bitsPres]; rw [bitsPres_ksOf n, hm, h1, Nat.pow_succ]; simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_zero, Nat.add_zero, Nat.zero_add])
    · rename_i h1
      simp only [bitsPres]; rw [bitsPres_ksOf n, hm, show bm % 2 = 0 by omega, Nat.pow_succ]; simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_zero, Nat.add_zero, Nat.zero_add]

theorem bitsRev_ksOf : ∀ (n bm ex : Nat) (hs : List Bytes) (i : Nat), SubB n bm ex →
    bitsRev (ksOf n bm ex hs) i = 2 ^ i * (ex % 2 ^ n)
  | 0, _, _, _, i, _ => by simp [ksOf, bitsRev, Nat.mod_one]
  | n + 1, bm, ex, hs, i, hsub => by
    obtain ⟨s0, s1⟩ := (SubB_succ _ _ _).mp hsub
    have hm : ex % 2 ^ (n + 1) = ex % 2 + 2 * (ex / 2 % 2 ^ n) := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul, Nat.add_comm]
    simp only [ksOf]
    split
    · split
      · rename_i h1 h2
        simp only [bitsRev]; rw [bitsRev_ksOf n _ _ _ _ s1, hm, h2, Nat.pow_succ]; simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      · rename_i h1 h2
        simp only [bitsRev]; rw [bitsRev_ksOf n _ _ _ _ s1, hm, show ex % 2 = 0 by omega, Nat.pow_succ]; simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    · rename_i h1
      have : ex % 2 = 0 := by have := fun h => h1 (s0 h); omega
      simp only [bitsRev]; rw [bitsRev_ksOf n _ _ _ _ s1, hm, this, Nat.pow_succ]; simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_zero, Nat.add_zero, Nat.zero_add]

theorem slotBytes_ksOf : ∀ (n bm ex : Nat) (hs : List Bytes), hs.length = popc n bm → SubB n bm ex →
    ZeroB n bm ex hs → slotBytes (ksOf n bm ex hs) (List.replicate (popc n ex) (zeros 32)) = hs.flatten
  | 0, _, _, hs, hl, _, _ => by
    simp only [popc, List.length_eq_zero_iff] at hl; subst hl; rfl
  | n + 1, bm, ex, hs, hl, hsub, hz => by
    have hb : bm % 2 < 2 := Nat.mod_lt _ (by omega)
    have he : ex % 2 < 2 := Nat.mod_lt _ (by omega)
    obtain ⟨s0, s1⟩ := (SubB_succ _ _ _).mp hsub
    obtain ⟨z0, z1⟩ := (ZeroB_succ _ _ _ _).mp hz
    rw [popc_succ] at hl ⊢
    by_cases hb1 : bm % 2 = 1
    · match hs, hl with
      | [], hl => simp at hl; omega
      | hh :: hs', hl =>
      simp only [List.length_cons] at hl
      simp only [hb1, ↓reduceIte, List.tail_cons] at z1
      by_cases he1 : ex % 2 = 1
      · have := z0 hb1 he1
        simp only [List.headD_cons] at this
        simp only [ksOf, hb1, he1, ↓reduceIte, List.tail_cons, slotBytes, List.flatten_cons, this]
        rw [show 1 + popc n (ex / 2) = popc n (ex / 2) + 1 by omega, List.replicate_succ]
        simp only [List.headD_cons, List.tail_cons]
        rw [slotBytes_ksOf n _ _ _ (by omega) s1 z1]
      · simp only [ksOf, hb1, he1, ↓reduceIte, List.tail_cons, List.headD_cons, slotBytes, List.flatten_cons]
        rw [show ex % 2 = 0 by omega, Nat.zero_add, slotBytes_ksOf n _ _ _ (by omega) s1 z1]
    · have he1 : ex % 2 = 0 := by have := fun h => hb1 (s0 h); omega
      simp only [hb1, ↓reduceIte] at z1
      simp only [ksOf, hb1, ↓reduceIte, slotBytes]
      rw [he1, Nat.zero_add, slotBytes_ksOf n _ _ _ (by omega) s1 z1]

theorem slotPos_ksOf : ∀ (n bm ex : Nat) (hs : List Bytes) (i : Nat), SubB n bm ex → i < n → bitOf ex i = 1 →
    slotPos (ksOf n bm ex hs) (popc i ex) = popc i bm
  | 0, _, _, _, i, _, hi, _ => absurd hi (by omega)
  | n + 1, bm, ex, hs, i, hsub, hi, hbit => by
    have hb : bm % 2 < 2 := Nat.mod_lt _ (by omega)
    have he : ex % 2 < 2 := Nat.mod_lt _ (by omega)
    obtain ⟨s0, s1⟩ := (SubB_succ _ _ _).mp hsub
    cases i with
    | zero =>
      rw [bitOf_zero] at hbit
      simp only [popc, ksOf, s0 hbit, hbit, ↓reduceIte, slotPos]
    | succ i =>
      rw [bitOf_succ] at hbit
      rw [popc_succ, popc_succ]
      have ih := slotPos_ksOf n (bm / 2) (ex / 2) (if bm % 2 = 1 then hs.tail else hs) i s1 (by omega) hbit
      by_cases hb1 : bm % 2 = 1
      · simp only [hb1, ↓reduceIte] at ih
        by_cases he1 : ex % 2 = 1
        · simp only [ksOf, hb1, he1, ↓reduceIte]
          rw [Nat.add_comm 1 (popc i (ex / 2)), slotPos, ih]; try omega
        · simp only [ksOf, hb1, he1, ↓reduceIte]
          rw [show ex % 2 = 0 by omega, Nat.zero_add, slotPos, ih]; try omega
      · have he1 : ex % 2 = 0 := by have := fun h => hb1 (s0 h); omega
        simp only [hb1, ↓reduceIte] at ih
        simp only [ksOf, hb1, ↓reduceIte, he1, Nat.zero_add, slotPos, ih]
        omega

theorem ksOf_hashes : ∀ (n bm ex : Nat) (hs : List Bytes), hs.length = popc n bm → (∀ h ∈ hs, h.length = 32) →
    ∀ s ∈ ksOf n bm ex hs, (match s with | some (some h) => h.length = 32 | _ => True)
  | 0, _, _, _, _, _ => by simp [ksOf]
  | n + 1, bm, ex, hs, hl, h32 => by
    have hb : bm % 2 < 2 := Nat.mod_lt _ (by omega)
    rw [popc_succ] at hl
    intro s hsm
    simp only [ksOf] at hsm
    split at hsm
    · rename_i hb1
      match hs, hl with
      | [], hl => simp at hl; omega
      | hh :: hs', hl =>
      simp only [List.length_cons, List.tail_cons, List.headD_cons] at hl hsm
      rcases List.mem_cons.mp hsm with rfl | hm
      · by_cases he1 : ex % 2 = 1 <;> simp [he1, h32 hh (by simp)]
      · exact ksOf_hashes n _ _ hs' (by omega) (fun h hm' => h32 h (List.mem_cons_of_mem _ hm')) s hm
    · rename_i hb1
      rcases List.mem_cons.mp hsm with rfl | hm
      · trivial
      · exact ksOf_hashes n _ _ hs (by omega) h32 s hm

/-! ## `chunks32` -/

theorem chunks32_length : ∀ k bs, (chunks32 k bs).length = k
  | 0, _ => rfl
  | k + 1, bs => by simp [chunks32, chunks32_length k]

theorem chunks32_mem : ∀ k (bs : Bytes), 32 * k ≤ bs.length → ∀ c ∈ chunks32 k bs, c.length = 32
  | 0, _, _ => by simp [chunks32]
  | k + 1, bs, h => by
    intro c hc
    simp only [chunks32, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp; omega
    · exact chunks32_mem k _ (by simp; omega) c hc

theorem chunks32_flatten : ∀ k (bs : Bytes), bs.length = 32 * k → (chunks32 k bs).flatten = bs
  | 0, bs, h => by simp at h; simp [chunks32, h]
  | k + 1, bs, h => by
    simp only [chunks32, List.flatten_cons]
    rw [chunks32_flatten k _ (by simp; omega), List.take_append_drop]

theorem chunks32_getD : ∀ k (bs : Bytes) j, j < k → (chunks32 k bs).getD j [] = (bs.drop (32 * j)).take 32
  | 0, _, _, h => absurd h (by omega)
  | k + 1, bs, 0, _ => by simp [chunks32]
  | k + 1, bs, j + 1, h => by
    simp only [chunks32, List.getD_cons_succ]
    rw [chunks32_getD k _ j (by omega), List.drop_drop]
    congr 2; omega

/-! ## `popN` -/

theorem popN_rev (L stk : List PTrie) : popN L.length (L.reverse ++ stk) = some (L, stk) := by
  have := popN_append L.reverse stk
  simpa using this

theorem popN_some : ∀ (n : Nat) (stk cs stk' : List PTrie), popN n stk = some (cs, stk') →
    cs.length = n ∧ stk = cs.reverse ++ stk'
  | 0, stk, cs, stk', h => by
    simp only [popN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | n + 1, [], cs, stk', h => by simp [popN] at h
  | n + 1, x :: stk, cs, stk', h => by
    simp only [popN] at h
    cases hp : popN n stk with
    | none => rw [hp] at h; simp at h
    | some y =>
      obtain ⟨cs', r⟩ := y
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := popN_some n stk cs' r hp
      simp [h1, h2]

end ReexecNpai
