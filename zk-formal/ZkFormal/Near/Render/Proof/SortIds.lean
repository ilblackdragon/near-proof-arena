import ZkFormal.Near.Render.Proof.Base

/-!
# ZkFormal.Near.Render.Proof.SortIds — the sorted receipt ids of a `Good` batch

`IdsOk (sortedIds I)`: between 1 and 256 ids, each 32 bytes, strictly
increasing as little-endian integers (from `Good.nodup`); and the byte-serial
carry facts of `SortGen`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- What the sort table needs about its ids. -/
structure IdsOk (S : List (Nat × List Nat)) : Prop where
  len_pos : 1 ≤ S.length
  len_le : S.length ≤ 256
  mem : ∀ x ∈ S, x.2.length = 32 ∧ ∀ b ∈ x.2, b < 256
  strict : S.Pairwise fun a b => leVal a.2 < leVal b.2

/-! ## insertion sort -/

theorem perm_insertSorted (x : Nat × List Nat) :
    ∀ l : List (Nat × List Nat), (insertSorted x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    simp only [insertSorted]
    split
    · exact List.Perm.refl _
    · exact ((perm_insertSorted x ys).cons y).trans (List.Perm.swap x y ys)

theorem perm_sorted : ∀ l : List (Nat × List Nat), (l.foldr insertSorted []).Perm l
  | [] => List.Perm.refl _
  | x :: l => by
    simp only [List.foldr_cons]
    exact (perm_insertSorted x _).trans ((perm_sorted l).cons x)

theorem pairwise_insertSorted (x : Nat × List Nat) :
    ∀ l : List (Nat × List Nat), l.Pairwise (fun a b => leVal a.2 ≤ leVal b.2) →
      (insertSorted x l).Pairwise (fun a b => leVal a.2 ≤ leVal b.2)
  | [], _ => by simp [insertSorted]
  | y :: ys, h => by
    simp only [insertSorted]
    rw [List.pairwise_cons] at h
    split
    · rename_i hxy
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 h⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy
      · exact Nat.le_trans hxy (h.1 z hz)
    · rename_i hxy
      refine List.pairwise_cons.2 ⟨?_, pairwise_insertSorted x ys h.2⟩
      intro z hz
      rcases List.mem_cons.1 ((perm_insertSorted x ys).mem_iff.1 hz) with rfl | hz
      · omega
      · exact h.1 z hz

theorem pairwise_sorted : ∀ l : List (Nat × List Nat),
    (l.foldr insertSorted []).Pairwise (fun a b => leVal a.2 ≤ leVal b.2)
  | [] => List.Pairwise.nil
  | x :: l => pairwise_insertSorted x _ (pairwise_sorted l)

/-! ## little-endian values -/

theorem leVal_toNats (b : Bytes) : leVal (toNats b) = leNat b := by
  induction b with
  | nil => rfl
  | cons x b ih => simp only [toNats, List.map_cons, leVal, List.foldr_cons, leNat] at ih ⊢; rw [ih]

theorem leNat_inj : ∀ (a b : Bytes), a.length = b.length → leNat a = leNat b → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    simp only [leNat] at h
    have hx := x.toNat_lt; have hy := y.toNat_lt
    have h1 : x.toNat = y.toNat := by omega
    have h2 : leNat a = leNat b := by omega
    rw [UInt8.toNat_inj.1 h1, leNat_inj a b (by simpa using hl) h2]

theorem leVal_lt : ∀ (l : List Nat), (∀ b ∈ l, b < 256) → leVal l < 256 ^ l.length
  | [], _ => by simp [leVal]
  | x :: l, h => by
    have hx := h x (by simp)
    have ih := leVal_lt l (fun b hb => h b (by simp [hb]))
    simp only [leVal, List.foldr_cons, List.length_cons, Nat.pow_succ] at ih ⊢
    have : 256 * (List.foldr (fun x acc => x + 256 * acc) 0 l) + 256 ≤ 256 ^ l.length * 256 := by
      rw [Nat.mul_comm (256 ^ l.length)]; exact Nat.mul_le_mul_left 256 ih
    omega

/-! ## the ids of a `Good` batch -/

section
variable {c : Claim} {e : Ext}

theorem rawIds_len : (rawIds (mkInfo c e)).length = e.rs.length := by
  simp [rawIds, mkInfo_e]

theorem rawIds_mem {x : Nat × List Nat} (h : x ∈ rawIds (mkInfo c e)) :
    ∃ rc ∈ e.rs, x.2 = toNats rc.receiptId := by
  simp only [rawIds, mkInfo_e, List.mem_map] at h
  obtain ⟨⟨rc, r⟩, hm, rfl⟩ := h
  exact ⟨rc, List.of_mem_zip hm |>.1, rfl⟩

theorem rawIds_vals : (rawIds (mkInfo c e)).map (fun x => leVal x.2) = e.rs.map fun rc => leNat rc.receiptId := by
  simp only [rawIds, mkInfo_e, List.map_map]
  have : (e.rs.zip (List.range e.rs.length)).map Prod.fst = e.rs := List.map_fst_zip (by simp)
  conv => rhs; rw [← this]
  simp only [List.map_map]
  congr 1; funext p; simp [leVal_toNats]

theorem id_len (hg : Good c e) {rc : Receipt} (h : rc ∈ e.rs) : rc.receiptId.length = 32 := by
  have := List.all_eq_true.1 hg.inSlice rc h
  simp only [Receipt.inSlice, Receipt.wf, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1.1.1.2

theorem idsOk (hg : Good c e) : IdsOk (sortedIds (mkInfo c e)) := by
  have hp := perm_sorted (rawIds (mkInfo c e))
  have hlen : (sortedIds (mkInfo c e)).length = e.rs.length := by
    rw [sortedIds, hp.length_eq, rawIds_len]
  refine ⟨by rw [hlen, hg.len]; exact hg.n_pos, by rw [hlen, hg.len]; exact hg.n_le, ?_, ?_⟩
  · intro x hx
    obtain ⟨rc, hrc, hx2⟩ := rawIds_mem (hp.mem_iff.1 hx)
    rw [hx2]
    refine ⟨by simp [toNats, id_len hg hrc], fun b hb => ?_⟩
    simp only [toNats, List.mem_map] at hb
    obtain ⟨u, _, rfl⟩ := hb
    exact u.toNat_lt
  · -- distinct values
    have hnd : ((rawIds (mkInfo c e)).map fun x => leVal x.2).Nodup := by
      rw [rawIds_vals]
      have h0 := hg.nodup
      unfold List.Nodup at h0 ⊢
      rw [List.pairwise_map] at h0 ⊢
      refine h0.imp_of_mem (fun ha hb hne heq => hne ?_)
      exact leNat_inj _ _ (by rw [id_len hg ha, id_len hg hb]) heq
    have hnd' := (hp.map (fun x => leVal x.2)).nodup_iff.2 hnd
    unfold List.Nodup at hnd'
    rw [List.pairwise_map] at hnd'
    exact (pairwise_sorted _).imp₂ (fun a b h1 h2 => Nat.lt_of_le_of_ne h1 h2) hnd'

end

/-! ## byte-serial addition -/

namespace SortGen

theorem byte_succ (x i : Nat) : byte x (i + 1) = byte (x / 256) i := by
  simp only [byte, Nat.pow_succ', Nat.div_div_eq_div_mul]

theorem byte_lt (x i : Nat) : byte x i < 256 := Nat.mod_lt _ (by omega)

/-- **Byte `i` of `x + y + c`.** -/
theorem carry_step : ∀ (i x y c : Nat),
    byte (x + y + c) i + 256 * carryFrom x y c (i + 1) = byte x i + byte y i + carryFrom x y c i
  | 0, x, y, c => by simp only [byte, carryFrom, Nat.pow_zero, Nat.div_one]; omega
  | i + 1, x, y, c => by
    have h := carry_step i (x / 256) (y / 256) ((x % 256 + y % 256 + c) / 256)
    have hz : (x + y + c) / 256 = x / 256 + y / 256 + (x % 256 + y % 256 + c) / 256 := by omega
    rw [byte_succ, byte_succ, byte_succ, hz]
    exact h

theorem carry_le : ∀ (i x y c : Nat), c ≤ 1 → carryFrom x y c i ≤ 1
  | 0, _, _, _, h => h
  | i + 1, x, y, c, h => carry_le i _ _ _ (by omega)

theorem carry_top : ∀ (i x y c : Nat), x + y + c < 256 ^ i → carryFrom x y c i = 0
  | 0, x, y, c, h => by simp at h; simp [carryFrom]; omega
  | i + 1, x, y, c, h => by
    apply carry_top i
    rw [Nat.pow_succ] at h
    have : (x + y + c) / 256 < 256 ^ i := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    omega

theorem byte_leVal : ∀ (l : List Nat) (i : Nat), (∀ b ∈ l, b < 256) → byte (leVal l) i = l.getD i 0
  | [], i, _ => by simp [leVal, byte]
  | x :: l, 0, h => by
    have := h x (by simp)
    simp only [leVal, List.foldr_cons, byte, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]; omega
  | x :: l, i + 1, h => by
    have := h x (by simp)
    rw [byte_succ, List.getD_cons_succ, ← byte_leVal l i (fun b hb => h b (by simp [hb]))]
    simp only [leVal, List.foldr_cons]
    congr 1; omega

/-- The 8 bits of a byte. -/
theorem bits8 (b : Nat) (h : b < 256) :
    b / 2 ^ 0 % 2 + 2 * (b / 2 ^ 1 % 2) + 4 * (b / 2 ^ 2 % 2) + 8 * (b / 2 ^ 3 % 2) +
      16 * (b / 2 ^ 4 % 2) + 32 * (b / 2 ^ 5 % 2) + 64 * (b / 2 ^ 6 % 2) + 128 * (b / 2 ^ 7 % 2) = b := by
  simp only [Nat.reducePow]; omega

end SortGen

end ZkFormal.Near.Render
