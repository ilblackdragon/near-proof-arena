import ZkFormal.NearV3.Rcpt.Render.Srcp.Gen

namespace ZkFormal.NearV3.Render.SrcpGen

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra

private theorem map_getD {α β : Type} (d : α) (f : α → β) (xs : List α) :
    (List.range xs.length).map (fun i => f (xs.getD i d)) = xs.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < xs.length by simpa using h1)]

private theorem sum_const (xs : List Nat) (v : Nat) :
    (xs.map (fun _ => v)).sum = xs.length * v := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem kinds_length (B : SrcpB) : (kinds B).length = 33 + 64 * B.path.length := by
  simp only [kinds, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_range, List.length_flatMap]
  rw [sum_const, List.length_range]
  omega

/-- The renderer uses exactly the semantic row budget, with no spare-row demand. -/
theorem R_eq (bs : List SrcpB) : R bs = srcpRows bs := by
  simp only [R, recs, List.length_flatMap, List.length_map, kinds_length]
  exact congrArg List.sum (map_getD default (fun B : SrcpB => 33 + 64 * B.path.length) bs)

theorem R_pos {bs : List SrcpB} (h : SrcpWf bs) : 0 < R bs := by
  rw [R_eq]
  cases bs with
  | nil => exact False.elim (h.nonempty rfl)
  | cons b bs => simp [srcpRows]; omega

theorem rows_size (bs : List SrcpB) : (rows bs).size = 2 ^ logOf (R bs) := by
  exact mkTab_size _ _ _

theorem rows_log_bound {bs : List SrcpB} (h : SrcpWf bs) :
    logOf (R bs) ≤ SrcpV3.maxLog := by
  apply logOf_le (by decide)
  simpa [R_eq] using h.rows

theorem rows_capacity (bs : List SrcpB) : R bs ≤ (rows bs).size := by
  rw [rows_size]
  exact le_pow_logOf _

/-- Every source leaf starts at a positive message index. -/
theorem ql_pos {bs : List SrcpB} (h : SrcpWf bs) (i : Nat) (hi : i < bs.length) :
    0 < bs[i].ql := by
  cases i with
  | zero => rw [h.q0 hi]; omega
  | succ i => rw [h.qnext i hi]; omega

/-- Root counter subtraction is exact on every well-formed block. -/
theorem root_q_succ {bs : List SrcpB} (h : SrcpWf bs)
    (i : Nat) (hi : i < bs.length) (z : Nat) :
    (rootFrame bs[i] z).q + 1 = bs[i].ql := by
  have := ql_pos h i hi
  simp only [rootFrame]
  omega

/-- The descriptors expose the precise legal coordinate ranges. -/
theorem mem_kinds (B : SrcpB) (k : Kind) : k ∈ kinds B ↔
    k = .root ∨ (∃ p, p < 32 ∧ k = .leaf p) ∨
      (∃ i o, i < B.path.length ∧ o < 64 ∧ k = .path i o) := by
  simp only [kinds, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ((h | ⟨p, hp, he⟩) | ⟨i, hi, o, ho, he⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨p, hp, he.symm⟩)
    · exact Or.inr (Or.inr ⟨i, o, hi, ho, he.symm⟩)
  · rintro (h | ⟨p, hp, he⟩ | ⟨i, o, hi, ho, he⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨p, hp, he.symm⟩)
    · exact Or.inr ⟨i, hi, o, ho, he.symm⟩

theorem mem_recs {bs : List SrcpB} {r : Nat × Kind} (h : r ∈ recs bs) :
    r.1 < bs.length ∧ r.2 ∈ kinds (bs.getD r.1 default) := by
  simp only [recs, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨i, hi, k, hk, he⟩ := h
  subst r
  exact ⟨hi, hk⟩

theorem rows_get {bs : List SrcpB} {r x : Nat}
    (hr : r < 2 ^ logOf (R bs)) (hx : x < SrcpV3.width) :
    ((rows bs).getD r #[]).getD x 0 = cell bs r x :=
  mkTab_get hr hx

theorem padding_cell {bs : List SrcpB} {r x : Nat} (hr : R bs ≤ r) :
    cell bs r x = if x = SrcpV3.sz then srcpSize bs else 0 := by
  simp [cell, Nat.not_lt.mpr hr]

theorem leaf_registers (B : SrcpB) (z p x : Nat) :
    (leafFrame B z p).regs.getD x 0 = B.leaf.getD (p + x) 0 := by
  simp [leafFrame]

theorem path_registers (B : SrcpB) (z i o x : Nat) :
    (pathFrame B z i o).regs.getD x 0 =
      (B.path.getD i default).acc.getD (o % 32 + x) 0 := by
  simp [pathFrame]

end ZkFormal.NearV3.Render.SrcpGen
