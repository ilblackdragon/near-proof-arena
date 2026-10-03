import ZkFormal.Algebra.Statements

/-!
# ZkFormal.Algebra.DecodeCount — fiber bounds for the challenge decoders

`decodeChal_count`: every element of `K` has at most `3^8` preimages under
`t ↦ decodeChal (LazyRO.answer t)` on `[0, 2^256)`.  The 32-byte answer is
`t` in big-endian, so limb `i` of the answer is the base-`2^32` digit
`7 - i` of `t`; the digits are independent (`count_div_mod_le`) and each
residue mod `p` has at most `3` preimages in `[0, 2^32)` since `2^32 ≤ 3p`.

`decodeOod_count`: `decodeOod y = c` forces `decodeChal y ∈ {c, c[c1 := 0]}`,
so fibers have size `≤ 2·3^8`.
-/

namespace ZkFormal.Algebra

open ArenaCore ArenaCore.Security

/-! ## Big-endian encoding -/

theorem beN_add (a b t : Nat) : Bytes.beN (a + b) t = Bytes.beN a (t / 256 ^ b) ++ Bytes.beN b t := by
  induction b generalizing t with
  | zero => simp [Bytes.beN]
  | succ b ih =>
    rw [← Nat.add_assoc]
    simp only [Bytes.beN]
    rw [ih, List.append_assoc, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ b)]

theorem beN_drop_take (a b c t : Nat) :
    ((Bytes.beN (a + (b + c)) t).drop a).take b = Bytes.beN b (t / 256 ^ c) := by
  rw [beN_add, List.drop_left' (Bytes.beN_length _ _), beN_add, List.take_left' (Bytes.beN_length _ _)]

/-- The base of the limbs, `2^32`. -/
abbrev M32 : Nat := 256 ^ 4

theorem be32_answer (t i : Nat) (hi : i < 8) :
    be32 (LazyRO.answer t) i = t / M32 ^ (7 - i) % M32 := by
  have h : Bytes.beN 32 t = Bytes.beN (4 * i + (4 + 4 * (7 - i))) t := by congr 1; omega
  rw [be32, LazyRO.answer, h, beN_drop_take, Bytes.beToNat_beN, Nat.pow_mul]

/-! ## Counting -/

theorem count_nil {α : Type} (E : α → Prop) : count [] E = 0 := by
  classical
  simp [count]

theorem count_singleton_le {α : Type} (a : α) (E : α → Prop) (k : Nat) (h : E a → 1 ≤ k) :
    count [a] E ≤ k := by
  classical
  rw [count_cons, count_nil]
  by_cases hE : E a
  · simp [hE]; exact h hE
  · simp [hE]

theorem count_and_const_le {α : Type} (l : List α) (p : Prop) (Q : α → Prop) :
    count l (fun x => p ∧ Q x) ≤ (open Classical in if p then count l Q else 0) := by
  classical
  by_cases hp : p
  · rw [ite_eq_left hp]; exact count_mono l (fun x h => h.2)
  · rw [ite_eq_right hp]
    have := count_mono l (E := fun x => p ∧ Q x) (F := fun _ => False) (fun x h => hp h.1)
    rw [count_const] at this
    simpa using this

/-- Independence of the quotient and remainder digits. -/
theorem count_div_mod_le (M : Nat) (P Q : Nat → Prop) : ∀ A : Nat,
    count (List.range (A * M)) (fun t => P (t / M) ∧ Q (t % M)) ≤
      count (List.range A) P * count (List.range M) Q
  | 0 => by simp [count_nil]
  | A + 1 => by
    classical
    rw [Nat.succ_mul, List.range_add, count_append, count_map, List.range_succ, count_append,
      Nat.add_mul]
    apply Nat.add_le_add (count_div_mod_le M P Q A)
    have h1 : count (List.range M) (fun s => P ((A * M + s) / M) ∧ Q ((A * M + s) % M)) ≤
        count (List.range M) (fun s => P A ∧ Q s) := by
      apply count_mono_mem
      intro s hs h
      have hs' : s < M := List.mem_range.mp hs
      have hd : (A * M + s) / M = A := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hs', Nat.add_zero]
      have hm : (A * M + s) % M = s := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hs']
      rw [hd, hm] at h
      exact h
    refine Nat.le_trans h1 (Nat.le_trans (count_and_const_le _ _ _) ?_)
    rw [count_cons, count_nil]
    by_cases hA : P A <;> simp [hA]

/-- Each residue mod `p` has at most 3 preimages in `[0, 2^32)`. -/
theorem count_ofNat_eq_le (x : Fp) : count (List.range M32) (fun d => Fp.ofNat d = x) ≤ 3 := by
  have h1 : count (List.range M32) (fun d => Fp.ofNat d = x) ≤
      count (List.range M32) (fun d => d % P = x.toNat) := by
    apply count_mono
    intro d h
    rw [← h, Fp.toNat_ofNat]
  have h2 : count (List.range M32) (fun d => d % P = x.toNat) ≤
      count (List.range (3 * P)) (fun d => d % P = x.toNat) := by
    have : 3 * P = M32 + (3 * P - M32) := by
      have : M32 ≤ 3 * P := by decide
      omega
    rw [this, List.range_add, count_append]
    exact Nat.le_add_right _ _
  have h3 : count (List.range (3 * P)) (fun d => d % P = x.toNat) ≤
      count (List.range 3) (fun _ => True) * count (List.range P) (fun d => d = x.toNat) := by
    refine Nat.le_trans ?_ (count_div_mod_le P (fun _ => True) (fun d => d = x.toNat) 3)
    exact count_mono _ (fun d h => ⟨trivial, h⟩)
  have h4 : count (List.range 3) (fun _ => True) ≤ 3 := by
    have := count_le_length (List.range 3) (fun _ => True); simpa using this
  have h5 := count_eq_le_one (List.nodup_range (n := P)) x.toNat
  have := Nat.mul_le_mul h4 h5
  omega

/-- `n` base-`2^32` digits each in a prescribed residue class. -/
theorem count_digits (n : Nat) : ∀ c : Nat → Fp,
    count (List.range (M32 ^ n)) (fun t => ∀ j, j < n → Fp.ofNat (t / M32 ^ j % M32) = c j) ≤ 3 ^ n := by
  induction n with
  | zero =>
    intro c
    have := count_le_length (List.range (M32 ^ 0))
      (fun t => ∀ j, j < 0 → Fp.ofNat (t / M32 ^ j % M32) = c j)
    simpa using this
  | succ n ih =>
    intro c
    rw [Nat.pow_succ]
    refine Nat.le_trans ?_ (Nat.le_trans (count_div_mod_le M32
      (fun u => ∀ j, j < n → Fp.ofNat (u / M32 ^ j % M32) = c (j + 1))
      (fun d => Fp.ofNat d = c 0) (M32 ^ n))
      (Nat.mul_le_mul (ih fun j => c (j + 1)) (count_ofNat_eq_le (c 0))))
    apply count_mono
    intro t h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h (j + 1) (by omega)
      rwa [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    · have := h 0 (by omega)
      simpa using this

/-- Generic fiber bound: if every fiber of `f` on `l` has size `≤ k` and `f`
lands in `L`, then `f`-preimages of `B` number at most `|B ∩ L|·k`. -/
theorem count_comp_le {α β : Type} (l : List α) (f : α → β) (k : Nat)
    (hk : ∀ c, count l (fun x => f x = c) ≤ k) (B : β → Prop) : ∀ L : List β,
    count l (fun x => f x ∈ L ∧ B (f x)) ≤ count L B * k
  | [] => by
    have := count_mono l (E := fun x => f x ∈ ([] : List β) ∧ B (f x)) (F := fun _ => False)
      (fun x h => by simp at h)
    rw [count_const] at this
    simpa [count_nil] using this
  | c :: L => by
    classical
    have h1 : count l (fun x => f x ∈ c :: L ∧ B (f x)) ≤
        count l (fun x => f x = c ∧ B c) + count l (fun x => f x ∈ L ∧ B (f x)) := by
      refine Nat.le_trans (count_mono l (F := fun x => (f x = c ∧ B c) ∨ (f x ∈ L ∧ B (f x)))
        ?_) (count_or_le _ _ _)
      intro x ⟨hm, hB⟩
      rcases List.mem_cons.mp hm with h | h
      · exact Or.inl ⟨h, h ▸ hB⟩
      · exact Or.inr ⟨h, hB⟩
    have h2 : count l (fun x => f x = c ∧ B c) ≤ (if B c then 1 else 0) * k := by
      by_cases hc : B c
      · rw [ite_eq_left hc, Nat.one_mul]
        exact Nat.le_trans (count_mono l (fun x h => h.1)) (hk c)
      · rw [ite_eq_right hc, Nat.zero_mul]
        have := count_mono l (E := fun x => f x = c ∧ B c) (F := fun _ => False)
          (fun x h => hc h.2)
        rw [count_const] at this
        simpa using this
    have h3 := count_comp_le l f k hk B L
    rw [count_cons, Nat.add_mul]
    omega

theorem count_comp_le' {α β : Type} (l : List α) (f : α → β) (k : Nat)
    (hk : ∀ c, count l (fun x => f x = c) ≤ k) (B : β → Prop) (L : List β)
    (hL : ∀ y, y ∈ L) : count l (fun x => B (f x)) ≤ count L B * k :=
  Nat.le_trans (count_mono l (fun x h => ⟨hL (f x), h⟩)) (count_comp_le l f k hk B L)

/-! ## The decoders -/

theorem roRange_eq : roRange = M32 ^ 8 := by
  show 2 ^ 256 = (256 ^ 4) ^ 8
  rw [← Nat.pow_mul, show 256 = 2 ^ 8 from rfl, ← Nat.pow_mul]

theorem decodeChal_fiber (c : Fp8) :
    count (List.range roRange) (fun t => decodeChal (LazyRO.answer t) = c) ≤ 3 ^ 8 := by
  rw [roRange_eq]
  refine Nat.le_trans (count_mono _ ?_) (count_digits 8 (fun j => Fp8.coeff c (7 - j)))
  intro t h j hj
  have hc := Fp8.coeff_ofCoeffs (fun i => Fp.ofNat (be32 (LazyRO.answer t) i)) (7 - j) (by omega)
  rw [be32_answer t (7 - j) (by omega), show 7 - (7 - j) = j by omega] at hc
  rw [← hc, ← h]
  rfl

theorem decodeOod_fiber (c : Fp8) :
    count (List.range roRange) (fun t => decodeOod (LazyRO.answer t) = c) ≤ 2 * 3 ^ 8 := by
  have hsub : ∀ y, decodeOod y = c → decodeChal y = c ∨ decodeChal y = { c with c1 := 0 } := by
    intro y h
    unfold decodeOod at h
    split at h
    · next hb =>
      right
      subst h
      exact Fp8.ext rfl hb.1 rfl rfl rfl rfl rfl rfl
    · exact Or.inl h
  refine Nat.le_trans (count_mono _ (fun t h => hsub _ h)) (Nat.le_trans (count_or_le _ _ _) ?_)
  have := Nat.add_le_add (decodeChal_fiber c) (decodeChal_fiber { c with c1 := 0 })
  omega

theorem decodeChal_count : DecodeChalCountStmt := by
  intro B b hb
  exact Nat.le_trans (count_comp_le' _ _ _ decodeChal_fiber B Fp8.all Fp8.mem_all)
    (Nat.mul_le_mul_right _ hb)

theorem decodeOod_count : DecodeOodCountStmt := by
  intro B b hb
  exact Nat.le_trans (count_comp_le' _ _ _ decodeOod_fiber B Fp8.all Fp8.mem_all)
    (Nat.mul_le_mul_right _ hb)

end ZkFormal.Algebra
