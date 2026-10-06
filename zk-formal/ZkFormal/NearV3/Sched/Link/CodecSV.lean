import ZkFormal.NearV3.Sched.Link.CodecVal

/-!
# `codec_schedVal`: the trie lane's `SchedVal` interface

There is a function `sv : Nat → List Nat` (instance τ ↦ its new `0x0f` encoding, the post bytes
of τ's codec block) with:
* bytes `< 256` and length `< 2^24`;
* every received `SPLEN` message is `(τ, |sv τ|)`;
* every received `SPOST` message is `(τ, d, (sv τ)[d])` with `d < |sv τ|`.

Ingredients:
* `codec_cover`: every active codec row lies in an instance block;
* `enc_row`: an encoding row is `f + i` with `i < L = 37 + 24·N`;
* `block_unique`: distinct blocks have distinct τ. Each block's first row receives its `SPAR`
  codec parameters `[τ, 0, …]`. Only public segments send on `SPAR`, and `render` has one such
  record per τ, so two blocks with the same τ would need the record twice.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E

namespace Codec
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem pad_next (hL : CLocal tr t pub) {w : Nat} (hw : w + 1 < tr.height t)
    (ha : cv tr t w act = 0) : cv tr t (w + 1) act = 0 := by
  have hw0 : w < tr.height t := by omega
  obtain ⟨q, c1⟩ := zd hL hw0 (e := mul3 .isTransition (notE (c act)) (n act))
    (by simp [constraints, cKind])
  zs c1 [nx hw, ha]
  simp only [zev, Mem.tenv_last_zero hw] at c1
  have := lt (tr := tr) (t := t) (w + 1) act
  omega

theorem act_prev (hL : CLocal tr t pub) {w : Nat} (hw1 : w + 1 < tr.height t)
    (ha : cv tr t (w + 1) act = 1) : cv tr t w act = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (kinds hL (show w < tr.height t by omega)).1 with h | h
  · have := pad_next hL hw1 h; omega
  · exact h

theorem row_first_kF (hL : CLocal tr t pub) (h0 : 0 < tr.height t) (ha : cv tr t 0 act = 1) :
    cv tr t 0 kF = 1 := by
  have hf : (tenv tr t 0 pub).first = 1 := by simp [tenv]
  obtain ⟨q, c1⟩ := zd hL h0 (e := .mul .isFirst (.mul (c act) (notE (c kF))))
    (by simp [constraints, cKind])
  zs c1 [zev_isFirst, hf, ha]
  have := (kinds hL h0).2.2.2.2.2.1
  omega

/-- **Every active row lies in an instance block.** -/
theorem codec_cover (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) :
    ∀ r, r < tr.height t → cv tr t r act = 1 →
      ∃ f, f ≤ r ∧ cv tr t f kF = 1 ∧ r < f + 5 + 24 * cv tr t f NN + 64 := by
  intro r
  induction r with
  | zero => intro h0 ha; exact ⟨0, Nat.le_refl _, row_first_kF hL h0 ha, by omega⟩
  | succ r ih =>
    intro hr1 ha1
    obtain ⟨f, hfr, hF, hrf⟩ := ih (by omega) (act_prev hL hr1 ha1)
    by_cases hlt : r + 1 < f + 5 + 24 * cv tr t f NN + 64
    · exact ⟨f, by omega, hF, hlt⟩
    · have he : r + 1 = f + 5 + 24 * cv tr t f NN + 64 := by omega
      have hB := codec_block hL hH (show f < tr.height t by omega) hF
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hend⟩ := hB
      rw [← he] at hend
      rcases hend with h | h
      · omega
      · exact ⟨r + 1, Nat.le_refl _, h, by omega⟩

/-- The encoding gate is `kH + kR + kZ`. -/
theorem encG_eval (r : Nat) (h : (encG).eval tr t r pub = 1) (hL : CLocal tr t pub)
    (hr : r < tr.height t) : cv tr t r kH + cv tr t r kR + cv tr t r kZ = 1 := by
  have K := kinds hL hr
  have e : (encG).eval tr t r pub = Fp.ofNat (cv tr t r kH + cv tr t r kR + cv tr t r kZ) :=
    ev_of (by simp only [encG, zev_add, zev_c, cur_cv]; omega)
  rw [e] at h
  have h1 : Fp.ofNat (cv tr t r kH + cv tr t r kR + cv tr t r kZ) = Fp.ofNat 1 := h
  exact ofNat_inj' (by omega) (by decide) h1

/-- **An encoding row is `f + i` with `i < 37 + 24·N` in its block.** -/
theorem enc_row (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {r : Nat} (hr : r < tr.height t)
    (he : cv tr t r kH + cv tr t r kR + cv tr t r kZ = 1) :
    ∃ f, f ≤ r ∧ cv tr t f kF = 1 ∧ r - f < 37 + 24 * cv tr t f NN := by
  have K := kinds hL hr
  obtain ⟨f, hfr, hF, hrf⟩ := codec_cover hL hH r hr (by omega)
  refine ⟨f, hfr, hF, ?_⟩
  apply Nat.lt_of_not_le; intro hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hA, -⟩ := codec_block hL hH (show f < tr.height t by omega) hF
  obtain ⟨-, hkA, -⟩ := hA (r - f - (5 + 24 * cv tr t f NN + 32)) (by omega)
  rw [show f + 5 + 24 * cv tr t f NN + 32 + (r - f - (5 + 24 * cv tr t f NN + 32)) = r by omega] at hkA
  omega

end Codec

/-! ## One codec block per τ -/

theorem count_two {α : Type} [BEq α] [LawfulBEq α] (g : Nat → List α) (m : α) {a b : Nat}
    (hab : a ≠ b) (ha : m ∈ g a) (hb : m ∈ g b) :
    ∀ (l : List Nat), l.Nodup → a ∈ l → b ∈ l → 2 ≤ (l.flatMap g).count m
  | [], _, h, _ => by simp at h
  | x :: tl, hnd, hal, hbl => by
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.1 hal with e | e <;> rcases List.mem_cons.1 hbl with e' | e'
    · exact absurd (e.trans e'.symm) hab
    · subst e
      have h1 := List.count_pos_iff.2 ha
      have h2 := List.count_pos_iff.2 (List.mem_flatMap.2 ⟨b, e', hb⟩)
      omega
    · subst e'
      have h1 := List.count_pos_iff.2 hb
      have h2 := List.count_pos_iff.2 (List.mem_flatMap.2 ⟨a, e, ha⟩)
      omega
    · have := count_two g m hab ha hb tl hnd.2 e e'
      omega

theorem parBlock_head {τ : Nat} {P : InstPub} {r : List Nat} (hr : r ∈ parBlock τ P) :
    r.head? = some τ := by
  simp only [parBlock, List.mem_append, List.mem_singleton] at hr
  rcases hr with (((rfl | hr) | hr) | hr) | hr
  · simp [parCodec]
  · split at hr
    · simp at hr
    · simp only [List.mem_singleton] at hr; subst hr; simp [parScan]
  · simp only [rawRecs, List.mem_map] at hr
    obtain ⟨⟨q, c⟩, -, rfl⟩ := hr; simp
  · simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨side, -, x, -, rfl⟩ := hr; simp
  · simp only [linkRecs, List.mem_map] at hr
    obtain ⟨l, -, rfl⟩ := hr; simp

theorem parBlock_tag {τ : Nat} {P : InstPub} {r : List Nat} (hr : r ∈ parBlock τ P) :
    r = parCodec τ P ∨ ∃ a, r[1]? = some a ∧ 1 ≤ a ∧ a ≤ 4 := by
  simp only [parBlock, List.mem_append, List.mem_singleton] at hr
  rcases hr with (((rfl | hr) | hr) | hr) | hr
  · exact Or.inl rfl
  · split at hr
    · simp at hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact Or.inr ⟨1, by simp [parScan, PT_SCAN], by decide, by decide⟩
  · simp only [rawRecs, List.mem_map] at hr
    obtain ⟨⟨q, c⟩, -, rfl⟩ := hr
    exact Or.inr ⟨2, by simp [PT_RAW], by decide, by decide⟩
  · simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨side, -, x, -, rfl⟩ := hr
    exact Or.inr ⟨3, by simp [PT_SHD], by decide, by decide⟩
  · simp only [linkRecs, List.mem_map] at hr
    obtain ⟨l, -, rfl⟩ := hr
    exact Or.inr ⟨4, by simp [PT_LINK], by decide, by decide⟩

theorem ne_tag0 {r : List Nat} {M : List Fp} {a : Nat} (hr : r[1]? = some a) (ha1 : 1 ≤ a) (ha4 : a ≤ 4)
    (hM : M[1]? = some (Fp.ofNat 0)) : r.map Fp.ofNat ≠ M := by
  intro e; subst e
  rw [List.getElem?_map, hr] at hM
  simp only [Option.map_some, Option.some.injEq] at hM
  have := ofNat_inj' (by omega) (by decide) hM
  omega

/-- A tag-0 `SPAR` record of head `τ` is `τ`'s codec parameter record. -/
theorem par_codec_mem {Ps : List InstPub} {fwd : List (Nat × Nat)} (hlen : Ps.length < 2013265921)
    {M : List Fp} (hM : M ∈ (render Ps fwd).par.map (·.map Fp.ofNat)) {τ : Nat} (hτ : τ < 2013265921)
    (h0 : M.head? = some (Fp.ofNat τ)) (h1 : M[1]? = some (Fp.ofNat 0)) :
    τ < Ps.length ∧ M = (parCodec τ (Ps.getD τ instD)).map Fp.ofNat := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  rw [render_par, List.mem_flatMap] at hr
  obtain ⟨τ', hτ', hr⟩ := hr
  have hτ'l := List.mem_range.1 hτ'
  have hh := parBlock_head hr
  have e : τ' = τ := by
    by_cases hne : τ' = τ
    · exact hne
    · exact absurd rfl (ne_of_head hh h0 (by omega) hτ hne)
  subst e
  refine ⟨hτ'l, ?_⟩
  rcases parBlock_tag hr with e | ⟨a, ha, h1a, h4a⟩
  · rw [e]
  · exact absurd rfl (ne_tag0 ha h1a h4a h1)

/-- The non-codec records of a block. -/
def parRest (τ : Nat) (P : InstPub) : List (List Nat) :=
  (if P.raw.isEmpty then [] else [parScan τ P]) ++ rawRecs τ P ++ shardRecs τ P ++ linkRecs τ P

theorem parBlock_split (τ : Nat) (P : InstPub) : parBlock τ P = [parCodec τ P] ++ parRest τ P := by
  simp [parBlock, parRest, List.append_assoc]

theorem parRest_tag {τ : Nat} {P : InstPub} {r : List Nat} (hr : r ∈ parRest τ P) :
    ∃ a, r[1]? = some a ∧ 1 ≤ a ∧ a ≤ 4 := by
  simp only [parRest, List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · split at hr
    · simp at hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨1, by simp [parScan, PT_SCAN], by decide, by decide⟩
  · simp only [rawRecs, List.mem_map] at hr
    obtain ⟨⟨q, c⟩, -, rfl⟩ := hr
    exact ⟨2, by simp [PT_RAW], by decide, by decide⟩
  · simp only [shardRecs, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨side, -, x, -, rfl⟩ := hr
    exact ⟨3, by simp [PT_SHD], by decide, by decide⟩
  · simp only [linkRecs, List.mem_map] at hr
    obtain ⟨l, -, rfl⟩ := hr
    exact ⟨4, by simp [PT_LINK], by decide, by decide⟩

theorem par_codec_count {Ps : List InstPub} {fwd : List (Nat × Nat)} (hlen : Ps.length < 2013265921)
    (τ : Nat) (hτ : τ < Ps.length) :
    ((render Ps fwd).par.map (·.map Fp.ofNat)).count ((parCodec τ (Ps.getD τ instD)).map Fp.ofNat) ≤ 1 := by
  rw [render_par]
  rw [count_flatMap_one Fp.ofNat _ _ τ _ List.nodup_range (List.mem_range.2 hτ) ?_]
  · rw [parBlock_split, List.map_append, List.count_append]
    have h0 : ((parRest τ (Ps.getD τ instD)).map (·.map Fp.ofNat)).count
        ((parCodec τ (Ps.getD τ instD)).map Fp.ofNat) = 0 := by
      apply count_zero_of
      intro r hr
      obtain ⟨a, ha, h1, h4⟩ := parRest_tag hr
      exact ne_tag0 ha h1 h4 (by simp [parCodec])
    rw [h0]
    simp
  · intro τ' hmem hne r hr
    exact ne_of_head (parBlock_head hr) (by simp [parCodec]) (by have := List.mem_range.1 hmem; omega)
      (by omega) hne

end ZkFormal.NearV3.Sched
