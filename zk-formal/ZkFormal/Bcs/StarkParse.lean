import ZkFormal.Bcs.StarkAdapter
import ZkFormal.Stark.ParseLemmas

/-!
# ZkFormal.Bcs.StarkParse — L4's readers consume fixed-length prefixes

`Fixed R k`: whenever the reader `R` succeeds, it consumed exactly `k` bytes,
and it succeeds identically on that prefix followed by anything.  Used to
show that the clear bytes absorbed by the transcript parse back to the
erased message (`parseParts_clear`).
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace ZkFormal.Bcs.Adapter

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

/-- The reader consumed a prefix of length `k` and is stable under changing the rest. -/
def Fixed {α : Type} (R : Bytes → Option (α × Bytes)) (k : Nat) : Prop :=
  ∀ r v r', R r = some (v, r') → ∃ p, r = p ++ r' ∧ p.length = k ∧ ∀ s, R (p ++ s) = some (v, s)

theorem take?_fixed (n : Nat) : Fixed (Stark.take? n) n := by
  intro r v r' h
  unfold Stark.take? at h
  split at h
  · rename_i hn
    cases h
    refine ⟨r.take n, (List.take_append_drop n r).symm, by simp; omega, fun s => ?_⟩
    unfold Stark.take?
    have hl : (r.take n).length = n := by simp; omega
    rw [if_pos (by simp [hl]), List.take_left' hl, List.drop_left' hl]
  · cases h

theorem readU32s_fixed : ∀ n, Fixed (Stark.readU32s n) (4 * n)
  | 0 => by
    intro r v r' h
    simp [Stark.readU32s] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl, fun s => by simp [Stark.readU32s]⟩
  | n + 1 => by
    intro r v r' h
    simp only [Stark.readU32s] at h
    split at h
    · cases h
    · rename_i b r1 h1
      split at h
      · cases h
      · rename_i xs r2 h2
        cases h
        obtain ⟨p1, e1, l1, s1⟩ := take?_fixed 4 _ _ _ h1
        obtain ⟨p2, e2, l2, s2⟩ := readU32s_fixed n _ _ _ h2
        refine ⟨p1 ++ p2, by rw [e1, e2, List.append_assoc], by simp [l1, l2]; omega, fun s => ?_⟩
        simp only [Stark.readU32s]
        rw [List.append_assoc, s1 (p2 ++ s)]
        simp only
        rw [s2 s]

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

theorem readFs_fixed (n : Nat) : Fixed (Stark.readFs (F := F) n) (4 * n) := by
  intro r v r' h
  unfold Stark.readFs at h
  split at h
  · cases h
  · rename_i xs r1 h1
    split at h
    · rename_i hall
      cases h
      obtain ⟨p, e, l, s1⟩ := readU32s_fixed n _ _ _ h1
      refine ⟨p, e, l, fun s => ?_⟩
      unfold Stark.readFs
      rw [s1 s]
      simp only [hall, if_true]
    · cases h

theorem readKs_fixed : ∀ n, Fixed (Stark.readKs (F := F) (K := K) n) (32 * n)
  | 0 => by
    intro r v r' h
    simp [Stark.readKs] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl, fun s => by simp [Stark.readKs]⟩
  | n + 1 => by
    intro r v r' h
    simp only [Stark.readKs] at h
    split at h
    · cases h
    · rename_i ls r1 h1
      split at h
      · cases h
      · rename_i xs r2 h2
        cases h
        obtain ⟨p1, e1, l1, s1⟩ := readFs_fixed (F := F) 8 _ _ _ h1
        obtain ⟨p2, e2, l2, s2⟩ := readKs_fixed n _ _ _ h2
        refine ⟨p1 ++ p2, by rw [e1, e2, List.append_assoc], by simp [l1, l2]; omega, fun s => ?_⟩
        simp only [Stark.readKs]
        rw [List.append_assoc, s1 (p2 ++ s)]
        simp only
        rw [s2 s]

theorem readKs_length : ∀ {n : Nat} {r : Bytes} {xs : List K} {r' : Bytes},
    Stark.readKs (F := F) n r = some (xs, r') → xs.length = n
  | 0, r, xs, r', h => by simp [Stark.readKs] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | n + 1, r, xs, r', h => by
    simp only [Stark.readKs] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ys r2 h2
        cases h
        simp [readKs_length h2]

end

theorem readHeader_fixed (n : Nat) : Fixed (Stark.readHeader n) (8 + n) := by
  intro r v r' h
  unfold Stark.readHeader at h
  split at h
  · rename_i a b r1 h1
    split at h
    · rename_i hab
      split at h
      · rename_i hs r2 h2
        cases h
        obtain ⟨p1, e1, l1, s1⟩ := readU32s_fixed 2 _ _ _ h1
        obtain ⟨p2, e2, l2, s2⟩ := take?_fixed n _ _ _ h2
        refine ⟨p1 ++ p2, by rw [e1, e2, List.append_assoc], by simp [l1, l2], fun s => ?_⟩
        unfold Stark.readHeader
        rw [List.append_assoc, s1 (p2 ++ s)]
        simp only [hab, if_true, and_self]
        rw [s2 s]
      · cases h
    · cases h
  · cases h

theorem readHeader_length {n : Nat} {r : Bytes} {l : List Nat} {r' : Bytes}
    (h : Stark.readHeader n r = some (l, r')) : l.length = n := by
  unfold Stark.readHeader at h
  split at h
  · split at h
    · rename_i hab
      split at h
      · rename_i hs r2 h2
        cases h
        unfold Stark.take? at h2
        split at h2
        · cases h2; simp; omega
        · cases h2
      · cases h
    · cases h
  · cases h

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-- **Parsed messages, clear part.**  The clear bytes of a parsed message
(`clearOf`) parse back (with `parseClear`) to the erased parts, followed by
anything; the roots are 64-byte, one per oracle part. -/
theorem parseParts_clear (hdr : List Nat) : ∀ (ps : List Stark.Part) (r : Bytes)
    (vs : List (Stark.PartV K Bytes)) (r' : Bytes),
    Stark.parseParts (F := F) hdr ps r = some (vs, r') →
    ∃ raw, r = raw ++ r' ∧ (∀ s, parseClear (F := F) hdr ps (Stark.clearOf vs raw ++ s) =
        some (vs.map Stark.PT.PartV.erase, s)) ∧
      (∀ root ∈ Stark.rootsOf vs, root.length = 64) ∧
      (Stark.rootsOf vs).length = (oracleShapes ps).length
  | [], r, vs, r', h => by
    simp [Stark.parseParts] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, fun s => by simp [parseClear, Stark.clearOf], by simp [Stark.rootsOf],
      by simp [Stark.rootsOf, oracleShapes]⟩
  | p :: ps, r, vs, r', h => by
    simp only [Stark.parseParts] at h
    split at h
    · cases h
    · rename_i v r1 h1
      split at h
      · cases h
      · rename_i ws r2 h2
        cases h
        obtain ⟨raw2, e2, c2, rl2, rn2⟩ := parseParts_clear hdr ps r1 ws r' h2
        cases p with
        | header n =>
          simp only at h1
          split at h1
          · rename_i l r3 h3
            split at h1
            · rename_i hl
              cases h1
              obtain ⟨p1, e1, l1, s1⟩ := readHeader_fixed n _ _ _ h3
              have hln := readHeader_length h3
              refine ⟨p1 ++ raw2, by rw [e1, e2, List.append_assoc], fun s => ?_, ?_, ?_⟩
              · simp only [Stark.clearOf, List.length_append]
                rw [List.take_left' (by omega), List.drop_left' (by omega), List.append_assoc]
                simp only [parseClear]
                rw [s1]
                simp only [hl, if_true]
                rw [c2 s]
                rfl
              · simpa [Stark.rootsOf] using rl2
              · simpa [Stark.rootsOf, oracleShapes] using rn2
            · cases h1
          · cases h1
        | oracle mats =>
          simp only at h1
          split at h1
          · rename_i root r3 h3
            cases h1
            obtain ⟨p1, e1, l1, s1⟩ := take?_fixed 64 _ _ _ h3
            have hroot : root = p1 := by
              have := s1 []; rw [List.append_nil] at this
              unfold Stark.take? at this
              rw [if_pos (by omega)] at this
              simp only [Option.some.injEq, Prod.mk.injEq] at this
              rw [List.take_of_length_le (by omega)] at this
              exact this.1.symm
            subst hroot
            refine ⟨root ++ raw2, by rw [e1, e2, List.append_assoc], fun s => ?_, ?_, ?_⟩
            · simp only [Stark.clearOf, List.drop_left' l1, parseClear]
              rw [c2 s]
              rfl
            · intro x hx
              simp only [Stark.rootsOf, List.filterMap_cons, List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact l1
              · exact rl2 x hx
            · simp only [Stark.rootsOf, oracleShapes, List.filterMap_cons, List.length_cons]
              simpa [Stark.rootsOf, oracleShapes] using rn2
          · cases h1
        | elems n =>
          simp only at h1
          split at h1
          · rename_i xs r3 h3
            cases h1
            obtain ⟨p1, e1, l1, s1⟩ := readKs_fixed (F := F) (K := K) n _ _ _ h3
            have hxs : xs.length = n := readKs_length h3
            refine ⟨p1 ++ raw2, by rw [e1, e2, List.append_assoc], fun s => ?_, ?_, ?_⟩
            · simp only [Stark.clearOf, List.length_append]
              rw [List.take_left' (by omega), List.drop_left' (by omega), List.append_assoc]
              simp only [parseClear]
              rw [s1]
              simp only
              rw [c2 s]
              rfl
            · simpa [Stark.rootsOf] using rl2
            · simpa [Stark.rootsOf, oracleShapes] using rn2
          · cases h1

end

end ZkFormal.Bcs.Adapter
