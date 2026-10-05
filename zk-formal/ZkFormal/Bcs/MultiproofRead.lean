import ZkFormal.Bcs.StarkAdapter

/-!
# ZkFormal.Bcs.MultiproofRead — prefix stability of L4's byte readers

If a reader consumes `p` from `r = p ++ r'`, it reads the same value from
`p ++ s` for every `s`; in particular the consumed prefix
`r.take (r.length - r'.length)` re-parses to the same value with nothing left.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.Bcs.Multiproof

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

/-- `f` is a prefix reader: it consumes a prefix of its input and ignores
the rest. -/
def PrefixReader {α : Type} (f : Bytes → Option (α × Bytes)) : Prop :=
  ∀ r v r', f r = some (v, r') → ∃ p, r = p ++ r' ∧ ∀ s, f (p ++ s) = some (v, s)

theorem PrefixReader.consumed {α : Type} {f : Bytes → Option (α × Bytes)} (hf : PrefixReader f)
    {r : Bytes} {v : α} {r' : Bytes} (h : f r = some (v, r')) :
    f (r.take (r.length - r'.length)) = some (v, []) := by
  obtain ⟨p, rfl, hp⟩ := hf r v r' h
  have : (p ++ r').take ((p ++ r').length - r'.length) = p := by
    simp [List.take_append]
  rw [this]
  simpa using hp []

theorem take?_prefix (n : Nat) : PrefixReader (Stark.take? n) := by
  intro r v r' h
  unfold Stark.take? at h
  split at h
  · rename_i hn
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨r.take n, (List.take_append_drop n r).symm, fun s => ?_⟩
    have hl : (r.take n).length = n := by simp; omega
    unfold Stark.take?
    rw [ite_eq_left (by simp; omega)]
    simp [List.take_append, List.drop_append, hl]
  · cases h

theorem readU32s_prefix : ∀ n, PrefixReader (Stark.readU32s n)
  | 0 => by
    intro r v r' h
    simp only [Stark.readU32s, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, fun s => rfl⟩
  | n + 1 => by
    intro r v r' h
    simp only [Stark.readU32s] at h
    split at h
    · cases h
    · rename_i b r1 hb
      split at h
      · cases h
      · rename_i xs r2 hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨p1, rfl, hp1⟩ := take?_prefix 4 r b r1 hb
        obtain ⟨p2, rfl, hp2⟩ := readU32s_prefix n _ xs r2 hx
        refine ⟨p1 ++ p2, by simp, fun s => ?_⟩
        simp only [Stark.readU32s]
        rw [List.append_assoc, hp1 (p2 ++ s)]
        simp only
        rw [hp2 s]

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

theorem readFs_prefix (n : Nat) : PrefixReader (Stark.readFs (F := F) n) := by
  intro r v r' h
  unfold Stark.readFs at h
  split at h
  · cases h
  · rename_i xs r1 hx
    split at h
    · rename_i hall
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨p, rfl, hp⟩ := readU32s_prefix n r xs r1 hx
      refine ⟨p, rfl, fun s => ?_⟩
      unfold Stark.readFs
      rw [hp s]
      simp only [hall, ite_true]
    · cases h

theorem readRows_prefix : ∀ ws, PrefixReader (Stark.readRows (F := F) ws)
  | [] => by
    intro r v r' h
    simp only [Stark.readRows, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, fun s => rfl⟩
  | w :: ws => by
    intro r v r' h
    simp only [Stark.readRows] at h
    split at h
    · cases h
    · rename_i row r1 hrow
      split at h
      · cases h
      · rename_i rows r2 hrows
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨p1, rfl, hp1⟩ := readFs_prefix (F := F) w r row r1 hrow
        obtain ⟨p2, rfl, hp2⟩ := readRows_prefix ws _ rows r2 hrows
        refine ⟨p1 ++ p2, by simp, fun s => ?_⟩
        simp only [Stark.readRows]
        rw [List.append_assoc, hp1 (p2 ++ s)]
        simp only
        rw [hp2 s]

/-- The consumed bytes of a successful `readRows` re-parse to the same rows. -/
theorem readRows_consumed {ws : List Nat} {r : Bytes} {rows : List (List F)} {r' : Bytes}
    (h : Stark.readRows (F := F) ws r = some (rows, r')) :
    Stark.readRows (F := F) ws (r.take (r.length - r'.length)) = some (rows, []) :=
  (readRows_prefix ws).consumed h

end

end ZkFormal.Bcs.Multiproof
