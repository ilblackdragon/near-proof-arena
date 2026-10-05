import ZkFormal.Stark.Statements

/-!
# ZkFormal.Stark.ParseLemmas — the prefix parser splits the proof (P1)

Every reader returns a suffix of its input; a message's raw bytes are exactly
the bytes consumed, so the proof is the concatenation of the absorbed messages
followed by the query-phase bytes (`parsePrefix_split : ParsePrefixStmt`).
Also: header serialization round trip (`readHeader_encHeader`).
-/

namespace ZkFormal.Stark

open ArenaCore Lean.Grind

/-- `s` is a suffix of `r`. -/
def IsSuf (s r : Bytes) : Prop := ∃ p, r = p ++ s

theorem IsSuf.refl (r : Bytes) : IsSuf r r := ⟨[], rfl⟩

theorem IsSuf.trans {a b c : Bytes} (h1 : IsSuf a b) (h2 : IsSuf b c) : IsSuf a c := by
  obtain ⟨p, rfl⟩ := h1; obtain ⟨q, rfl⟩ := h2; exact ⟨q ++ p, by simp⟩

theorem IsSuf.take_append {s r : Bytes} (h : IsSuf s r) : r.take (r.length - s.length) ++ s = r := by
  obtain ⟨p, rfl⟩ := h
  simp

theorem take?_suf {n : Nat} {r a b : Bytes} (h : take? n r = some (a, b)) : IsSuf b r := by
  unfold take? at h
  split at h
  · cases h; exact ⟨r.take n, (List.take_append_drop n r).symm⟩
  · cases h

theorem readU32s_suf : ∀ {n : Nat} {r : Bytes} {xs : List Nat} {r' : Bytes},
    readU32s n r = some (xs, r') → IsSuf r' r
  | 0, r, xs, r', h => by simp [readU32s] at h; obtain ⟨_, rfl⟩ := h; exact .refl _
  | n + 1, r, xs, r', h => by
    simp only [readU32s] at h
    split at h
    · cases h
    · next b r1 h1 =>
      split at h
      · cases h
      · next ys r2 h2 =>
        cases h
        exact (readU32s_suf h2).trans (take?_suf h1)

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]

omit [DecidableEq F] in
theorem readFs_suf {n : Nat} {r : Bytes} {xs : List F} {r' : Bytes}
    (h : readFs (F := F) n r = some (xs, r')) : IsSuf r' r := by
  unfold readFs at h
  split at h
  · cases h
  · next ys r1 h1 =>
    split at h
    · cases h; exact readU32s_suf h1
    · cases h

theorem readKs_suf : ∀ {n : Nat} {r : Bytes} {xs : List K} {r' : Bytes},
    readKs (F := F) n r = some (xs, r') → IsSuf r' r
  | 0, r, xs, r', h => by simp [readKs] at h; obtain ⟨_, rfl⟩ := h; exact .refl _
  | n + 1, r, xs, r', h => by
    simp only [readKs] at h
    split at h
    · cases h
    · next ls r1 h1 =>
      split at h
      · cases h
      · next ys r2 h2 =>
        cases h
        exact (readKs_suf h2).trans (readFs_suf h1)

theorem readHeader_suf {n : Nat} {r : Bytes} {l : List Nat} {r' : Bytes}
    (h : readHeader n r = some (l, r')) : IsSuf r' r := by
  unfold readHeader at h
  split at h
  · next v m r1 h1 =>
    split at h
    · split at h
      · next hs r2 h2 => cases h; exact (take?_suf h2).trans (readU32s_suf h1)
      · cases h
    · cases h
  · cases h

theorem parseParts_suf {hdr : List Nat} : ∀ {ps : List Part} {r : Bytes}
    {vs : List (PartV K Bytes)} {r' : Bytes},
    parseParts (F := F) hdr ps r = some (vs, r') → IsSuf r' r
  | [], r, vs, r', h => by simp [parseParts] at h; obtain ⟨_, rfl⟩ := h; exact .refl _
  | p :: ps, r, vs, r', h => by
    simp only [parseParts] at h
    split at h
    · cases h
    · next v r1 h1 =>
      split at h
      · cases h
      · next ws r2 h2 =>
        cases h
        refine (parseParts_suf h2).trans ?_
        cases p with
        | header n =>
          simp only at h1
          split at h1
          · next l r3 h3 =>
            split at h1
            · cases h1; exact readHeader_suf h3
            · cases h1
          · cases h1
        | oracle _ =>
          simp only at h1
          split at h1
          · next a r3 h3 => cases h1; exact take?_suf h3
          · cases h1
        | elems n =>
          simp only at h1
          split at h1
          · next a r3 h3 => cases h1; exact readKs_suf h3
          · cases h1

theorem parseSlots_split {hdr : List Nat} : ∀ {ss : List Slot} {r : Bytes}
    {ps : List (PSlot K)} {r' : Bytes},
    parseSlots (F := F) hdr ss r = some (ps, r') → r = ps.flatMap PSlot.raw ++ r'
  | [], r, ps, r', h => by simp [parseSlots] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | .chal ood :: ss, r, ps, r', h => by
    simp only [parseSlots] at h
    split at h
    · cases h
    · next qs r1 h1 =>
      cases h
      simpa [PSlot.raw] using parseSlots_split h1
  | .msg parts :: ss, r, ps, r', h => by
    simp only [parseSlots] at h
    split at h
    · cases h
    · next vs r1 h1 =>
      split at h
      · cases h
      · next qs r2 h2 =>
        cases h
        have e := parseSlots_split h2
        simp only [List.flatMap_cons, PSlot.raw, List.append_assoc, ← e]
        exact ((parseParts_suf h1).take_append).symm

end

/-- **(P1)** -/
theorem parsePrefix_split : ParsePrefixStmt := by
  intro F K _ _ _ _ V pb hdr ps rest h
  unfold parsePrefix at h
  split at h
  · cases h
  · next hdr' r1 _ =>
    split at h
    · split at h
      · cases h
      · next qs r2 h2 => cases h; exact parseSlots_split h2
    · cases h

/-! ## Header round trip -/

/-- Header encoding: `u32 version ‖ u32 numTables ‖ u8 h_t`. -/
def encHeader (hs : List Nat) : Bytes :=
  Bytes.leN 4 formatVersion ++ Bytes.leN 4 hs.length ++ hs.map UInt8.ofNat

theorem u8_toNat_ofNat (x : Nat) : (UInt8.ofNat x).toNat = x % 256 := by simp

theorem leToNat_leN4 (n : Nat) (h : n < 2 ^ 32) : Bytes.leToNat (Bytes.leN 4 n) = n := by
  simp only [Bytes.leN, Bytes.leToNat, u8_toNat_ofNat]
  omega

theorem readHeader_encHeader (hs : List Nat) (rest : Bytes) (hlen : hs.length < 2 ^ 32)
    (hb : ∀ h ∈ hs, h < 256) :
    readHeader hs.length (encHeader hs ++ rest) = some (hs, rest) := by
  have hmap : (hs.map UInt8.ofNat).map UInt8.toNat = hs := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id hs]
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp, u8_toNat_ofNat, id]
    exact Nat.mod_eq_of_lt (hb a ha)
  simp only [readHeader, encHeader, readU32s, take?, Bytes.leN_length, List.length_append,
    List.append_assoc]
  simp [leToNat_leN4 _ hlen, leToNat_leN4 formatVersion (by decide), Bytes.leN_length, hmap]

end ZkFormal.Stark
