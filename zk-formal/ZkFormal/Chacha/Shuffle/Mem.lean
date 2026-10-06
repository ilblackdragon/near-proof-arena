import ZkFormal.Chacha.Shuffle.Walk
import ZkFormal.Chacha.Bus

/-!
# ZkFormal.Chacha.Shuffle.Mem — the memory bus of `shufV3`

`MemBal`: the internal memory bus `busMem` balances within the table (it is used by no
other table and no public segment).  Then every active read is matched by an active write
with the same message (`exists_write`), and a message written at most once is read at most
once (`read_unique`).
-/

namespace ZkFormal.Chacha.Shuffle

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- The buses of the table. -/
structure Buses where
  bin : Nat
  bout : Nat
  mem : Nat
  gen : Nat
  shuf : Nat

def Buses.is (B : Buses) : List Interaction := interactions B.bin B.bout B.mem B.gen B.shuf

/-- The memory bus is private and distinct from the others. -/
def Buses.ok (B : Buses) : Prop := B.mem ≠ B.bin ∧ B.mem ≠ B.bout ∧ B.mem ≠ B.gen ∧ B.mem ≠ B.shuf

/-- Balance of the memory bus inside the table. -/
def MemBal (B : Buses) (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop :=
  ∀ m, tableBusCount B.is tr t pub B.mem true m = tableBusCount B.is tr t pub B.mem false m

def iMinit (B : Buses) : Interaction := B.is[1]!
def iMR1 (B : Buses) : Interaction := B.is[2]!
def iMR2 (B : Buses) : Interaction := B.is[3]!
def iMW2 (B : Buses) : Interaction := B.is[4]!

theorem is_nodup (B : Buses) : B.is.Nodup := by
  have h : ((B.is).map (fun i : Interaction => (i.send, i.mult, i.msg.length))).Nodup := by
    simp only [Buses.is, interactions, List.map_cons, List.map_nil]
    decide
  exact List.Pairwise.of_map _ (fun a b hab e => hab (by rw [e])) h

theorem is_mult (B : Buses) : ∀ i ∈ B.is, i.mult.length = 1 := by
  simp [Buses.is, interactions]

theorem cell_eq {r r' x y : Nat} (h : tr.cell t r x = tr.cell t r' y) : cv tr t r x = cv tr t r' y := by
  unfold cv; rw [h]

theorem msg_minit (B : Buses) (r : Nat) : (iMinit B).msgVal tr t r pub =
    [tr.cell t r colInst, tr.cell t r colQ, tr.cell t r colL, tr.cell t r colV0] := rfl
theorem msg_mr1 (B : Buses) (r : Nat) : (iMR1 B).msgVal tr t r pub =
    [tr.cell t r colInst, tr.cell t r colQ, tr.cell t r colT1, tr.cell t r colC] := rfl
theorem msg_mr2 (B : Buses) (r : Nat) : (iMR2 B).msgVal tr t r pub =
    [tr.cell t r colInst, tr.cell t r colJ, tr.cell t r colT2, tr.cell t r colO] := rfl
theorem msg_mw2 (B : Buses) (r : Nat) : (iMW2 B).msgVal tr t r pub =
    [tr.cell t r colInst, tr.cell t r colJ, tr.cell t r colQ, tr.cell t r colC] := rfl

theorem mult_col {i : Interaction} {x r : Nat} (hi : i.mult = [ZkFormal.Chacha.Table.E.c x]) :
    i.multNat tr t r pub ≠ 0 ↔ cv tr t r x = 1 := by
  unfold Interaction.multNat
  rw [hi]
  simp only [Interaction.multNat.go]
  have e : (ZkFormal.Chacha.Table.E.c x).eval tr t r pub = tr.cell t r x := rfl
  rw [e]
  constructor
  · intro h
    by_cases h1 : tr.cell t r x = 1
    · unfold cv; rw [h1]; rfl
    · simp [h1] at h
  · intro h
    have : tr.cell t r x = 1 := by
      unfold cv at h; rw [← Fp.ofNat_toNat (tr.cell t r x), h]; rfl
    simp [this]

theorem mem_minit (B : Buses) : iMinit B ∈ B.is := by simp [iMinit, Buses.is, interactions]
theorem mem_mr1 (B : Buses) : iMR1 B ∈ B.is := by simp [iMR1, Buses.is, interactions]
theorem mem_mr2 (B : Buses) : iMR2 B ∈ B.is := by simp [iMR2, Buses.is, interactions]
theorem mem_mw2 (B : Buses) : iMW2 B ∈ B.is := by simp [iMW2, Buses.is, interactions]

/-- The sending interactions on the memory bus are `MINIT` and `MW2`. -/
theorem mem_senders (B : Buses) (hB : B.ok) {i : Interaction} (hi : i ∈ B.is) (hb : i.bus = B.mem)
    (hs : i.send = true) : i = iMinit B ∨ i = iMW2 B := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  simp only [Buses.is, interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [iMinit, iMW2, Buses.is, interactions]

/-- The receiving interactions on the memory bus are `MR1` and `MR2`. -/
theorem mem_receivers (B : Buses) (hB : B.ok) {i : Interaction} (hi : i ∈ B.is) (hb : i.bus = B.mem)
    (hs : i.send = false) : i = iMR1 B ∨ i = iMR2 B := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  simp only [Buses.is, interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [iMR1, iMR2, Buses.is, interactions]

/-- An active read is matched by an active write. -/
theorem exists_write (B : Buses) (hB : B.ok) (hM : MemBal B tr t pub) {r : Nat} (hr : r < tr.height t)
    {i : Interaction} (hi : i ∈ B.is) (hb : i.bus = B.mem) (hs : i.send = false)
    (ha : i.multNat tr t r pub ≠ 0) :
    ∃ r', r' < tr.height t ∧ ∃ i', (i' = iMinit B ∨ i' = iMW2 B) ∧
      i'.msgVal tr t r' pub = i.msgVal tr t r pub ∧ i'.multNat tr t r' pub ≠ 0 := by
  have h1 := tableBusCount_pos hr hi ha
  rw [hb, hs, ← hM] at h1
  obtain ⟨r', hr', i', hi', hb', hs', hm', ha'⟩ := exists_of_tableBusCount h1
  exact ⟨r', hr', i', mem_senders B hB hi' hb' hs', hm', ha'⟩

/-- If every active write with message `m` is the same pair, two active reads with message `m`
are the same pair. -/
theorem read_unique (B : Buses) (hB : B.ok) (hM : MemBal B tr t pub) {m : List Fp}
    (hw : ∀ r1 i1 r2 i2, r1 < tr.height t → r2 < tr.height t → (i1 = iMinit B ∨ i1 = iMW2 B) →
      (i2 = iMinit B ∨ i2 = iMW2 B) → i1.msgVal tr t r1 pub = m → i2.msgVal tr t r2 pub = m →
      i1.multNat tr t r1 pub ≠ 0 → i2.multNat tr t r2 pub ≠ 0 → r1 = r2 ∧ i1 = i2)
    {r1 r2 : Nat} {i1 i2 : Interaction} (hr1 : r1 < tr.height t) (hr2 : r2 < tr.height t)
    (hi1 : i1 ∈ B.is) (hi2 : i2 ∈ B.is) (hb1 : i1.bus = B.mem) (hb2 : i2.bus = B.mem)
    (hs1 : i1.send = false) (hs2 : i2.send = false)
    (hm1 : i1.msgVal tr t r1 pub = m) (hm2 : i2.msgVal tr t r2 pub = m)
    (ha1 : i1.multNat tr t r1 pub ≠ 0) (ha2 : i2.multNat tr t r2 pub ≠ 0) : r1 = r2 ∧ i1 = i2 := by
  -- the send count of `m` is at most one
  obtain ⟨rw, hrw, iw, hiw, hmw, haw⟩ := exists_write B hB hM hr1 hi1 hb1 hs1 ha1
  have hle : tableBusCount B.is tr t pub B.mem true m ≤ 1 := by
    apply tableBusCount_le_one (is_nodup B) (is_mult B) rw iw
    intro r hr i hi hb hs hm ha
    have hi' := mem_senders B hB hi hb hs
    exact hw r i rw iw hr hrw hi' hiw hm (by rw [hmw, hm1]) ha haw
  rw [hM] at hle
  apply Classical.byContradiction
  intro hne
  have hne' : r1 ≠ r2 ∨ i1 ≠ i2 := by
    by_cases e : r1 = r2
    · exact Or.inr (fun h => hne ⟨e, h⟩)
    · exact Or.inl e
  have := tableBusCount_ge_two (is_nodup B) hr1 hr2 hi1 hi2 hne' hb1 hs1 hm1 ha1 hb2 hs2 hm2 ha2
  omega

end ZkFormal.Chacha.Shuffle
