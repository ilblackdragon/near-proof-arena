import ZkFormal.NearV3.Extract.Ups.PlanDefs

/-!
# ZkFormal.NearV3.Extract.Ups.IxRow — selector expressions on index rows

`ixRow ci ti di si ki sdi`: a row whose one-hot selectors (case, `I`, `D`, `t*`, kind,
source level) are fixed by indices and every other cell is `0`.  An expression over these
columns only (`IxE e`) has the same `nev` on a real row with these indices (`nev_ix`), and
its value on index rows is checked against a semantic function by `decide +kernel`
(`s15V`, `twoV`, `spY1V`, `spY2V`, `xcpV`, `vcpV`, `ba0V`, `ba1V`, …).
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

def ixRow (ci ti di si ki sdi : Nat) : URow := fun x =>
  if 17 ≤ x ∧ x < 28 then (if x - 17 = ci then 1 else 0)
  else if 28 ≤ x ∧ x < 31 then (if x - 28 = di then 1 else 0)
  else if 31 ≤ x ∧ x < 34 then (if x - 31 = si then 1 else 0)
  else if 34 ≤ x ∧ x < 37 then (if x - 34 = ti then 1 else 0)
  else if 50 ≤ x ∧ x < 61 then (if x - 50 = ki then 1 else 0)
  else if 65 ≤ x ∧ x < 68 then (if x - 65 = sdi then 1 else 0)
  else if x = kPT then (if ki = 11 then 1 else 0)
  else 0

/-- The index columns. -/
def ixCol (x : Nat) : Bool :=
  (17 ≤ x && x < 37) || (50 ≤ x && x < 61) || (65 ≤ x && x < 68) || x == 179

/-- The selectors of a row, as indices. -/
structure IxOf (C : URow) (ci ti di si ki sdi : Nat) : Prop where
  cs : ∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0
  ti : ∀ m, m < 3 → C (34 + m) = if m = ti then 1 else 0
  dd : ∀ m, m < 3 → C (28 + m) = if m = di then 1 else 0
  ts : ∀ m, m < 3 → C (31 + m) = if m = si then 1 else 0
  kd : ∀ m, m < 12 → C (kcol m) = if m = ki then 1 else 0
  sd : ∀ m, m < 3 → C (65 + m) = if m = sdi then 1 else 0

theorem ixAgree {C : URow} {ci ti di si ki sdi : Nat} (h : IxOf C ci ti di si ki sdi) :
    ∀ x, ixCol x = true → C x = ixRow ci ti di si ki sdi x := by
  intro x hx
  simp only [ixCol, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
  unfold ixRow
  by_cases a1 : 17 ≤ x ∧ x < 28
  · rw [if_pos a1]; have := h.cs (x - 17) (by omega); rwa [show 17 + (x - 17) = x by omega] at this
  rw [if_neg a1]
  by_cases a2 : 28 ≤ x ∧ x < 31
  · rw [if_pos a2]; have := h.dd (x - 28) (by omega); rwa [show 28 + (x - 28) = x by omega] at this
  rw [if_neg a2]
  by_cases a3 : 31 ≤ x ∧ x < 34
  · rw [if_pos a3]; have := h.ts (x - 31) (by omega); rwa [show 31 + (x - 31) = x by omega] at this
  rw [if_neg a3]
  by_cases a4 : 34 ≤ x ∧ x < 37
  · rw [if_pos a4]; have := h.ti (x - 34) (by omega); rwa [show 34 + (x - 34) = x by omega] at this
  rw [if_neg a4]
  by_cases a5 : 50 ≤ x ∧ x < 61
  · rw [if_pos a5]; have := h.kd (x - 50) (by omega)
    simp only [kcol, show x - 50 < 11 by omega, ite_true, show 50 + (x - 50) = x by omega] at this
    exact this
  rw [if_neg a5]
  by_cases a6 : 65 ≤ x ∧ x < 68
  · rw [if_pos a6]; have := h.sd (x - 65) (by omega); rwa [show 65 + (x - 65) = x by omega] at this
  rw [if_neg a6]
  have hx' : x = kPT := by rw [kPT_v]; omega
  rw [if_pos hx']; subst hx'; have := h.kd 11 (by omega); simpa [kcol, eq_comm] using this

/-- An expression over index columns only. -/
abbrev IxE (e : Expr) : Prop := (∀ x ∈ e.colsC, ixCol x = true) ∧ e.colsN = []

theorem nev_ix {C D : URow} {ci ti di si ki sdi : Nat} (h : IxOf C ci ti di si ki sdi) {e : Expr} (he : IxE e) :
    nev C D e = nev (ixRow ci ti di si ki sdi) zrow e :=
  nev_congr e (fun x hx => ixAgree h x (he.1 x hx)) (by rw [he.2]; simp)

/-! ## Semantic values of the derived selectors -/

def kdOf (ki : Nat) : UKind := UKind.all.getD ki .RDB
def csOf (ci : Nat) : UCase := UCase.all.getD ci .LP
def b2n (b : Bool) : Nat := if b then 1 else 0

/-- Target slot 15 (last window) of a rewritten branch. -/
def s15V (ki sdi si : Nat) : Nat := b2n ((kdOf ki == .RDB && sdi == 1) || (kdOf ki == .RBI && si != 0))
/-- Two windows in the split branch (the new leaf and the moved node). -/
def twoV (ci : Nat) : Nat := b2n (csOf ci == .LSc || csOf ci == .ESn0 || csOf ci == .ESn1)
def spY1V (ci si ki : Nat) : Nat := b2n (kdOf ki == .SPB && (csOf ci == .LSa || (si == 0 && twoV ci == 1)))
def spY2V (ci si ki : Nat) : Nat := b2n (kdOf ki == .SPB && si != 0 && twoV ci == 1)
def xcpV (ci ki : Nat) : Nat := b2n (kdOf ki == .SPB && (csOf ci == .ESl1 || csOf ci == .ESn1))
def vcpV (ci ki : Nat) : Nat :=
  b2n (kdOf ki == .RDB || kdOf ki == .RBI || kdOf ki == .MVL || (kdOf ki == .SPB && csOf ci == .LSa))
def ba0V (si ki : Nat) : Nat := b2n (kdOf ki == .RBI && si == 0)
def ba1V (si ki : Nat) : Nat := 128 * b2n (kdOf ki == .RBI && si != 0)

/-- The right-hand sides of the derived-selector constraints. -/
def eS15 : Expr := s15E
def eTwo : Expr := twoE
def eSpY1 : Expr := .mul (c kSPB) (.add (c cLSa) (.mul (c ts1) twoE))
def eSpY2 : Expr := .mul (c kSPB) (.mul (not (c ts1)) twoE)
def eXcp : Expr := .mul (c kSPB) (.add (c cESl1) (c cESn1))
def eVcp : Expr := sum [c kRDB, c kRBI, c kMVL, .mul (c kSPB) (c cLSa)]
def eBa0 : Expr := .mul (c kRBI) (c ts1)
def eBa1 : Expr := smul 128 (.mul (c kRBI) (not (c ts1)))

def ixCheck : Bool :=
  (List.range 11).all fun ci => (List.range 3).all fun si => (List.range 12).all fun ki =>
    (List.range 3).all fun sdi =>
      let R := ixRow ci 0 0 si ki sdi
      nev R zrow eS15 == s15V ki sdi si && nev R zrow eTwo == twoV ci && nev R zrow eSpY1 == spY1V ci si ki &&
      nev R zrow eSpY2 == spY2V ci si ki && nev R zrow eXcp == xcpV ci ki && nev R zrow eVcp == vcpV ci ki &&
      nev R zrow eBa0 == ba0V si ki && nev R zrow eBa1 == ba1V si ki

theorem ixCheck_ok : ixCheck = true := by decide +kernel

/-- `ti`, `di` do not matter for these expressions. -/
theorem ixRow_ti_di (ci ti di si ki sdi : Nat) {e : Expr}
    (he : ∀ x ∈ e.colsC, (17 ≤ x ∧ x < 28) ∨ (31 ≤ x ∧ x < 34) ∨ (50 ≤ x ∧ x < 61) ∨ (65 ≤ x ∧ x < 68) ∨ x = 179) :
    nev (ixRow ci ti di si ki sdi) zrow e = nev (ixRow ci 0 0 si ki sdi) zrow e := by
  apply nev_congr e _ (fun _ _ => rfl)
  intro x hx
  have := he x hx
  unfold ixRow
  by_cases a1 : 17 ≤ x ∧ x < 28
  · simp only [a1, and_self, ite_true]
  have b2 : ¬ (28 ≤ x ∧ x < 31) := by omega
  have b4 : ¬ (34 ≤ x ∧ x < 37) := by omega
  simp only [a1, b2, b4, ite_false]

theorem ixVals {C D : URow} {ci ti di si ki sdi : Nat} (h : IxOf C ci ti di si ki sdi)
    (h1 : ci < 11) (h2 : si < 3) (h3 : ki < 12) (h4 : sdi < 3) :
    nev C D eS15 = s15V ki sdi si ∧ nev C D eTwo = twoV ci ∧ nev C D eSpY1 = spY1V ci si ki ∧
    nev C D eSpY2 = spY2V ci si ki ∧ nev C D eXcp = xcpV ci ki ∧ nev C D eVcp = vcpV ci ki ∧
    nev C D eBa0 = ba0V si ki ∧ nev C D eBa1 = ba1V si ki := by
  have hc := ixCheck_ok
  simp only [ixCheck, List.all_eq_true, List.mem_range] at hc
  have := hc ci h1 si h2 ki h3 sdi h4
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := this
  have hI : ∀ e : Expr, IxE e →
      (∀ x ∈ e.colsC, (17 ≤ x ∧ x < 28) ∨ (31 ≤ x ∧ x < 34) ∨ (50 ≤ x ∧ x < 61) ∨ (65 ≤ x ∧ x < 68) ∨ x = 179) →
      nev C D e = nev (ixRow ci 0 0 si ki sdi) zrow e := fun e he hc' => by
    rw [nev_ix (D := D) h he, ixRow_ti_di ci ti di si ki sdi hc']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hI eS15 (by decide) (by decide)]; exact a1
  · rw [hI eTwo (by decide) (by decide)]; exact a2
  · rw [hI eSpY1 (by decide) (by decide)]; exact a3
  · rw [hI eSpY2 (by decide) (by decide)]; exact a4
  · rw [hI eXcp (by decide) (by decide)]; exact a5
  · rw [hI eVcp (by decide) (by decide)]; exact a6
  · rw [hI eBa0 (by decide) (by decide)]; exact a7
  · rw [hI eBa1 (by decide) (by decide)]; exact a8

/-- A kind column on an index row. -/
theorem kcolV {C : URow} {ci ti di si ki sdi : Nat} (h : IxOf C ci ti di si ki sdi) (m : Nat) (hm : m < 12) :
    C (kcol m) = if m = ki then 1 else 0 := h.kd m hm

end ZkFormal.NearV3.UpsRows
