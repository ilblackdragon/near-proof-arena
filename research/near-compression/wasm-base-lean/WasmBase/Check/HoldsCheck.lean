import WasmBase.Main.SegSha
/-!
# WasmBase.Check.HoldsCheck — a sound executable checker for `Holds` / `HoldsX` / `ChipIf` (E2E M4c NV)

**Why.**  In M4b every theorem stated from `Holds (wasmBaseSegAir …)` turned out vacuous: the
relation is unsatisfiable (`SegSha.seg_holds_false`).  A soundness theorem whose AIR relation no
honest trace satisfies proves nothing.  This file gives a **kernel-proved sound Boolean checker**
for the relations lane A's soundness theorems assume, so that running it on an honest prover trace
(`wasmbase-tool holds …`, `Check/TraceDump.lean`) is a machine-checked **non-vacuity witness**:
`checkHoldsX A pub ct = true` *is* a proof (by `checkHoldsX_sound`) that the concrete trace
`ct.toTrace` satisfies `HoldsX A pub`.

* `CTrace` — a concrete finite trace: per table its height, width and row-major cells
  (`Array F`); `CTrace.toTrace` is its `Trace` (cells outside the matrix read 0).
* `checkHolds` / `checkHoldsX` — publics length, heights in `[4, 2^24]`, every constraint on every
  row, `busLoad < P` for every bus an interaction mentions (every other bus has load 0), and the
  per-bus mod-p balance: the nonzero-count occurrences are sorted by `(bus, message)`
  (`List.mergeSort`, any comparator) and scanned (`scan`) once, checking each run's
  `Σ sends ≡ Σ receives (mod p)`.  Soundness of the scan needs **no** sortedness (a run is checked
  whenever the key changes; equal keys split over several runs are each balanced, so their sum is),
  only that sorting is a permutation (`List.mergeSort_perm`).  Sorting makes it complete.
* `checkSeg` — one scan over the chip's sends (count 1, bus 103) **plus** the Lean occurrences:
  `checkSeg_sound` gives `HoldsX A pub ct.toTrace ∧ ChipIf compressW A pub ct.toTrace (chipOf comps)`
  for the chip's compression list `comps` (cid, h, block), with the chip's messages *computed* from
  the Lean SHA-512 compression `compressW`, so the dump's chip inputs are re-hashed by the spec.

Soundness theorems: `checkHolds_sound`, `checkHoldsX_sound`, `checkSeg_sound`.  The proofs use
only the definitions (no `native_decide`); running the compiled checker is the executable part.
-/

namespace WasmBase
namespace HoldsCheck

open ZkFormal.Algebra StateM5a.Sha512If
set_option linter.unusedSimpArgs false

/-! ## Concrete traces -/

/-- One table of a concrete trace: height, width and row-major cells. -/
structure CTable where
  height : Nat
  width : Nat
  data : Array F

/-- A concrete finite trace (tables in AIR order). -/
structure CTrace where
  tabs : Array CTable

/-- The `Trace` of a concrete trace (heights 0 / cells 0 outside the dump). -/
def CTrace.toTrace (ct : CTrace) : Trace where
  height t := if h : t < ct.tabs.size then ct.tabs[t].height else 0
  cell t r c := if h : t < ct.tabs.size then
      (if c < ct.tabs[t].width then ct.tabs[t].data.getD (r * ct.tabs[t].width + c) 0 else 0)
    else 0

/-! ## Bus sums over an occurrence list -/

/-- `busNat`'s sum over an arbitrary occurrence list. -/
def bsum (l : List Occ) (b : Nat) (s : Bool) (m : List F) : Nat :=
  ((l.filter fun o => o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m).map (·.2.2.2)).sum

theorem busNat_eq_bsum (A : Air) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) (m : List F) :
    busNat A tr pub b s m = bsum (occs A tr pub) b s m := rfl

theorem bsum_nil (b : Nat) (s : Bool) (m : List F) : bsum [] b s m = 0 := rfl

theorem bsum_cons (o : Occ) (l : List Occ) (b : Nat) (s : Bool) (m : List F) :
    bsum (o :: l) b s m = (if o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m then o.2.2.2 else 0) + bsum l b s m := by
  unfold bsum
  rw [List.filter_cons]
  by_cases h : o.1 = b ∧ o.2.1 = s ∧ o.2.2.1 = m
  · simp only [h, and_self, decide_true, ite_true, List.map_cons, List.sum_cons]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, Nat.zero_add]

theorem bsum_append (l l' : List Occ) (b : Nat) (s : Bool) (m : List F) :
    bsum (l ++ l') b s m = bsum l b s m + bsum l' b s m := by
  unfold bsum; rw [List.filter_append, List.map_append, List.sum_append]

theorem bsum_perm {l l' : List Occ} (h : l.Perm l') (b : Nat) (s : Bool) (m : List F) :
    bsum l b s m = bsum l' b s m :=
  ((h.filter _).map _).sum_nat

theorem bsum_filter_nz (l : List Occ) (b : Nat) (s : Bool) (m : List F) :
    bsum (l.filter fun o => o.2.2.2 != 0) b s m = bsum l b s m := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    rw [List.filter_cons]
    by_cases h0 : o.2.2.2 = 0
    · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ite_false, ih, bsum_cons]; simp
    · have : (o.2.2.2 != 0) = true := by simpa using h0
      rw [if_pos this, bsum_cons, bsum_cons, ih]

/-! ## The balance scan -/

/-- Scan a list of occurrences grouped by key `(bus, message)`; `sn`/`rc` accumulate the current
run's send/receive counts; a run is closed (and checked, unless its bus is skipped) whenever the
key changes and at the end.  Tail-recursive. -/
def scan (skip : Nat → Bool) : List Occ → Nat → List F → Nat → Nat → Bool
  | [], kb, _, sn, rc => skip kb || sn % P == rc % P
  | o :: l, kb, km, sn, rc =>
    if o.1 == kb && o.2.2.1 == km then
      scan skip l kb km (if o.2.1 then sn + o.2.2.2 else sn) (if o.2.1 then rc else rc + o.2.2.2)
    else if skip kb || sn % P == rc % P then
      scan skip l o.1 o.2.2.1 (if o.2.1 then o.2.2.2 else 0) (if o.2.1 then 0 else o.2.2.2)
    else false

theorem scan_sound (skip : Nat → Bool) :
    ∀ (l : List Occ) (kb : Nat) (km : List F) (sn rc : Nat), scan skip l kb km sn rc = true →
      ∀ b m, skip b = false →
        ((if kb = b ∧ km = m then sn else 0) + bsum l b true m) % P =
          ((if kb = b ∧ km = m then rc else 0) + bsum l b false m) % P := by
  intro l
  induction l with
  | nil =>
    intro kb km sn rc h b m hs
    simp only [scan, Bool.or_eq_true, beq_iff_eq] at h
    simp only [bsum_nil, Nat.add_zero]
    by_cases hk : kb = b ∧ km = m
    · rw [if_pos hk, if_pos hk]
      rcases h with h | h
      · rw [hk.1, hs] at h; exact absurd h (by decide)
      · exact h
    · rw [if_neg hk, if_neg hk]
  | cons o l ih =>
    intro kb km sn rc h b m hs
    obtain ⟨ob, os, om, oc⟩ := o
    rw [bsum_cons, bsum_cons]
    simp only [scan] at h
    by_cases hsame : ob = kb ∧ om = km
    · obtain ⟨rfl, rfl⟩ := hsame
      simp only [beq_self_eq_true, Bool.and_self, ite_true] at h
      have := ih ob om _ _ h b m hs
      by_cases hk : ob = b ∧ om = m
      · obtain ⟨rfl, rfl⟩ := hk
        cases os <;> simpa [Nat.add_assoc] using this
      · have h1 : ¬ (ob = b ∧ os = true ∧ om = m) := fun ⟨a, _, c⟩ => hk ⟨a, c⟩
        have h2 : ¬ (ob = b ∧ os = false ∧ om = m) := fun ⟨a, _, c⟩ => hk ⟨a, c⟩
        simpa only [hk, h1, h2, ite_false, Nat.zero_add] using this
    · have hne : (ob == kb && om == km) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        by_cases h1 : ob = kb
        · exact Or.inr fun h2 => hsame ⟨h1, h2⟩
        · exact Or.inl h1
      rw [hne] at h
      simp only [Bool.false_eq_true, ite_false] at h
      split at h
      · rename_i hrun
        have := ih ob om _ _ h b m hs
        by_cases hk : kb = b ∧ km = m
        · -- the closed run is the target key; `o` is not
          obtain ⟨rfl, rfl⟩ := hk
          have hok : sn % P = rc % P := by
            simp only [Bool.or_eq_true, beq_iff_eq] at hrun
            rcases hrun with h' | h'
            · rw [hs] at h'; exact absurd h' (by decide)
            · exact h'
          have h1 : ¬ (ob = kb ∧ os = true ∧ om = km) := fun ⟨a, _, c⟩ => hsame ⟨a, c⟩
          have h2 : ¬ (ob = kb ∧ os = false ∧ om = km) := fun ⟨a, _, c⟩ => hsame ⟨a, c⟩
          simp only [hsame, h1, h2, ite_false, Nat.zero_add, and_self, ite_true] at this ⊢
          rw [Nat.add_mod, hok, this, ← Nat.add_mod]
        · by_cases ho : ob = b ∧ om = m
          · obtain ⟨rfl, rfl⟩ := ho
            cases os <;> simpa [hk] using this
          · have h1 : ¬ (ob = b ∧ os = true ∧ om = m) := fun ⟨a, _, c⟩ => ho ⟨a, c⟩
            have h2 : ¬ (ob = b ∧ os = false ∧ om = m) := fun ⟨a, _, c⟩ => ho ⟨a, c⟩
            simpa only [hk, ho, h1, h2, ite_false, Nat.zero_add] using this
      · exact absurd h (by decide)

/-- Lexicographic order on messages (any comparator is sound; this one makes the scan complete). -/
def msgLe : List F → List F → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.toNat < b.toNat then true else if a.toNat = b.toNat then msgLe as bs else false

/-- Occurrence order: by bus, then message. -/
def occLe (x y : Occ) : Bool :=
  if x.1 < y.1 then true else if x.1 = y.1 then msgLe x.2.2.1 y.2.2.1 else false

/-- **The balance check** of an occurrence list: drop zero counts, sort, scan. -/
def checkBal (skip : Nat → Bool) (l : List Occ) : Bool :=
  scan skip ((l.filter fun o => o.2.2.2 != 0).mergeSort occLe) 0 [] 0 0

theorem checkBal_sound {skip : Nat → Bool} {l : List Occ} (h : checkBal skip l = true) :
    ∀ b m, skip b = false → bsum l b true m % P = bsum l b false m % P := by
  intro b m hs
  have := scan_sound skip _ 0 [] 0 0 h b m hs
  simp only [ite_self, Nat.zero_add] at this
  rwa [bsum_perm (List.mergeSort_perm _ _), bsum_perm (List.mergeSort_perm _ _),
    bsum_filter_nz, bsum_filter_nz] at this

/-! ## Constraints, heights, bus loads -/

/-- Every constraint of every table vanishes on every row. -/
def checkConstr (A : Air) (pub : List F) (tr : Trace) : Bool :=
  (List.range A.tables.length).all fun t =>
    match A.tables[t]? with
    | none => true
    | some T => (List.range (tr.height t)).all fun r => T.constraints.all fun e => e.eval (tr.row pub t r) == 0

theorem checkConstr_sound {A : Air} {pub : List F} {tr : Trace} (h : checkConstr A pub tr = true) :
    ∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
      ∀ e ∈ (A.tables[t]'ht).constraints, e.eval (tr.row pub t r) = 0 := by
  intro t ht r hr e he
  have h1 := List.all_eq_true.mp h t (List.mem_range.mpr ht)
  rw [List.getElem?_eq_getElem ht] at h1
  simp only at h1
  have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
  have h3 := List.all_eq_true.mp h2 e he
  simpa using h3

/-- Heights in `[4, 2^maxLogHeight]`. -/
def checkHeights (A : Air) (tr : Trace) : Bool :=
  (List.range A.tables.length).all fun t => 4 ≤ tr.height t && tr.height t ≤ 2 ^ maxLogHeight

theorem checkHeights_sound {A : Air} {tr : Trace} (h : checkHeights A tr = true) :
    (∀ t, t < A.tables.length → 4 ≤ tr.height t) ∧ (∀ t, t < A.tables.length → tr.height t ≤ 2 ^ maxLogHeight) := by
  constructor <;> intro t ht <;> have := List.all_eq_true.mp h t (List.mem_range.mpr ht) <;>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this <;> omega

/-- The buses any interaction of the AIR mentions. -/
def buses (A : Air) : List Nat := (A.tables.flatMap fun T => T.inters.map (·.bus)).eraseDups

theorem busLoad_zero {A : Air} {tr : Trace} {b : Nat} (hb : b ∉ buses A) : busLoad A tr b = 0 := by
  unfold busLoad
  apply sum_eq_zero_of_all
  intro x hx
  obtain ⟨⟨T, t⟩, hT, rfl⟩ := List.mem_map.mp hx
  have hTm : T ∈ A.tables := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hT)
  have : (T.inters.filter (·.bus = b)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro i hi hib
    apply hb
    unfold buses
    rw [List.mem_eraseDups]
    exact List.mem_flatMap.mpr ⟨T, hTm, List.mem_map.mpr ⟨i, hi, by simpa using hib⟩⟩
  simp [this]

/-- `busLoad < P` on every mentioned bus. -/
def checkLoad (A : Air) (tr : Trace) : Bool := (buses A).all fun b => busLoad A tr b < P

theorem checkLoad_sound {A : Air} {tr : Trace} (h : checkLoad A tr = true) : ∀ b, busLoad A tr b < P := by
  intro b
  by_cases hb : b ∈ buses A
  · simpa using List.all_eq_true.mp h b hb
  · rw [busLoad_zero hb]; exact Nat.pos_of_ne_zero (by decide)

/-! ## `Holds` and `HoldsX` -/

/-- Everything but the balance. -/
def checkShape (A : Air) (pub : List F) (tr : Trace) : Bool :=
  pub.length == A.numPub && checkHeights A tr && checkLoad A tr && checkConstr A pub tr

/-- **The `Holds` checker.** -/
def checkHolds (A : Air) (pub : List F) (ct : CTrace) : Bool :=
  checkShape A pub ct.toTrace && checkBal (fun _ => false) (occs A ct.toTrace pub)

/-- **The `HoldsX` checker** (bus `extBus` not balanced). -/
def checkHoldsX (A : Air) (pub : List F) (ct : CTrace) : Bool :=
  checkShape A pub ct.toTrace && checkBal (· == extBus) (occs A ct.toTrace pub)

theorem checkShape_sound {A : Air} {pub : List F} {tr : Trace} (h : checkShape A pub tr = true) :
    pub.length = A.numPub ∧ (∀ t, t < A.tables.length → 4 ≤ tr.height t) ∧
      (∀ t, t < A.tables.length → tr.height t ≤ 2 ^ maxLogHeight) ∧
      (∀ t (ht : t < A.tables.length), ∀ r, r < tr.height t →
        ∀ e ∈ (A.tables[t]'ht).constraints, e.eval (tr.row pub t r) = 0) ∧
      (∀ b, busLoad A tr b < P) := by
  simp only [checkShape, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, (checkHeights_sound h2).1, (checkHeights_sound h2).2, checkConstr_sound h4, checkLoad_sound h3⟩

/-- **Soundness of `checkHolds`.** -/
theorem checkHolds_sound {A : Air} {pub : List F} {ct : CTrace} (h : checkHolds A pub ct = true) :
    Holds A pub ct.toTrace := by
  simp only [checkHolds, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := checkShape_sound h.1
  exact ⟨h1, h2, h3, h4, fun b m => checkBal_sound h.2 b m rfl, h5⟩

/-- **Soundness of `checkHoldsX`.** -/
theorem checkHoldsX_sound {A : Air} {pub : List F} {ct : CTrace} (h : checkHoldsX A pub ct = true) :
    HoldsX A pub ct.toTrace := by
  simp only [checkHoldsX, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := checkShape_sound h.1
  exact ⟨h1, h2, h3, h4, fun b m hb => checkBal_sound h.2 b m (by simpa using hb), h5⟩

/-! ## The chip hypothesis `ChipIf` -/

/-- The chip's bus-103 traffic of a compression list (`cid`, `h`, `block`), computed with the spec
compression `compressW`. -/
def chipOf (comps : List Comp) : List IfMsg := comps.flatMap (chipMsgs SegSha.compressW)

/-- The chip's sends as occurrences (bus 103, send, count 1). -/
def chipOccs (chip : List IfMsg) : List Occ := chip.map fun x => (extBus, true, SegSha.ifF x, 1)

theorem bsum_chipOccs_send (chip : List IfMsg) (m : List F) :
    bsum (chipOccs chip) extBus true m = (chip.map SegSha.ifF).count m := by
  induction chip with
  | nil => rfl
  | cons x chip ih =>
    simp only [chipOccs, List.map_cons] at ih ⊢
    rw [bsum_cons, ih, List.count_cons]
    by_cases h : SegSha.ifF x = m
    · simp [h]; omega
    · simp [h]

theorem bsum_chipOccs_recv (chip : List IfMsg) (m : List F) :
    bsum (chipOccs chip) extBus false m = 0 := by
  induction chip with
  | nil => rfl
  | cons x chip ih =>
    simp only [chipOccs, List.map_cons] at ih ⊢
    rw [bsum_cons, ih]; simp

theorem bsum_chipOccs_other (chip : List IfMsg) {b : Nat} (hb : b ≠ extBus) (s : Bool) (m : List F) :
    bsum (chipOccs chip) b s m = 0 := by
  induction chip with
  | nil => rfl
  | cons x chip ih =>
    simp only [chipOccs, List.map_cons] at ih ⊢
    rw [bsum_cons, ih]
    have : ¬ (extBus = b ∧ true = s ∧ SegSha.ifF x = m) := fun h => hb h.1.symm
    simp only [this, ite_false]

/-- The chip contract's decidable part: distinct `cid`s, input shapes, 64-bit words, `cid < P`. -/
def checkComps (comps : List Comp) : Bool :=
  decide (comps.map Comp.cid).Nodup &&
    comps.all fun c => c.h.length == 8 && c.blk.length == 16 && c.cid < P &&
      c.h.all (· < 2 ^ 64) && c.blk.all (· < 2 ^ 64)

/-- **The segment checker**: `HoldsX` and `ChipIf` with the chip's computed traffic, one scan over
the chip's sends and the Lean occurrences (every bus balanced). -/
def checkSeg (A : Air) (pub : List F) (ct : CTrace) (comps : List Comp) : Bool :=
  checkShape A pub ct.toTrace && checkComps comps &&
    checkBal (fun _ => false) (chipOccs (chipOf comps) ++ occs A ct.toTrace pub)

theorem chipOf_cid {comps : List Comp} (h : ∀ c ∈ comps, c.cid < P) : ∀ x ∈ chipOf comps, x.cid < P := by
  intro x hx
  obtain ⟨c, hc, hx⟩ := List.mem_flatMap.mp hx
  simp only [chipMsgs, List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  exact h c hc

/-- **Soundness of `checkSeg`**: the concrete trace satisfies `HoldsX` and the chip hypothesis
with the chip traffic of `comps`. -/
theorem checkSeg_sound {A : Air} {pub : List F} {ct : CTrace} {comps : List Comp}
    (h : checkSeg A pub ct comps = true) :
    HoldsX A pub ct.toTrace ∧ SegSha.ChipIf SegSha.compressW A pub ct.toTrace (chipOf comps) := by
  simp only [checkSeg, Bool.and_eq_true] at h
  obtain ⟨⟨hs, hc⟩, hb⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := checkShape_sound hs
  have hbal := checkBal_sound hb
  simp only [checkComps, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨hnd, hcs⟩ := hc
  refine ⟨⟨h1, h2, h3, h4, fun b m hx => ?_, h5⟩, ⟨?_, ?_, fun m => ?_⟩⟩
  · have := hbal b m rfl
    rwa [bsum_append, bsum_append, bsum_chipOccs_other _ hx, bsum_chipOccs_other _ hx,
      Nat.zero_add, Nat.zero_add] at this
  · refine ⟨comps, rfl, hnd, fun c hc => ?_⟩
    obtain ⟨⟨⟨⟨e1, e2⟩, -⟩, e4⟩, e5⟩ := hcs c hc
    refine ⟨e1, e2, fun w hw => ?_, fun w hw => ?_⟩
    · exact e4 w hw
    · exact e5 w hw
  · exact chipOf_cid fun c hc => by
      obtain ⟨⟨⟨⟨-, -⟩, e3⟩, -⟩, -⟩ := hcs c hc
      simpa using e3
  · have := hbal extBus m rfl
    rwa [bsum_append, bsum_append, bsum_chipOccs_send, bsum_chipOccs_recv, Nat.zero_add] at this

end HoldsCheck
end WasmBase

#print axioms WasmBase.HoldsCheck.checkBal_sound
#print axioms WasmBase.HoldsCheck.checkHolds_sound
#print axioms WasmBase.HoldsCheck.checkHoldsX_sound
#print axioms WasmBase.HoldsCheck.checkSeg_sound
