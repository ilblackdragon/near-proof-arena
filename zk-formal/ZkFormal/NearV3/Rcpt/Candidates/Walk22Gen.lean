/- Candidate log22 generalization of Render/WalkGen.lean. Frozen renderer unchanged;
all cells and interactions retain their original definitions. -/
import ZkFormal.Near.Render.Proof.MrkRecs
import ZkFormal.NearV3.Extract.WalkProof2

/-!
# ZkFormal.NearV3.Render.WalkGen — honest rows of the `walkV3` table

Completeness side of `walkV3` (`Tables/Walk.lean`), after v1 `Near/Render/Walk.lean`.

Input: the walks as the view sees them (`WalkR`, `Extract/WalkView.lean`); the honest
input predicate `WalkOk` is `WalkWf3` plus a nonempty list and the row cap `2^22`.

Rows: the records `(wv, j)` (walk, step index) in table order (`WalkGen.recs`), then
zero padding.  Row `(wv, j)` with step `s = wv.step j`, `n = |wv.steps|`:
`act = 1`, `ws = [j = 0]`, `we = [j + 1 = n]`, `gK = [j ≠ 0]`, `w`, `τ`, `t = j − 1`
(`0` on the `START` row), `sym`, the edge `e = [N, I, nib, N2, I2, ek]`, `u`, the mode
one-hot `mS mK mB mD`, `inv = (sym − nib)⁻¹` on mode 1 (else `0`), `hv` on mode 2 (else
`0`), `ub`, `fk`/`kk` = the walk's `fk`/`k` on the last row (else `0`), `bmb` = the bits of
`bm` on mode 2 (else `0`), `sel` = one-hot of `sym` on mode-2 non-last rows (else `0`).
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.Candidates.Walk22Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra

/-- Number of rows of the walks. -/
def rows (ws : List WalkR) : Nat := (ws.map fun wv => wv.steps.length).sum

/-- What the honest `walkV3` trace needs: the view's well-formedness, at least one walk, and
the row cap. -/
structure WalkOk (ws : List WalkR) : Prop where
  wf : WalkWf3 ws
  pos : 0 < ws.length
  cap : rows ws ≤ 2 ^ 22

namespace WalkGen

/-- A row record: walk and step index. -/
abbrev Rec := WalkR × Nat

/-- The row records in table order. -/
def recs (ws : List WalkR) : List Rec :=
  ws.flatMap fun wv => (List.range wv.steps.length).map fun j => (wv, j)

def stp (p : Rec) : WStep3 := p.1.step p.2

/-- `(sym − nib)⁻¹` in `Fp` (as a canonical natural). -/
def invOf (s : WStep3) : Nat := (Fp.ofNat s.sym - Fp.ofNat (s.e.getD 2 0))⁻¹.toNat

/-- Cells of the row of record `p`. -/
def rowCell (p : Rec) : Nat → Nat
  | 0 => 1
  | 1 => if p.2 = 0 then 1 else 0
  | 2 => if p.2 + 1 = p.1.steps.length then 1 else 0
  | 3 => if p.2 = 0 then 0 else 1
  | 4 => p.1.w
  | 5 => p.1.tau
  | 6 => p.2 - 1
  | 7 => (stp p).sym
  | 8 => (stp p).e.getD 0 0
  | 9 => (stp p).e.getD 1 0
  | 10 => (stp p).e.getD 2 0
  | 11 => (stp p).e.getD 3 0
  | 12 => (stp p).e.getD 4 0
  | 13 => (stp p).e.getD 5 0
  | 14 => (stp p).u
  | 15 => if (stp p).mode = 0 then 1 else 0
  | 16 => if (stp p).mode = 1 then 1 else 0
  | 17 => if (stp p).mode = 2 then 1 else 0
  | 18 => if (stp p).mode = 3 then 1 else 0
  | 19 => if (stp p).mode = 1 then invOf (stp p) else 0
  | 20 => if (stp p).mode = 2 then (stp p).hv else 0
  | 21 => (stp p).ub
  | 22 => if p.2 + 1 = p.1.steps.length then p.1.fk else 0
  | 23 => if p.2 + 1 = p.1.steps.length then p.1.k else 0
  | j + 24 =>
    if j < 16 then (if (stp p).mode = 2 then (stp p).bm / 2 ^ j % 2 else 0)
    else if j < 32 then
      (if (stp p).mode = 2 ∧ ¬ p.2 + 1 = p.1.steps.length ∧ (stp p).sym = j - 16 then 1 else 0)
    else 0

/-- The cell of row `q`, column `col` (`H` is the table height; padding rows are zero). -/
def cell (ws : List WalkR) (_H q col : Nat) : Nat :=
  if q < rows ws then rowCell ((recs ws).getD q default) col else 0

end WalkGen

/-- The honest `walkV3` rows. -/
def walkRows (ws : List WalkR) : Array Row :=
  mkTab (2 ^ logOf (rows ws)) WalkV3.width (WalkGen.cell ws (2 ^ logOf (rows ws)))

/-! ## The records -/

namespace WalkGen

/-- Consecutive records: next step of the same walk, or first step of a new walk after the
last step of a walk. -/
def RAdj (a b : Rec) : Prop :=
  (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (a.2 + 1 = a.1.steps.length ∧ b.2 = 0)

theorem recs_length (ws : List WalkR) : (recs ws).length = rows ws := by
  induction ws with
  | nil => rfl
  | cons wv ws ih => simp [recs, rows] at ih ⊢; (try rw [← ih])

theorem recs_mem {ws : List WalkR} {p : Rec} (h : p ∈ recs ws) : p.1 ∈ ws ∧ p.2 < p.1.steps.length := by
  simp only [recs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨wv, hw, j, hj, rfl⟩ := h
  exact ⟨hw, hj⟩

theorem recs_getD_mem {ws : List WalkR} {q : Nat} (hq : q < rows ws) : (recs ws).getD q default ∈ recs ws := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [recs_length]; exact hq)]
  exact List.getElem_mem _

theorem recs_adj (ws : List WalkR) (hlen : ∀ wv ∈ ws, 1 ≤ wv.steps.length) : Adj2 RAdj (recs ws) := by
  apply Adj2.flatMap
  · intro wv _
    apply Adj2.of_get
    intro q hq
    simp only [List.length_map, List.length_range] at hq
    simp [RAdj]
  · apply Adj2.of_get
    intro q hq a b ha hb
    right
    obtain ⟨m, hm⟩ : ∃ m, ws[q].steps.length = m + 1 :=
      ⟨ws[q].steps.length - 1, by have := hlen _ (List.getElem_mem (show q < ws.length by omega)); omega⟩
    obtain ⟨m', hm'⟩ : ∃ m, ws[q + 1].steps.length = m + 1 :=
      ⟨ws[q + 1].steps.length - 1, by have := hlen _ (List.getElem_mem hq); omega⟩
    rw [hm, List.range_succ, List.map_append] at ha
    rw [hm', List.range_succ_eq_map] at hb
    simp at ha hb
    subst ha hb
    simp [hm]
  · intro wv hw h
    have := hlen wv hw
    simp only [List.map_eq_nil_iff, List.range_eq_nil] at h; omega

theorem recs_head {ws : List WalkR} (hpos : 0 < ws.length) (hlen : ∀ wv ∈ ws, 1 ≤ wv.steps.length) :
    ((recs ws).getD 0 default).2 = 0 := by
  cases ws with
  | nil => simp at hpos
  | cons wv ws =>
    have h := hlen wv (by simp)
    simp only [recs, List.flatMap_cons]
    obtain ⟨n, hn⟩ : ∃ n, wv.steps.length = n + 1 := ⟨wv.steps.length - 1, by omega⟩
    rw [hn, List.range_succ_eq_map]
    simp

theorem recs_last {ws : List WalkR} (hpos : 0 < ws.length) (hlen : ∀ wv ∈ ws, 1 ≤ wv.steps.length) :
    ((recs ws).getD (rows ws - 1) default).2 + 1 = ((recs ws).getD (rows ws - 1) default).1.steps.length := by
  have hne : ws ≠ [] := by intro h; subst h; simp at hpos
  obtain ⟨ws', wl, hws⟩ : ∃ ws' wl, ws = ws' ++ [wl] :=
    ⟨ws.dropLast, ws.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  have hl := hlen wl (by simp [hws])
  obtain ⟨m, hm⟩ : ∃ m, wl.steps.length = m + 1 := ⟨wl.steps.length - 1, by omega⟩
  have hr : rows ws = rows ws' + wl.steps.length := by simp [rows, hws]
  have hrw : recs ws = recs ws' ++ (List.range wl.steps.length).map fun j => (wl, j) := by
    simp [recs, hws]
  rw [hrw, hr, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [recs_length]; omega)]
  rw [recs_length, show rows ws' + wl.steps.length - 1 - rows ws' = m by omega, hm, List.range_succ,
    List.map_append, List.getElem?_append_right (by simp)]
  simp [hm]

/-! ## Per-row facts of an honest input -/

/-- The bits of `x` below `2^n`. -/
theorem bits_sum (x : Nat) : ∀ n, ((List.range n).map fun j => 2 ^ j * (x / 2 ^ j % 2)).sum = x % 2 ^ n
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, bits_sum x n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.pow_succ, Nat.mod_mul]

variable {ws : List WalkR} (hok : WalkOk ws)
include hok

theorem len2 {wv : WalkR} (hw : wv ∈ ws) : 2 ≤ wv.steps.length := hok.wf.len wv hw

theorem len1 : ∀ wv ∈ ws, 1 ≤ wv.steps.length := fun wv hw => by have := len2 hok hw; omega

theorem step_eq {wv : WalkR} {j : Nat} (hj : j < wv.steps.length) : wv.step j = wv.steps[j] := by
  simp [WalkR.step, List.getD_eq_getElem?_getD, hj]

theorem stepOk {p : Rec} (hp : p ∈ recs ws) : StepOk (stp p) (p.2 + 1 == p.1.steps.length) := by
  obtain ⟨hw, hj⟩ := recs_mem hp
  rw [stp, step_eq hok hj]
  exact hok.wf.rows _ hw _ hj

theorem canonR {p : Rec} (hp : p ∈ recs ws) :
    p.1.w < ZkFormal.Algebra.P ∧ p.1.tau < ZkFormal.Algebra.P ∧ (stp p).sym < ZkFormal.Algebra.P ∧
      ∀ x ∈ (stp p).e, x < ZkFormal.Algebra.P := by
  obtain ⟨hw, hj⟩ := recs_mem hp
  have h := hok.wf.canon _ hw
  have hs := h.2.2 (stp p) (by rw [stp, step_eq hok hj]; exact List.getElem_mem _)
  exact ⟨h.1, h.2.1, hs.1, hs.2.2.2⟩

/-- Unpacked facts of an honest row record (constants as numerals). -/
structure RowF (p : Rec) : Prop where
  j_lt : p.2 < p.1.steps.length
  n2 : 2 ≤ p.1.steps.length
  mode : (stp p).mode ≤ 3
  elen : (stp p).e.length = 6
  stepE : (stp p).mode = 0 → (stp p).e.getD 2 0 = (stp p).sym ∧
    (¬ p.2 + 1 = p.1.steps.length → (stp p).e.getD 5 0 = 0 ∨ (stp p).e.getD 5 0 = 1) ∧
    (p.2 + 1 = p.1.steps.length → (stp p).e.getD 5 0 = 2)
  absK : (stp p).mode = 1 → ((stp p).e.getD 5 0 = 1 ∨ (stp p).e.getD 5 0 = 3) ∧ (stp p).e.getD 2 0 ≠ (stp p).sym
  absB : (stp p).mode = 2 → (stp p).e.getD 1 0 = 0 ∧ (stp p).bm < 2 ^ 16 ∧ (stp p).hv ≤ 1 ∧
    (p.2 + 1 = p.1.steps.length → (stp p).hv = 0) ∧
    (¬ p.2 + 1 = p.1.steps.length → (stp p).sym < 16 ∧ (stp p).bm / 2 ^ (stp p).sym % 2 = 0)
  lastEnd : p.2 + 1 = p.1.steps.length → (stp p).sym = 16
  start : p.2 = 0 → (stp p).mode = 0 ∧ (stp p).sym = 18 ∧ (stp p).e.getD 1 0 = p.1.tau
  lastEq : p.2 + 1 = p.1.steps.length → p.1.last = stp p
  canon : p.1.w < ZkFormal.Algebra.P ∧ p.1.tau < ZkFormal.Algebra.P ∧ (stp p).sym < ZkFormal.Algebra.P ∧
    ∀ x ∈ (stp p).e, x < ZkFormal.Algebra.P

theorem rowF {p : Rec} (hp : p ∈ recs ws) : RowF p := by
  obtain ⟨hw, hj⟩ := recs_mem hp
  have so := stepOk hok hp
  have hst := hok.wf.start _ hw
  by_cases hl : p.2 + 1 = p.1.steps.length
  · have so' : StepOk (stp p) true := by simpa [hl] using so
    refine ⟨hj, len2 hok hw, so'.mode, so'.elen, fun h => ?_, fun h => ?_, fun h => ?_, fun _ => so'.lastEnd rfl,
      fun h0 => ?_, fun _ => ?_, canonR hok hp⟩
    · have := so'.stepE h; simp only [EK_VAL] at this; exact ⟨this.1, fun h' => absurd hl h', fun _ => this.2.2 trivial⟩
    · have := so'.absK h; simp only [EK_KEY, EK_LEND] at this; exact this
    · have := so'.absB h; exact ⟨this.1, this.2.1, this.2.2.1, fun _ => this.2.2.2.1 rfl, fun h' => absurd hl h'⟩
    · have := len2 hok hw; omega
    · simp only [WalkR.last, stp]; congr 1; omega
  · have hb : (p.2 + 1 == p.1.steps.length) = false := by simp [hl]
    have so' : StepOk (stp p) false := by rw [hb] at so; exact so
    refine ⟨hj, len2 hok hw, so'.mode, so'.elen, fun h => ?_, fun h => ?_, fun h => ?_, fun h' => absurd h' hl,
      fun h0 => ?_, fun h' => absurd h' hl, canonR hok hp⟩
    · have := so'.stepE h; simp only [EK_DOWN, EK_KEY] at this
      exact ⟨this.1, fun _ => this.2.1 trivial, fun h' => absurd h' hl⟩
    · have := so'.absK h; simp only [EK_KEY, EK_LEND] at this; exact this
    · have := so'.absB h; exact ⟨this.1, this.2.1, this.2.2.1, fun h' => absurd h' hl, fun _ => this.2.2.2.2 rfl⟩
    · simp only [stp, h0]; simp only [SYM_START] at hst; exact hst

/-- Same-walk successor record: the chain facts. -/
theorem chainF {p p' : Rec} (hp : p ∈ recs ws) (h1 : p'.1 = p.1) (h2 : p'.2 = p.2 + 1)
    (hlt : p.2 + 1 < p.1.steps.length) :
    ((stp p).mode = 0 → (stp p').e.getD 0 0 = (stp p).e.getD 3 0 ∧ (stp p').e.getD 1 0 = (stp p).e.getD 4 0 ∧
      (stp p').mode ≠ 3) ∧
    ((stp p).mode ≠ 0 → (stp p').mode = 3) := by
  obtain ⟨hw, hj⟩ := recs_mem hp
  have hc := hok.wf.chain _ hw p.2 hlt
  have hst : stp p' = p.1.step (p.2 + 1) := by simp only [stp, h1, h2]
  rw [hst]
  refine ⟨fun h => ?_, hc.2⟩
  obtain ⟨he, hm⟩ := hc.1 h
  have e0 := congrArg (fun l => l.getD 0 0) he
  have e1 := congrArg (fun l => l.getD 1 0) he
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop] at e0 e1
  simp only [stp, List.getD_eq_getElem?_getD]
  exact ⟨by simpa using e0, by simpa using e1, hm⟩

end WalkGen

end ZkFormal.NearV3.Candidates.Walk22Render
