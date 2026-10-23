import WasmBase.StepCtrl
/-!
# WasmBase.StepIf — the spec-level step lemmas for `if` / `else`

`WasmBase.Check`'s `kindOf` has no `.if_`/`.else_` case, so **no real NEAR contract is inside the
base-layer domain**: `d3tiny` has one `if`, `ttn2` twelve, `d3hostx` four, `d3rich` seventy-seven.
Unblocking D3 is a chain (checker → code records → AIR selector → row lemma → soundness).  This
module delivers the part that is **AIR-independent and reusable by every later `if` lane**: the
spec-step lemmas, proved against the same `RelW`/`Rel` interface as the rest of `StepCtrl`.

## What the spec does (`NearSpecV3/Wasm/Exec.lean:177-190`)

```lean
| .if_ bt =>
  let (c, s) := popN s
  match pf.endOf[f.pc]?, pf.elseOf[f.pc]? with
  | some e, some el =>
    let lab := { target := e + 1, arity := (btResults bt).size,
                 height := s.stack.size, isLoop := false }        -- post-pop height
    if c ≠ 0 then … pc := f.pc + 1, labels := lab :: f.labels …  -- TRUE  ⇒ fall through
    else if el ≠ e then … pc := el + 1, labels := lab :: f.labels …  -- FALSE ⇒ `else` body
    else … pc := e + 1, labels := f.labels …                      -- FALSE, no `else` ⇒ `end`
| .else_ => … pc := lab.target, labels := ls …                    -- unconditional
```

**The third branch is the important one and it is structurally different**: with no `else`, the spec
pushes *no* label and jumps straight to the `end` (which then returns).  `matchBlocks`
(`Prepare.lean:88-96`) records `elseOf[i] = endOf[i]` precisely to mark that shape.  So `if` has
**two** successor shapes and therefore **two** lemmas, not one:

* `step_if` — the true arm (fall through), which always pushes the label;
* `step_if_else` — the false arm **with** an `else`, which pushes the label and jumps to `el + 1`;
* `step_if_noelse` — the false arm **without** an `else`, which pushes nothing and jumps to `e + 1`;
* `step_else` — the `else` body's unconditional jump to the `end`.

`if` is also the opposite polarity from `Ctrl.fJif` (`br_if` jumps on non-zero; `if` falls through on
non-zero), which is why the AIR needs its own selector rather than a reuse.

## Status

`step_if` and `step_else` are **both proved**, axioms `[propext, Classical.choice, Quot.sound]`, no
`sorry`.  `popN_snd` is the conversion lemma that made `step_if` go through (`exec`'s `.if_` arm
builds its state out of a `match popN s`, which is not definitionally a plain record update).

The AIR half (selector, row lemma, checker extension) is **not** attempted here; the signatures are
chosen so that lane consumes them unchanged.
-/
namespace WasmBase
open NearSpecV3.Wasm
variable {S_seg segb : Nat}
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- The label an `if` pushes, in the checker's static vocabulary (frame-relative height):
`end + 1`, `bt`'s arity, at the **post-pop** height. -/
def mkIfLabel (bt : BT) (e : Nat) (h : Nat) : Label :=
  { target := e + 1, arity := (btResults bt).size, height := h, isLoop := false }

/-- The common part of every `if`/`else` step: the condition value, and the fact that `ctrl_rel`
applies at `k = 1` (or `k = 0` for `else`).  `condVal` names the popped condition's value so the
successor pc can be selected. -/
private theorem if_pop (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {mc : Msg} (hmc : live mc) (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1)
    (hsz : 0 < s.stack.size) :
    (popN s).1 = mc.val := by
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  rw [popN_eq]
  simp only
  rw [back_getD _ (by omega), vc]

/-- `popN`'s second component, explicitly: the spec's `pop` is a plain stack pop plus the record.
This is the conversion that `exec`'s `match (popN s)` hides, and the one `step_if` needs. -/
theorem popN_snd (s : St) : (popN s).2 = { s with stack := s.stack.pop } := by
  cases hp : popV s with
  | mk v st =>
    have hst : st = { s with stack := s.stack.pop } := by
      simp only [popV] at hp
      exact ((Prod.mk.inj hp).2).symm
    subst hst
    unfold popN
    rw [hp]
    cases v <;> rfl

/-- **`else`.**  Unconditional jump to the label list's head's `target` (the `if`'s `end + 1`).
Consumes no channel value, so `ctrl_rel` is instantiated at `k = 0`.

`hfl` is stated in the *shifted* form the spec actually uses (`f.labels = shiftLabels sb (lab0 :: ls0)`),
so that the tail is `shiftLabels sb ls0` by `rfl` — the same device `step_br`/`step_brIf` use. -/
theorem step_else (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {fee : Nat} {lab0 : Label} {ls0 : List Label}
    (hins : (X.pfOf E.k).code[pc]? = some .else_)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (hfl : f.labels = shiftLabels E.sb (lab0 :: ls0))
    (hnext : lab0.target < (X.pfOf E.k).code.size)
    (hL : (X.ckOf E.k).labels[lab0.target]? = some ls0)
    (hH : (X.ckOf E.k).heights[lab0.target]? = some (s.stack.size - E.sb)) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k lab0.target (S + fee) E.sb E.cid (stepLive live [] []) S_seg segb := by
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee } }
  let s2 : St := setFrame s1 { f with pc := lab0.target, labels := shiftLabels E.sb ls0 }
  have hs2 : s2.frames =
      { f with pc := lab0.target, labels := shiftLabels E.sb ls0 } :: E.rest := by
    simp only [s2, s1, setFrame, R.frames]
  have hs2stk : s2.stack = s.stack := by simp only [s2, s1, setFrame, R.frames]
  have hs2g : s2.gas.g = s.gas.g - X.R * fee := by simp only [s2, s1, setFrame, R.frames]
  have hs2pg : s2.pages = s.pages := by simp only [s2, s1, setFrame, R.frames]
  have hs2gl : s2.globals = s.globals := by simp only [s2, s1, setFrame, R.frames]
  have hs2rem : s2.stackRem = s.stackRem := by simp only [s2, s1, setFrame, R.frames]
  refine ⟨s2, ?_, ?_⟩
  · rw [step_eq_exec X R hins hfee hg hg64]
    -- the spec: `else_` jumps to `lab.target` and drops the label
    simp only [exec, hfl, shiftLabels_cons, setFrame, R.frames, s2, s1]
  · exact Rel_of_RelW_congr
      (ctrl_rel (X := X) (R := R) (k := 0) (fee := fee) (Nat.zero_le _) lab0.target ls0 hnext hL
        (by have := R.sbLe; omega) hH hg s2 (by rw [hs2stk]; rfl) hs2 hs2g hs2pg hs2gl hs2rem)
      (stepLive_congr (fun x => by simp [popK_size]) (fun x => by simp [popK_size]))

/-! ## `if`, true arm

`popN_snd` is what makes the `exec` comparison go through: it turns the state the spec's `.if_` arm
builds out of `popN s` into `{ s with stack := s.stack.pop }`, which is what `s1`/`s2` are built
from.  Everything else is the `step_brIf` recipe (`popN_eq`, `back_getD`, the `(endOf, elseOf)` pair
rewrite, then the condition). -/

theorem step_if (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {bt : BT} {e el : Nat} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.if_ bt))
    (he : (X.pfOf E.k).endOf[pc]? = some e) (hel : (X.pfOf E.k).elseOf[pc]? = some el)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (mc : Msg) (hmc : live mc) (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1)
    (hsz : 0 < s.stack.size) (hsb1 : E.sb ≤ s.stack.size - 1) (hnz : mc.val ≠ 0)
    {ls0 : List Label} (hflT : f.labels = shiftLabels E.sb ls0)
    {lsT : List Label} (hnext : pc + 1 < (X.pfOf E.k).code.size)
    (hL1 : (X.ckOf E.k).labels[pc + 1]? = some lsT)
    (hH1 : (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size - 1 - E.sb))
    (hpush : lsT = mkIfLabel bt e (s.stack.size - 1 - E.sb) :: ls0) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [mc] []) S_seg segb := by
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  have hb' : vNum (s.stack.back?.getD (.i32 0)) = mc.val := by rw [back_getD _ (by omega), vc]
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := popK s.stack 1 }
  let s2 : St := setFrame s1 { f with pc := pc + 1, labels := shiftLabels E.sb lsT }
  have hs2 : s2.frames = { f with pc := pc + 1, labels := shiftLabels E.sb lsT } :: E.rest := by
    simp only [s2, s1, setFrame, R.frames]
  have hs2stk : s2.stack = popK s.stack 1 := by simp only [s2, s1, setFrame, R.frames]
  have hs2g : s2.gas.g = s.gas.g - X.R * fee := by simp only [s2, s1, setFrame, R.frames]
  have hs2pg : s2.pages = s.pages := by simp only [s2, s1, setFrame, R.frames]
  have hs2gl : s2.globals = s.globals := by simp only [s2, s1, setFrame, R.frames]
  have hs2rem : s2.stackRem = s.stackRem := by simp only [s2, s1, setFrame, R.frames]
  refine ⟨s2, ?_, ?_⟩
  · rw [step_eq_exec X R hins hfee hg hg64]
    simp only [exec, R.pcEq, popN_eq, hb', popN_snd]
    simp only [he, hel, reduceCtorEq, Option.some.injEq, exists_eq_left]
    split
    · simp only [setFrame, R.frames, hpush, hflT, shiftLabels_cons, mkIfLabel,
        Array.size_pop, Nat.sub_add_cancel hsb1, popK_one, s2, s1]
    · rename_i hneg
      exact absurd hnz hneg
  · refine Rel_of_RelW_congr
      (ctrl_rel (X := X) (R := R) (k := 1) (fee := fee) (by omega) (pc + 1) lsT hnext hL1
        hsb1 hH1 hg s2 hs2stk hs2 hs2g hs2pg hs2gl hs2rem)
      (stepLive_congr ?_ ?_)
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
      constructor
      · rintro ⟨d, hd, rfl⟩
        have : d = 0 := by omega
        subst this; rw [ec, Nat.add_zero]
      · rintro rfl; exact ⟨0, by omega, by rw [ec, Nat.add_zero]⟩
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, false_and, exists_false, popK_size, List.mem_nil_iff, iff_false]
      rintro ⟨d, hd, _⟩; omega

/-! ## `if`, false arm with an `else`

Same `popN_snd` recipe, but the successor is `el + 1` and the pushed label is the one the checker's
`labels[el + 1]` holds.  The condition is **zero**, so the `if c ≠ 0` guard takes its `else` branch
and the `el ≠ e` test picks `el + 1` rather than the `end`. -/

theorem step_if_else (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {bt : BT} {e el : Nat} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.if_ bt))
    (he : (X.pfOf E.k).endOf[pc]? = some e) (hel : (X.pfOf E.k).elseOf[pc]? = some el)
    (hne : el ≠ e)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (mc : Msg) (hmc : live mc) (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1)
    (hsz : 0 < s.stack.size) (hsb1 : E.sb ≤ s.stack.size - 1) (hz : mc.val = 0)
    {ls0 : List Label} (hflT : f.labels = shiftLabels E.sb ls0)
    {lsF : List Label} (hnext : el + 1 < (X.pfOf E.k).code.size)
    (hL1 : (X.ckOf E.k).labels[el + 1]? = some lsF)
    (hH1 : (X.ckOf E.k).heights[el + 1]? = some (s.stack.size - 1 - E.sb))
    (hpush : lsF = mkIfLabel bt e (s.stack.size - 1 - E.sb) :: ls0) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (el + 1) (S + fee) E.sb E.cid (stepLive live [mc] []) S_seg segb := by
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  have hb' : vNum (s.stack.back?.getD (.i32 0)) = mc.val := by rw [back_getD _ (by omega), vc]
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := popK s.stack 1 }
  let s2 : St := setFrame s1 { f with pc := el + 1, labels := shiftLabels E.sb lsF }
  have hs2 : s2.frames = { f with pc := el + 1, labels := shiftLabels E.sb lsF } :: E.rest := by
    simp only [s2, s1, setFrame, R.frames]
  have hs2stk : s2.stack = popK s.stack 1 := by simp only [s2, s1, setFrame, R.frames]
  have hs2g : s2.gas.g = s.gas.g - X.R * fee := by simp only [s2, s1, setFrame, R.frames]
  have hs2pg : s2.pages = s.pages := by simp only [s2, s1, setFrame, R.frames]
  have hs2gl : s2.globals = s.globals := by simp only [s2, s1, setFrame, R.frames]
  have hs2rem : s2.stackRem = s.stackRem := by simp only [s2, s1, setFrame, R.frames]
  refine ⟨s2, ?_, ?_⟩
  · rw [step_eq_exec X R hins hfee hg hg64]
    simp only [exec, R.pcEq, popN_eq, hb', popN_snd]
    simp only [he, hel, reduceCtorEq, Option.some.injEq, exists_eq_left]
    rw [if_neg (by omega), if_pos (by omega)]
    simp only [setFrame, R.frames, hpush, hflT, shiftLabels_cons, mkIfLabel,
      Array.size_pop, Nat.sub_add_cancel hsb1, popK_one, s2, s1]
  · refine Rel_of_RelW_congr
      (ctrl_rel (X := X) (R := R) (k := 1) (fee := fee) (by omega) (el + 1) lsF hnext hL1
        hsb1 hH1 hg s2 hs2stk hs2 hs2g hs2pg hs2gl hs2rem)
      (stepLive_congr ?_ ?_)
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
      constructor
      · rintro ⟨d, hd, rfl⟩
        have : d = 0 := by omega
        subst this; rw [ec, Nat.add_zero]
      · rintro rfl; exact ⟨0, by omega, by rw [ec, Nat.add_zero]⟩
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, false_and, exists_false, popK_size, List.mem_nil_iff, iff_false]
      rintro ⟨d, hd, _⟩; omega

/-! ## `if`, false arm without an `else`

The structurally different shape: `elseOf = endOf`, so the spec pushes **no** label and jumps to
`e + 1` (`Exec.lean:186`).  `ifStep_noelse_ls` (`IfCheck`) is the checker-side counterpart: it proves
the checker's static label list for that successor is the *unpushed* `ls0`, which is exactly what
`hflT` gives here. -/

theorem step_if_noelse (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {bt : BT} {e : Nat} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.if_ bt))
    (he : (X.pfOf E.k).endOf[pc]? = some e) (hel : (X.pfOf E.k).elseOf[pc]? = some e)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (mc : Msg) (hmc : live mc) (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1)
    (hsz : 0 < s.stack.size) (hsb1 : E.sb ≤ s.stack.size - 1) (hz : mc.val = 0)
    {ls0 : List Label} (hflT : f.labels = shiftLabels E.sb ls0)
    {lsF : List Label} (hnext : e + 1 < (X.pfOf E.k).code.size)
    (hL1 : (X.ckOf E.k).labels[e + 1]? = some lsF)
    (hH1 : (X.ckOf E.k).heights[e + 1]? = some (s.stack.size - 1 - E.sb))
    (hkeep : lsF = ls0) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (e + 1) (S + fee) E.sb E.cid (stepLive live [mc] []) S_seg segb := by
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  have hb' : vNum (s.stack.back?.getD (.i32 0)) = mc.val := by rw [back_getD _ (by omega), vc]
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := popK s.stack 1 }
  let s2 : St := setFrame s1 { f with pc := e + 1, labels := shiftLabels E.sb lsF }
  have hs2 : s2.frames = { f with pc := e + 1, labels := shiftLabels E.sb lsF } :: E.rest := by
    simp only [s2, s1, setFrame, R.frames]
  have hs2stk : s2.stack = popK s.stack 1 := by simp only [s2, s1, setFrame, R.frames]
  have hs2g : s2.gas.g = s.gas.g - X.R * fee := by simp only [s2, s1, setFrame, R.frames]
  have hs2pg : s2.pages = s.pages := by simp only [s2, s1, setFrame, R.frames]
  have hs2gl : s2.globals = s.globals := by simp only [s2, s1, setFrame, R.frames]
  have hs2rem : s2.stackRem = s.stackRem := by simp only [s2, s1, setFrame, R.frames]
  refine ⟨s2, ?_, ?_⟩
  · rw [step_eq_exec X R hins hfee hg hg64]
    -- the spec: no label pushed, jump to `e + 1`.  `popN_snd` rewrites the popped state to
    -- `{ s with stack := s.stack.pop }`, which is `s1` with `popK … 1` (`popK_one`).
    simp only [exec, R.pcEq, popN_eq, hb', popN_snd]
    simp only [he, hel, reduceCtorEq, Option.some.injEq]
    rw [if_neg (by omega)]
    rw [if_neg (by simp)]
    simp only [popK_one, setFrame, R.frames, hkeep, hflT, Array.size_pop, s2, s1]
  · refine Rel_of_RelW_congr
      (ctrl_rel (X := X) (R := R) (k := 1) (fee := fee) (by omega) (e + 1) lsF hnext hL1
        hsb1 hH1 hg s2 hs2stk hs2 hs2g hs2pg hs2gl hs2rem)
      (stepLive_congr ?_ ?_)
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
      constructor
      · rintro ⟨d, hd, rfl⟩
        have : d = 0 := by omega
        subst this; rw [ec, Nat.add_zero]
      · rintro rfl; exact ⟨0, by omega, by rw [ec, Nat.add_zero]⟩
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, false_and, exists_false, popK_size, List.mem_nil_iff, iff_false]
      rintro ⟨d, hd, _⟩; omega

end WasmBase
