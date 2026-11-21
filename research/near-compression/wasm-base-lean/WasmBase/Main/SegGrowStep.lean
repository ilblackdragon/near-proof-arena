import WasmBase.StepOps2
import WasmBase.Main.SegGrowMerkle
import WasmBase.M3Check
/-!
# WasmBase.Main.SegGrowStep — `memory.size` / `memory.grow` against the relation, with the size clause (E2E M6, GROW)

`RelW` (`Event.lean`) has no clause for the memory-size message `[8, 0, 0, pages, 0, 0, 0, tp]`
(channel space 8, MEMG's and SEGG's): a space-8 message is part of the environment's live set
`E.live` and nothing ties it to `s.pages`.  The **size clause** is a state/live-set invariant in the
`Q` slot of the segment induction (`exec_rowsJ`, `Main/SegSigma.lean`):

* `szMsg pg tp` — the message; `SzC s live` — exactly one live space-8 message, and it carries
  `s.pages.size`.

The spec step of a MEMG row, from `RelW` and `SzC` (the row consumes the size message and the top
operand, produces the new size message at its own time, the result, and — on a successful grow — the
zero bytes of any grown addresses it hands to MEMBG):

* `step_memSize`: `memory.size` pushes `pages`; the size message is re-produced unchanged;
* `step_memGrow_ok`: `memory.grow n` with `pages + n ≤ maxMemoryPages` pushes the old size, appends
  `n` zero pages, and every address of `A ⊆ [64 KiB·pages, 64 KiB·(pages + n))` enters the heap view
  as a zero byte produced at `t` (MEMBG's productions, attributed to the grow);
* `step_memGrow_fail`: `pages + n > maxMemoryPages` pushes `2^32 − 1`, memory unchanged;

each with the **linear fee** (`step_eq_exec_grow`: the charge is `R·(fee + lin·n)`, `growFee`'s
reading of the gas entry, `M3Check.lean`), and each re-establishes `SzC` for the post-state.
`straight_rel_envG` is `straight_rel` (`Step.lean`) with the environment's live set changed by
messages outside the stack and the current locals (the size message, the grown bytes) and the
pages allowed to change (`HeapOK` given for the new environment; `HeapOK.grow` builds it after a
grow: the touched set becomes `T ++ A`).  The code facts (instruction, fee entry, straight
successor) are hypotheses, as in `step_conv` (`Main/M2Link.lean`).

## What is open for `seg_sound` of `wasmBaseSegAirG`

* **A `checkModuleM3` context.**  The segment soundness chain is stated for `X : M2Ctx`
  (`checkModuleM2`), whose `memory.grow`/`memory.size` records are the no-chip `0x240`/`0x241`;
  MEMG's FETCH asks for `0x40`/`0x3F` (`checkModuleM3`, `M3Check.lean`), so with an `M2Ctx` an
  active MEMG row has no CODE answer and a grow segment would satisfy the theorem vacuously.  An
  `M3Ctx` (the `M2Ctx` facts for `recordAtM3`, which is `recordAtM2` except at
  `memory.grow`/`memory.size`/HOST-W pcs) supplies the code hypotheses of the lemmas here.
* **The `HoldsXS` layer for the grow AIR.**  `HoldsX (wasmBaseSegAirG …)` does not imply `HoldsXS`:
  MEMG/SEGG/MEMBG/MEMBH add traffic on STATE and CH (and send on R16/BYTE/CODE).  The `seg_sound`
  copies use the STATE/CH balance only through `seg_msgs_permS` (`seg_hstS`, `seg_hchS`); the
  action list becomes `actListM2 ++` MEMG rows, a MEMG row's CH traffic is fused with the MEMBG zero
  bytes of its grow (`membg_grow_link`: every grown block's `tg` is a successful grow row's time),
  `initS`/`finS` gain SEGG's size messages and MEMBH's/MEMBG's blocks.
* **The MEMG row decoding** (its `cons`/`prod` lists as the `step_mem*` lemmas take them) and the
  memory root with MEMBG/MEMBH and the lift (`memRootOf_memGrow`).
-/
namespace WasmBase

open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

variable {S_seg segb : Nat}

/-! ## The size message and the size clause -/

/-- **The memory-size message** (channel space 8, slot 0, tag 0): the page count in limb 0. -/
def szMsg (pg tp : Nat) : Msg := ⟨8, 0, 0, pg, 0, 0, 0, tp⟩

@[simp] theorem szMsg_space (pg tp : Nat) : (szMsg pg tp).space = 8 := rfl

/-- **The size clause**: exactly one live space-8 message, carrying the page count of `s`. -/
def SzC (s : St) (live : Msg → Prop) : Prop :=
  ∃ tz, ∀ x, x.space = 8 → (live x ↔ x = szMsg s.pages.size tz)

theorem SzC.live {s : St} {live : Msg → Prop} (h : SzC s live) : ∃ tz, live (szMsg s.pages.size tz) := by
  obtain ⟨tz, h⟩ := h
  exact ⟨tz, (h _ rfl).mpr rfl⟩

/-- A live size message carries the page count. -/
theorem SzC.pages {s : St} {live : Msg → Prop} (h : SzC s live) {pg tp : Nat} (hl : live (szMsg pg tp)) :
    pg = s.pages.size := by
  obtain ⟨tz, h⟩ := h
  exact congrArg Msg.l0 ((h _ rfl).mp hl)

/-- **A row that neither touches space 8 nor changes the page count keeps the size clause.** -/
theorem SzC.keep {s s' : St} {live : Msg → Prop} {cons prod : List Msg} (h : SzC s live)
    (hc : ∀ x ∈ cons, x.space ≠ 8) (hp : ∀ x ∈ prod, x.space ≠ 8) (hpg : s'.pages.size = s.pages.size) :
    SzC s' (stepLive live cons prod) := by
  obtain ⟨tz, h⟩ := h
  refine ⟨tz, fun x hx => ?_⟩
  rw [hpg, ← h x hx]
  simp only [stepLive]
  constructor
  · rintro (⟨h1, -⟩ | h2)
    · exact h1
    · exact absurd hx (hp x h2)
  · intro h1; exact Or.inl ⟨h1, fun hm => hc x hm hx⟩

/-- The size clause after a row that consumes the live size message and produces `szMsg pg' t`. -/
theorem SzC.swap {s s' : St} {live : Msg → Prop} {cons prod : List Msg} (h : SzC s live) {tz : Nat}
    (hl : live (szMsg s.pages.size tz)) (hcz : szMsg s.pages.size tz ∈ cons)
    {t : Nat} (hp : ∀ x ∈ prod, x.space = 8 → x = szMsg s'.pages.size t)
    (hpz : szMsg s'.pages.size t ∈ prod) :
    SzC s' (stepLive live cons prod) := by
  obtain ⟨tz0, h⟩ := h
  refine ⟨t, fun x hx => ?_⟩
  simp only [stepLive]
  constructor
  · rintro (⟨h1, h2⟩ | h2)
    · have e := (h x hx).mp h1
      have e' := (h _ rfl).mp hl
      rw [← e'] at e
      exact absurd (e ▸ hcz) h2
    · exact hp x h2 hx
  · rintro rfl; exact Or.inr hpz

/-! ## The live set after a step that also changes the environment -/

/-- `stepLive` with environment messages appended to the consumed and produced lists. -/
theorem stepLive_env {live : Msg → Prop} {c1 p1 c2 p2 : List Msg} (hd : ∀ x ∈ p1, x ∉ c2) (x : Msg) :
    stepLive live (c1 ++ c2) (p1 ++ p2) x ↔ (stepLive live c1 p1 x ∧ x ∉ c2) ∨ x ∈ p2 := by
  simp only [stepLive, List.mem_append, not_or]
  constructor
  · rintro (⟨h1, h2, h3⟩ | h | h)
    · exact Or.inl ⟨Or.inl ⟨h1, h2⟩, h3⟩
    · exact Or.inl ⟨Or.inr h, hd x h⟩
    · exact Or.inr h
  · rintro (⟨⟨h1, h2⟩ | h1, h3⟩ | h)
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h)

/-- `{E with live := L}` keeps the frame part of the environment. -/
def Env.withLive (E : Env) (L : Msg → Prop) : Env := { E with live := L }

@[simp] theorem Env.withLive_sb (E : Env) (L : Msg → Prop) : (E.withLive L).sb = E.sb := rfl
@[simp] theorem Env.withLive_cid (E : Env) (L : Msg → Prop) : (E.withLive L).cid = E.cid := rfl
@[simp] theorem Env.withLive_k (E : Env) (L : Msg → Prop) : (E.withLive L).k = E.k := rfl
@[simp] theorem Env.withLive_rest (E : Env) (L : Msg → Prop) : (E.withLive L).rest = E.rest := rfl
@[simp] theorem Env.withLive_lsp (E : Env) (L : Msg → Prop) : (E.withLive L).lsp = E.lsp := rfl
@[simp] theorem Env.withLive_live (E : Env) (L : Msg → Prop) : (E.withLive L).live = L := rfl

/-- **`straight_rel` with an environment change**: the stack/locals part as in `straight_rel`; the
environment's live set becomes `(E.live minus c2) ∪ p2` for messages `c2`, `p2` outside the stack
(space 0) and the current locals, the pages may change, and the new heap view is given. -/
theorem straight_rel_envG (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S fee k : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    (hk : k ≤ s.stack.size) (stk' locs' : Array Val) (J : Option Nat)
    (keep : ∀ i, i < s.stack.size - k → stk'[i]? = s.stack[i]?) (hsz : s.stack.size - k ≤ stk'.size)
    (hnum : ∀ i, i < stk'.size → isNum (stk'[i]?.getD default))
    (lsz : locs'.size = f.locals.size) (lkeep : ∀ j, some j ≠ J → locs'[j]? = f.locals[j]?)
    (hJ : ∀ j, J = some j → j < f.locals.size)
    (lnum : ∀ j, j < locs'.size → isNum (locs'[j]?.getD default))
    (hnext : pc + 1 < (X.pfOf E.k).code.size)
    (hL : ∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls)
    (hsb : E.sb ≤ stk'.size) (hH : (X.ckOf E.k).heights[pc + 1]? = some (stk'.size - E.sb))
    (hgs : X.R * (S + fee - S_seg) ≤ segb)
    (c2 p2 : List Msg) (hc2 : ∀ x ∈ c2, x.space ≠ 0 ∧ x.space ≠ E.lsp ∧ x.space ≠ 4 ∧ x.space ≠ 5 ∧ x.space < 16)
    (hp2 : ∀ x ∈ p2, x.space ≠ 0 ∧ x.space ≠ E.lsp ∧ x.space ≠ 4 ∧ x.space ≠ 5 ∧ x.space < 16)
    (s' : St) (hs'stk : s'.stack = stk') (hs'fr : s'.frames = { f with pc := pc + 1, locals := locs' } :: E.rest)
    (hs'g : s'.gas.g = s.gas.g - X.R * fee)
    (hs'rem : s'.stackRem = s.stackRem)
    (heap' : HeapOK (E.withLive fun x => (E.live x ∧ x ∉ c2) ∨ x ∈ p2) s' (t + 1)) :
    RelW X (E.withLive fun x => (E.live x ∧ x ∉ c2) ∨ x ∈ p2) s' { f with pc := pc + 1, locals := locs' }
      (fun i => if i < s.stack.size - k then tps i else t) (fun j => if some j = J then t else tpl j)
      (t + 1) (pc + 1) (S + fee)
      (stepLive live
        ((((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          J.toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) (tpl j))) ++ c2)
        ((((List.range (stk'.size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
          J.toList.map (fun j => enc E.lsp j (locs'[j]?.getD default) t)) ++ p2)) S_seg segb where
  frames := hs'fr
  kLt := R.kLt
  fn := R.fn
  pcEq := rfl
  pcLt := hnext
  labels := hL
  base := R.base
  sbLe := by rw [hs'stk]; exact hsb
  height := by rw [hs'stk]; exact hH
  nloc := by simp [lsz, R.nloc]
  gas := R.step_gas hgs hs'g
  segLt := by have := R.segLt; omega
  segbLt := R.segbLt
  numS := by rw [hs'stk]; exact hnum
  numL := lnum
  tpsLt := by
    intro i hi
    show (if i < s.stack.size - k then tps i else t) < t + 1
    split
    · have := R.tpsLt i (by omega); omega
    · omega
  tplLt := by
    intro j hj
    show (if some j = J then t else tpl j) < t + 1
    split
    · omega
    · have := R.tplLt j (by simpa [lsz] using hj); omega
  envSep := by
    intro x hx
    rcases hx with ⟨h, -⟩ | h
    · exact R.envSep x h
    · exact ⟨(hp2 x h).1, (hp2 x h).2.1⟩
  entry := R.entry
  sbLt := R.sbLt
  cidLt := R.cidLt
  heap := heap'
  calls := R.calls.mono (by omega) rfl rfl rfl rfl (fun x hx => by
    show ((E.live x ∧ x ∉ c2) ∨ x ∈ p2) ↔ E.live x
    have n2 : x ∉ c2 := fun h => by
      have := hc2 x h; rcases hx with h4 | h5 | h16 <;> omega
    have n3 : x ∉ p2 := fun h => by
      have := hp2 x h; rcases hx with h4 | h5 | h16 <;> omega
    constructor
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact absurd h n3
    · intro h; exact Or.inl ⟨h, n2⟩) hs'rem
  live := by
    intro x
    have hd : ∀ y ∈ (((List.range (stk'.size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
          J.toList.map (fun j => enc E.lsp j (locs'[j]?.getD default) t)), y ∉ c2 := by
      intro y hy hc
      have := hc2 y hc
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.mem_toList] at hy
      rcases hy with ⟨d, _, rfl⟩ | ⟨j, _, rfl⟩
      · exact this.1 rfl
      · exact this.2.1 rfl
    rw [stepLive_env hd, straight_live X R hk stk' locs' J keep hsz lsz lkeep hJ x, hs'stk]
    simp only [Env.withLive_live, Env.withLive_lsp]
    have nst : x ∈ stackView stk' (fun i => if i < s.stack.size - k then tps i else t) → x ∉ c2 ∧ x ∉ p2 := by
      intro h
      obtain ⟨i, -, rfl⟩ := mem_stackView.mp h
      exact ⟨fun hc => (hc2 _ hc).1 rfl, fun hp => (hp2 _ hp).1 rfl⟩
    have nlc : x ∈ localView E.lsp locs' (fun j => if some j = J then t else tpl j) → x ∉ c2 ∧ x ∉ p2 := by
      intro h
      obtain ⟨j, -, rfl⟩ := mem_localView.mp h
      exact ⟨fun hc => (hc2 _ hc).2.1 rfl, fun hp => (hp2 _ hp).2.1 rfl⟩
    constructor
    · rintro (⟨h1 | h1 | h1, h2⟩ | h3)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
      · exact Or.inr (Or.inr (Or.inr h3))
    · rintro (h1 | h1 | ⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨Or.inl h1, (nst h1).1⟩
      · exact Or.inl ⟨Or.inr (Or.inl h1), (nlc h1).1⟩
      · exact Or.inl ⟨Or.inr (Or.inr h1), h2⟩
      · exact Or.inr h3

#print axioms straight_rel_envG

/-! ## The linear charge of `memory.grow` -/

/-- **`step_eq_exec` with `memory.grow`'s linear fee**: the gas entry read by `growFee` (`M3Check`)
charges `R · (fee + lin · n)` for the top operand `n`. -/
theorem step_eq_exec_grow (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {ins : Instr} {fee lin n : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some ins) (hfee : growFee X.cfg (X.pfOf E.k).gas[pc]? = some (fee, lin))
    (htop : NearSpecV3.Wasm.topCount s = n)
    (hg : X.R * (S + (fee + lin * n) - S_seg) ≤ segb) :
    step X.cfg X.p s =
      exec X.cfg X.p { s with gas := { s.gas with g := s.gas.g - X.R * (fee + lin * n) } } f (X.pfOf E.k) ins := by
  have hle62 := R.charge_ok hg
  have hpf : X.p.funcs[f.fn]? = some (X.pfOf E.k) := by rw [R.fn]; exact (X.factsOf R.kLt).func
  have hcode : (X.pfOf E.k).code[f.pc]? = some ins := by rw [R.pcEq]; exact hins
  have hsegb := R.segbLt
  have hgas := R.gas
  cases hg' : (X.pfOf E.k).gas[pc]? with
  | none => simp [growFee, hg'] at hfee
  | some e =>
    cases e with
    | none =>
      simp only [growFee, hg', Option.some.injEq, Prod.mk.injEq] at hfee
      obtain ⟨rfl, rfl⟩ := hfee
      have hge : (X.pfOf E.k).gas[f.pc]? = some none := by rw [R.pcEq]; exact hg'
      rw [show 0 + 0 * n = 0 by simp, Nat.mul_zero, Nat.sub_zero,
        show ({ s with gas := { s.gas with g := s.gas.g } } : St) = s from rfl]
      simp only [step, R.frames, hpf, hcode, hge]
    | some kf =>
      obtain ⟨k, fe⟩ := kf
      have hge : (X.pfOf E.k).gas[f.pc]? = some (some (k, fe)) := by rw [R.pcEq]; exact hg'
      simp only [growFee, hg'] at hfee
      split at hfee
      · rename_i hc
        obtain ⟨hR0, hmod, _⟩ := hc
        have hc : fe.c = X.R * (fe.c / X.cfg.regularOpCost) := by
          unfold Ctx.R; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
        generalize fe.c / X.cfg.regularOpCost = q at hc hfee
        have hamt : (if k = IK.linear then NearSpecV3.Wasm.topCount s else 0) * fe.l + fe.c = X.R * (fee + lin * n) := by
          split at hfee
          · rename_i hl
            simp only [Option.some.injEq, Prod.mk.injEq] at hfee
            obtain ⟨rfl, rfl⟩ := hfee
            rcases hl with hl | hk
            · rw [hl, Nat.mul_zero, Nat.zero_add, hc]; simp
            · rw [if_neg hk, Nat.zero_mul, Nat.zero_add, hc]; simp
          · rename_i hl
            split at hfee
            · rename_i hlR
              simp only [Option.some.injEq, Prod.mk.injEq] at hfee
              obtain ⟨rfl, rfl⟩ := hfee
              have hk : k = IK.linear := Classical.byContradiction fun hk => hl (Or.inr hk)
              rw [if_pos hk, htop, hlR, hc]
              unfold Ctx.R
              rw [Nat.mul_add, Nat.one_mul, Nat.mul_comm n]
              omega
            · simp at hfee
        have hlt : ¬ ((if k = IK.linear then NearSpecV3.Wasm.topCount s else 0) * fe.l + fe.c ≥ u64Bound) := by
          rw [hamt]; unfold u64Bound; omega
        have hle : ¬ ((if k = IK.linear then NearSpecV3.Wasm.topCount s else 0) * fe.l + fe.c > s.gas.g) := by
          rw [hamt]; omega
        simp only [step, R.frames, hpf, hcode, hge, charge]
        rw [if_neg hlt, if_neg hle, hamt]
      · simp at hfee

#print axioms step_eq_exec_grow

/-! ## One step with an environment change -/

/-- The state after a straight step: gas register, stack, frames and pages replaced. -/
def stPost (s : St) (g : Nat) (stk : Array Val) (fr : List Frame) (pg : Array ByteArray) : St :=
  { s with gas := { s.gas with g := g }, stack := stk, frames := fr, pages := pg }

/-- `HeapOK` under a change of the environment's live set outside spaces 2 and 3. -/
theorem HeapOK.withLive {E : Env} {s s' : St} {t t' : Nat} (H : HeapOK E s t) (hpg : s'.pages = s.pages)
    (hgl : s'.globals = s.globals) (ht : t ≤ t') (L : Msg → Prop)
    (hL : ∀ x, (x.space = 2 ∨ x.space = 3) → (L x ↔ E.live x)) : HeapOK (E.withLive L) s' t' := by
  have H' := H.mono hpg hgl ht
  obtain ⟨T, tpm, hnd, hlt, htp, hv⟩ := H'.mem
  obtain ⟨tpg, hg, hgv⟩ := H'.glob
  exact ⟨H'.pages, ⟨T, tpm, hnd, hlt, htp, fun x hx => (hL x (Or.inr hx)).trans (hv x hx)⟩,
    ⟨tpg, hg, fun x hx => (hL x (Or.inl hx)).trans (hgv x hx)⟩⟩

/-- **One straight step that pops `k` operands, pushes `v`, may replace the pages, and changes the
environment by `c2`/`p2`** (outside the stack, the current locals, the call part): the `step_straight`
of `StepOps2.lean` for `straight_rel_envG`. -/
theorem step_envG (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S fee k : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    (hk : k ≤ s.stack.size) (v : Val) (hv : isNum v)
    (hnext : pc + 1 < (X.pfOf E.k).code.size)
    (hL1 : ∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls)
    (hsb : E.sb ≤ s.stack.size - k + 1) (hH1 : (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size - k + 1 - E.sb))
    (hgs : X.R * (S + fee - S_seg) ≤ segb) (pg' : Array ByteArray)
    (hstep : step X.cfg X.p s = .cont (stPost s (s.gas.g - X.R * fee) ((popK s.stack k).push v)
      ({ f with pc := pc + 1 } :: E.rest) pg'))
    (c2 p2 : List Msg) (hc2 : ∀ x ∈ c2, x.space ≠ 0 ∧ x.space ≠ E.lsp ∧ x.space ≠ 4 ∧ x.space ≠ 5 ∧ x.space < 16)
    (hp2 : ∀ x ∈ p2, x.space ≠ 0 ∧ x.space ≠ E.lsp ∧ x.space ≠ 4 ∧ x.space ≠ 5 ∧ x.space < 16)
    (heap' : HeapOK (E.withLive fun x => (E.live x ∧ x ∉ c2) ∨ x ∈ p2)
      (stPost s (s.gas.g - X.R * fee) ((popK s.stack k).push v) ({ f with pc := pc + 1 } :: E.rest) pg') (t + 1))
    (cons prod : List Msg)
    (hc : ∀ x, x ∈ ((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++ c2 ↔ x ∈ cons)
    (hp : ∀ x, x ∈ enc 0 (s.stack.size - k) v t :: p2 ↔ x ∈ prod) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ s'.pages = pg' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live cons prod) S_seg segb := by
  refine ⟨_, hstep, rfl, ?_⟩
  have hf : ({ f with pc := pc + 1 } : Frame) = { f with pc := pc + 1, locals := f.locals } := rfl
  have SR := straight_rel_envG X R hk ((popK s.stack k).push v) f.locals none
    (pushpop_keep _ _ _) (by rw [pushpop_size]; omega) (pushpop_num _ _ _ hv R.numS)
    rfl (fun _ _ => rfl) (by simp) R.numL hnext hL1 (by rw [pushpop_size]; omega)
    (by rw [pushpop_size]; exact hH1) hgs c2 p2 hc2 hp2
    (stPost s (s.gas.g - X.R * fee) ((popK s.stack k).push v) ({ f with pc := pc + 1 } :: E.rest) pg')
    rfl rfl rfl rfl heap'
  have e : ∀ c1 p1 : List Msg, (∀ x, x ∈ c1 ↔ x ∈ cons) → (∀ x, x ∈ p1 ↔ x ∈ prod) →
      stepLive live c1 p1 = stepLive live cons prod := fun c1 p1 h1 h2 => stepLive_congr h1 h2
  have := Rel_of_RelW_congr SR (e _ _ (fun x => ?_) (fun x => ?_))
  · exact this
  · rw [← hc x]
    simp only [List.mem_append, Option.toList_none, List.map_nil, List.append_nil]
  · rw [← hp x]
    simp only [pushpop_size, List.mem_append, List.mem_map, List.mem_range, Option.toList_none,
      List.map_nil, List.append_nil, List.mem_cons]
    constructor
    · rintro (⟨d, hd, rfl⟩ | h)
      · have : d = 0 := by omega
        subst this; rw [Nat.add_zero, pushpop_top]; exact Or.inl rfl
      · exact Or.inr h
    · rintro (rfl | h)
      · exact Or.inl ⟨0, by omega, by rw [Nat.add_zero, pushpop_top]⟩
      · exact Or.inr h

#print axioms step_envG

/-- A space-8 message is an environment message, with the side conditions of `step_envG`. -/
theorem sz_env (E : Env) (pg tp : Nat) :
    (szMsg pg tp).space ≠ 0 ∧ (szMsg pg tp).space ≠ E.lsp ∧ (szMsg pg tp).space ≠ 4 ∧
      (szMsg pg tp).space ≠ 5 ∧ (szMsg pg tp).space < 16 := by
  simp only [szMsg_space, Env.lsp]; omega

/-- Removing / adding size messages does not change the environment's spaces 2 and 3. -/
theorem sz_heap {L : Msg → Prop} {c2 p2 : List Msg} (h8c : ∀ y ∈ c2, y.space = 8) (h8p : ∀ y ∈ p2, y.space = 8)
    {x : Msg} (hx : x.space = 2 ∨ x.space = 3) : ((L x ∧ x ∉ c2) ∨ x ∈ p2) ↔ L x := by
  have n1 : x ∉ c2 := fun h => by have := h8c x h; omega
  have n2 : x ∉ p2 := fun h => by have := h8p x h; omega
  exact ⟨fun h => h.elim (·.1) (absurd · n2), fun h => Or.inl ⟨h, n1⟩⟩

/-- The value a MEMG row pushes: an `i32`. -/
def i32V (n : Nat) : Val := .i32 (UInt32.ofNat n)

theorem i32V_num (n : Nat) : isNum (i32V n) := by simp [i32V, isNum]

/-! ## `memory.size` -/

/-- **`memory.size` from the relation and the size clause**: it consumes the live size message and
re-produces it at `t` (MEMG's `chRecv`/`chSend` on space 8), and pushes `pages` (an `i32`). -/
theorem step_memSize (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some .memSize) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (hnext : pc + 1 < (X.pfOf E.k).code.size)
    (hL1 : ∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls)
    (hH1 : (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size + 1 - E.sb))
    (hQ : SzC s live) {tz : Nat} (hz : live (szMsg s.pages.size tz)) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ s'.pages = s.pages ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid
        (stepLive live [szMsg s.pages.size tz] [enc 0 s.stack.size (i32V s.pages.size) t, szMsg s.pages.size t])
        S_seg segb ∧
      SzC s' (stepLive live [szMsg s.pages.size tz] [enc 0 s.stack.size (i32V s.pages.size) t, szMsg s.pages.size t]) := by
  have hsbl := R.sbLe
  have hstep : step X.cfg X.p s = .cont (stPost s (s.gas.g - X.R * fee) ((popK s.stack 0).push (i32V s.pages.size))
      ({ f with pc := pc + 1 } :: E.rest) s.pages) := by
    rw [step_eq_exec X R hins hfee hg hg64]
    simp only [exec, pushI32, pushV, setFrame, R.frames, R.pcEq, stPost, popK, i32V]
  have hheap : HeapOK (E.withLive fun x => (E.live x ∧ x ∉ [szMsg s.pages.size tz]) ∨ x ∈ [szMsg s.pages.size t])
      (stPost s (s.gas.g - X.R * fee) ((popK s.stack 0).push (i32V s.pages.size))
        ({ f with pc := pc + 1 } :: E.rest) s.pages) (t + 1) :=
    HeapOK.withLive (t' := t + 1) (s' := stPost s (s.gas.g - X.R * fee) ((popK s.stack 0).push (i32V s.pages.size))
        ({ f with pc := pc + 1 } :: E.rest) s.pages) R.heap rfl rfl (Nat.le_succ t) _
      (fun x hx => sz_heap (c2 := [szMsg s.pages.size tz]) (p2 := [szMsg s.pages.size t]) (by simp) (by simp) hx)
  obtain ⟨s', hs, hpg, hR⟩ := step_envG X R (k := 0) (Nat.zero_le _) (i32V s.pages.size) (i32V_num _) hnext hL1
    (by omega) (by simpa using hH1) hg s.pages hstep [szMsg s.pages.size tz] [szMsg s.pages.size t]
    (fun x hx => by rw [List.mem_singleton.mp hx]; exact sz_env E _ _)
    (fun x hx => by rw [List.mem_singleton.mp hx]; exact sz_env E _ _) hheap
    [szMsg s.pages.size tz] [enc 0 s.stack.size (i32V s.pages.size) t, szMsg s.pages.size t]
    (fun x => by simp) (fun x => by simp)
  refine ⟨s', hs, hpg, hR, ?_⟩
  exact SzC.swap hQ hz (by simp) (fun x hx h8 => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · simp [enc] at h8
    · rw [hpg]) (by rw [hpg]; simp)

#print axioms step_memSize

/-! ## `memory.grow` -/

/-- The zero bytes a successful grow hands to MEMBG (`encB a 0 t`, produced at the grow's time). -/
def zeroBytes (A : List Nat) (t : Nat) : List Msg := A.map fun a => encB a 0 t

theorem zeroBytes_space {A : List Nat} {t : Nat} {x : Msg} (h : x ∈ zeroBytes A t) : x.space = 3 := by
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp h; rfl

/-- The exec of `memory.grow` on an `i32` top operand. -/
theorem exec_memGrow (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) {w : UInt32}
    (hb : s.stack.back? = some (.i32 w)) :
    exec cfg p s f pf .memGrow =
      if s.pages.size + w.toNat ≤ cfg.maxMemoryPages then
        .cont (setFrame (pushI32 { s with stack := s.stack.pop, pages := s.pages ++ Array.replicate w.toNat zeroPage }
          s.pages.size) { f with pc := f.pc + 1 })
      else .cont (setFrame (pushI32 { s with stack := s.stack.pop } (2 ^ 32 - 1)) { f with pc := f.pc + 1 }) := by
  simp only [exec, popN, popV, hb, Option.getD_some]

/-- The heap view after a successful grow: the old touched bytes keep their value and time, the
addresses of `A` (all in the new pages) are zero bytes produced at `t`. -/
theorem HeapOK.grow {E : Env} {s s' : St} {t : Nat} (H : HeapOK E s t) {n : Nat}
    (hpg : s'.pages = s.pages ++ Array.replicate n zeroPage) (hgl : s'.globals = s.globals)
    (A : List Nat) (hAnd : A.Nodup)
    (hA : ∀ a ∈ A, s.pages.size * pageSize ≤ a ∧ a < (s.pages.size + n) * pageSize)
    (L : Msg → Prop) (hL2 : ∀ x, x.space = 2 → (L x ↔ E.live x))
    (hL3 : ∀ x, x.space = 3 → (L x ↔ E.live x ∨ x ∈ zeroBytes A t)) :
    HeapOK (E.withLive L) s' (t + 1) := by
  obtain ⟨T, tpm, hnd, hlt, htp, hv⟩ := H.mem
  obtain ⟨tpg, hg, hgv⟩ := H.glob
  have hgr : ∀ a, readByte s' a = readByte (SegGrow.grown s n) a := fun a => readByte_congr hpg a
  have hsz : s'.pages.size = s.pages.size + n := by rw [hpg]; simp
  refine ⟨fun i hi => ?_, ⟨T ++ A, fun a => if a ∈ A then t else tpm a, ?_, ?_, ?_, fun x hx => ?_⟩,
    ⟨tpg, fun g hgs => ?_, fun x hx => ?_⟩⟩
  · -- the pages
    have hi' : i < s.pages.size + n := by rw [← hsz]; exact hi
    simp only [hpg]
    by_cases h : i < s.pages.size
    · rw [Array.getElem_append_left h]; exact H.pages i h
    · rw [Array.getElem_append_right (by omega)]; simp [zeroPage, ByteArray.size]
  · rw [List.nodup_append]
    refine ⟨hnd, hAnd, fun a ha b hb hab => ?_⟩
    subst hab
    have := hlt a ha; have := (hA a hb).1
    unfold memBytes at *; omega
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · have := hlt a h; unfold memBytes at *; rw [hsz]
      have : s.pages.size * pageSize ≤ (s.pages.size + n) * pageSize := Nat.mul_le_mul_right _ (by omega)
      omega
    · unfold memBytes; rw [hsz]; exact (hA a h).2
  · intro a ha
    show (if a ∈ A then t else tpm a) < t + 1
    split
    · omega
    · rcases List.mem_append.mp ha with h | h
      · have := htp a h; omega
      · contradiction
  · rw [Env.withLive_live, hL3 x hx, hv x hx]
    simp only [memView, List.map_append, List.mem_append, zeroBytes, List.mem_map]
    have hnA : ∀ a ∈ T, a ∉ A := fun a ha hA' => by
      have := hlt a ha; have := (hA a hA').1; unfold memBytes at *; omega
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · refine Or.inl ⟨a, ha, ?_⟩
        rw [if_neg (hnA a ha), hgr, SegGrow.readByte_grown_lt (by have := hlt a ha; unfold memBytes at this; exact this)]
      · refine Or.inr ⟨a, ha, ?_⟩
        rw [if_pos ha, hgr, SegGrow.readByte_grown_ge (hA a ha).1 (hA a ha).2]; rfl
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · refine Or.inl ⟨a, ha, ?_⟩
        rw [if_neg (hnA a ha), hgr, SegGrow.readByte_grown_lt (by have := hlt a ha; unfold memBytes at this; exact this)]
      · refine Or.inr ⟨a, ha, ?_⟩
        rw [if_pos ha, hgr, SegGrow.readByte_grown_ge (hA a ha).1 (hA a ha).2]; rfl
  · rw [hgl] at hgs ⊢; have := hg g hgs; exact ⟨by omega, this.2⟩
  · rw [Env.withLive_live, hL2 x hx, hgv x hx, hgl]

#print axioms HeapOK.grow

/-- **A successful `memory.grow` from the relation and the size clause.**  The top operand is the
`i32` page count `n` (consumed with the live size message `pages`); with `pages + n ≤ maxMemoryPages`
the step appends `n` zero pages, pushes the old size, re-produces the size message as `pages + n` at
`t`, and the addresses `A` of the new pages that MEMBG hands over enter the heap view as zero bytes
produced at `t`.  The charge is the linear fee `R · (fee + lin · n)`. -/
theorem step_memGrow_ok (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {fee lin : Nat} {w : UInt32}
    (hins : (X.pfOf E.k).code[pc]? = some .memGrow) (hfee : growFee X.cfg (X.pfOf E.k).gas[pc]? = some (fee, lin))
    (hstk : E.sb + 1 ≤ s.stack.size) (hw : s.stack[s.stack.size - 1]? = some (.i32 w))
    (hg : X.R * (S + (fee + lin * w.toNat) - S_seg) ≤ segb)
    (hok : s.pages.size + w.toNat ≤ X.cfg.maxMemoryPages)
    (hnext : pc + 1 < (X.pfOf E.k).code.size)
    (hL1 : ∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls)
    (hH1 : (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size - E.sb))
    (hQ : SzC s live) {tz : Nat} (hz : live (szMsg s.pages.size tz))
    (A : List Nat) (hAnd : A.Nodup)
    (hA : ∀ a ∈ A, s.pages.size * pageSize ≤ a ∧ a < (s.pages.size + w.toNat) * pageSize) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ s'.pages = s.pages ++ Array.replicate w.toNat zeroPage ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + (fee + lin * w.toNat)) E.sb E.cid
        (stepLive live [enc 0 (s.stack.size - 1) (.i32 w) (tps (s.stack.size - 1)), szMsg s.pages.size tz]
          (enc 0 (s.stack.size - 1) (i32V s.pages.size) t :: szMsg (s.pages.size + w.toNat) t :: zeroBytes A t))
        S_seg segb ∧
      SzC s' (stepLive live [enc 0 (s.stack.size - 1) (.i32 w) (tps (s.stack.size - 1)), szMsg s.pages.size tz]
          (enc 0 (s.stack.size - 1) (i32V s.pages.size) t :: szMsg (s.pages.size + w.toNat) t :: zeroBytes A t)) := by
  have hb : s.stack.back? = some (.i32 w) := by rw [Array.back?_eq_getElem?]; exact hw
  have htop : NearSpecV3.Wasm.topCount s = w.toNat := by simp [NearSpecV3.Wasm.topCount, hb]
  have hpg' : (s.pages ++ Array.replicate w.toNat zeroPage).size = s.pages.size + w.toNat := by simp
  have hstep : step X.cfg X.p s = .cont (stPost s (s.gas.g - X.R * (fee + lin * w.toNat))
      ((popK s.stack 1).push (i32V s.pages.size)) ({ f with pc := pc + 1 } :: E.rest)
      (s.pages ++ Array.replicate w.toNat zeroPage)) := by
    rw [step_eq_exec_grow X R hins hfee htop hg, exec_memGrow _ _ _ _ _ (w := w) (by simpa using hb), if_pos hok]
    simp only [pushI32, pushV, setFrame, R.frames, R.pcEq, stPost, popK, i32V]
  let c2 := [szMsg s.pages.size tz]
  let p2 := szMsg (s.pages.size + w.toNat) t :: zeroBytes A t
  have hc2 : ∀ x ∈ c2, x.space ≠ 0 ∧ x.space ≠ E.lsp ∧ x.space ≠ 4 ∧ x.space ≠ 5 ∧ x.space < 16 := by
    intro x hx; rw [List.mem_singleton.mp hx]; exact sz_env E _ _
  have hp2 : ∀ x ∈ p2, x.space ≠ 0 ∧ x.space ≠ E.lsp ∧ x.space ≠ 4 ∧ x.space ≠ 5 ∧ x.space < 16 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact sz_env E _ _
    · rw [zeroBytes_space h]; simp only [Env.lsp]; omega
  have hheap : HeapOK (E.withLive fun x => (E.live x ∧ x ∉ c2) ∨ x ∈ p2)
      (stPost s (s.gas.g - X.R * (fee + lin * w.toNat)) ((popK s.stack 1).push (i32V s.pages.size))
        ({ f with pc := pc + 1 } :: E.rest) (s.pages ++ Array.replicate w.toNat zeroPage)) (t + 1) := by
    refine HeapOK.grow R.heap ?_ ?_ A hAnd hA _ (fun x hx => ?_) (fun x hx => ?_)
    · rfl
    · rfl
    · have n1 : x ∉ c2 := fun h => by rw [List.mem_singleton.mp h] at hx; simp at hx
      have n2 : x ∉ p2 := fun h => by
        rcases List.mem_cons.mp h with rfl | h
        · simp at hx
        · rw [zeroBytes_space h] at hx; omega
      exact ⟨fun h => h.elim (·.1) (absurd · n2), fun h => Or.inl ⟨h, n1⟩⟩
    · have n1 : x ∉ c2 := fun h => by rw [List.mem_singleton.mp h] at hx; simp at hx
      have n2 : x ≠ szMsg (s.pages.size + w.toNat) t := fun h => by rw [h] at hx; simp at hx
      simp only [p2, List.mem_cons, n2, false_or]
      exact ⟨fun h => h.elim (fun h => Or.inl h.1) Or.inr, fun h => h.elim (fun h => Or.inl ⟨h, n1⟩) Or.inr⟩
  obtain ⟨s', hs, hpg, hR⟩ := step_envG X R (k := 1) (by omega) (i32V s.pages.size) (i32V_num _) hnext hL1
    (by omega) (by rw [hH1]; congr 1; omega) hg _ hstep c2 p2 hc2 hp2 hheap
    [enc 0 (s.stack.size - 1) (.i32 w) (tps (s.stack.size - 1)), szMsg s.pages.size tz]
    (enc 0 (s.stack.size - 1) (i32V s.pages.size) t :: szMsg (s.pages.size + w.toNat) t :: zeroBytes A t)
    (fun x => by simp [c2, hw]) (fun x => by simp [p2])
  refine ⟨s', hs, hpg, hR, ?_⟩
  have hsz' : s'.pages.size = s.pages.size + w.toNat := by rw [hpg, hpg']
  exact SzC.swap hQ hz (by simp) (fun x hx h8 => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | h
    · simp [enc] at h8
    · rw [hsz']
    · rw [zeroBytes_space h] at h8; omega) (by rw [hsz']; simp)

#print axioms step_memGrow_ok

/-- **A failing `memory.grow`** (`pages + n > maxMemoryPages`): pushes `2^32 − 1`, memory and size
unchanged (the size message is re-produced at `t`), with the linear fee. -/
theorem step_memGrow_fail (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {fee lin : Nat} {w : UInt32}
    (hins : (X.pfOf E.k).code[pc]? = some .memGrow) (hfee : growFee X.cfg (X.pfOf E.k).gas[pc]? = some (fee, lin))
    (hstk : E.sb + 1 ≤ s.stack.size) (hw : s.stack[s.stack.size - 1]? = some (.i32 w))
    (hg : X.R * (S + (fee + lin * w.toNat) - S_seg) ≤ segb)
    (hfail : X.cfg.maxMemoryPages < s.pages.size + w.toNat)
    (hnext : pc + 1 < (X.pfOf E.k).code.size)
    (hL1 : ∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls)
    (hH1 : (X.ckOf E.k).heights[pc + 1]? = some (s.stack.size - E.sb))
    (hQ : SzC s live) {tz : Nat} (hz : live (szMsg s.pages.size tz)) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ s'.pages = s.pages ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + (fee + lin * w.toNat)) E.sb E.cid
        (stepLive live [enc 0 (s.stack.size - 1) (.i32 w) (tps (s.stack.size - 1)), szMsg s.pages.size tz]
          [enc 0 (s.stack.size - 1) (i32V (2 ^ 32 - 1)) t, szMsg s.pages.size t])
        S_seg segb ∧
      SzC s' (stepLive live [enc 0 (s.stack.size - 1) (.i32 w) (tps (s.stack.size - 1)), szMsg s.pages.size tz]
          [enc 0 (s.stack.size - 1) (i32V (2 ^ 32 - 1)) t, szMsg s.pages.size t]) := by
  have hb : s.stack.back? = some (.i32 w) := by rw [Array.back?_eq_getElem?]; exact hw
  have htop : NearSpecV3.Wasm.topCount s = w.toNat := by simp [NearSpecV3.Wasm.topCount, hb]
  have hstep : step X.cfg X.p s = .cont (stPost s (s.gas.g - X.R * (fee + lin * w.toNat))
      ((popK s.stack 1).push (i32V (2 ^ 32 - 1))) ({ f with pc := pc + 1 } :: E.rest) s.pages) := by
    rw [step_eq_exec_grow X R hins hfee htop hg, exec_memGrow _ _ _ _ _ (w := w) (by simpa using hb),
      if_neg (Nat.not_le.mpr hfail)]
    simp only [pushI32, pushV, setFrame, R.frames, R.pcEq, stPost, popK, i32V]
  have hheap : HeapOK (E.withLive fun x => (E.live x ∧ x ∉ [szMsg s.pages.size tz]) ∨ x ∈ [szMsg s.pages.size t])
      (stPost s (s.gas.g - X.R * (fee + lin * w.toNat)) ((popK s.stack 1).push (i32V (2 ^ 32 - 1)))
        ({ f with pc := pc + 1 } :: E.rest) s.pages) (t + 1) :=
    HeapOK.withLive (t' := t + 1) (s' := stPost s (s.gas.g - X.R * (fee + lin * w.toNat))
        ((popK s.stack 1).push (i32V (2 ^ 32 - 1))) ({ f with pc := pc + 1 } :: E.rest) s.pages)
      R.heap rfl rfl (Nat.le_succ t) _
      (fun x hx => sz_heap (c2 := [szMsg s.pages.size tz]) (p2 := [szMsg s.pages.size t]) (by simp) (by simp) hx)
  obtain ⟨s', hs, hpg, hR⟩ := step_envG X R (k := 1) (by omega) (i32V (2 ^ 32 - 1)) (i32V_num _) hnext hL1
    (by omega) (by rw [hH1]; congr 1; omega) hg s.pages hstep [szMsg s.pages.size tz] [szMsg s.pages.size t]
    (fun x hx => by rw [List.mem_singleton.mp hx]; exact sz_env E _ _)
    (fun x hx => by rw [List.mem_singleton.mp hx]; exact sz_env E _ _) hheap
    [enc 0 (s.stack.size - 1) (.i32 w) (tps (s.stack.size - 1)), szMsg s.pages.size tz]
    [enc 0 (s.stack.size - 1) (i32V (2 ^ 32 - 1)) t, szMsg s.pages.size t]
    (fun x => by simp [hw]) (fun x => by simp)
  refine ⟨s', hs, hpg, hR, ?_⟩
  exact SzC.swap hQ hz (by simp) (fun x hx h8 => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · simp [enc] at h8
    · rw [hpg]) (by rw [hpg]; simp)

#print axioms step_memGrow_fail

end WasmBase
