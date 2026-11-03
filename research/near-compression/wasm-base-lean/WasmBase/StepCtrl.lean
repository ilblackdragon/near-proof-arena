import WasmBase.StepOps2
/-!
# WasmBase.StepCtrl — structured control: block, loop, end, br, br_if, return

Labels are static (`CheckOut.labels`); under the no-discard condition (D3) branches leave the operand
stack unchanged, so the AIR's CTRL row only moves the pc (and pops the `br_if` condition).
-/
namespace WasmBase

variable {S_seg segb : Nat}
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- Relation after a control instruction: stack `popK k`, new pc and labels, locals unchanged. -/
theorem ctrl_rel (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S fee k : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) (hk : k ≤ s.stack.size)
    (pc' : Nat) (ls' : List Label)
    (hnext : pc' < (X.pfOf E.k).code.size) (hL : (X.ckOf E.k).labels[pc']? = some ls')
    (hsb : E.sb ≤ s.stack.size - k) (hH : (X.ckOf E.k).heights[pc']? = some (s.stack.size - k - E.sb))
    (hgs : X.R * (S + fee - S_seg) ≤ segb)
    (s' : St) (hs'stk : s'.stack = popK s.stack k)
    (hs'fr : s'.frames = { f with pc := pc', labels := shiftLabels E.sb ls' } :: E.rest)
    (hs'g : s'.gas.g = s.gas.g - X.R * fee) (hs'pg : s'.pages = s.pages)
    (hs'gl : s'.globals = s.globals) (hs'rem : s'.stackRem = s.stackRem) :
    RelW X E s' { f with pc := pc', labels := shiftLabels E.sb ls' }
      (fun i => if i < s.stack.size - k then tps i else t) (fun j => if some j = none then t else tpl j)
      (t + 1) pc' (S + fee)
      (stepLive live
        (((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          (none : Option Nat).toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) (tpl j)))
        (((List.range ((popK s.stack k).size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) ((popK s.stack k)[s.stack.size - k + d]?.getD default) t) ++
          (none : Option Nat).toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) t))) S_seg segb where
  frames := hs'fr
  kLt := R.kLt
  fn := R.fn
  pcEq := rfl
  pcLt := hnext
  labels := ⟨ls', hL, rfl⟩
  base := R.base
  sbLe := by rw [hs'stk, popK_size]; exact hsb
  height := by rw [hs'stk, popK_size]; exact hH
  nloc := R.nloc
  gas := R.step_gas hgs hs'g
  segLt := by have := R.segLt; omega
  segbLt := R.segbLt
  numS := by
    rw [hs'stk]; intro i hi; rw [popK_size] at hi; rw [popK_get _ _ _ hi]; exact R.numS i (by omega)
  numL := R.numL
  tpsLt := by
    intro i hi
    show (if i < s.stack.size - k then tps i else t) < t + 1
    split
    · have := R.tpsLt i (by omega); omega
    · omega
  tplLt := by
    intro j hj
    show (if some j = none then t else tpl j) < t + 1
    simp only [reduceCtorEq, ite_false]
    have := R.tplLt j hj; omega
  envSep := R.envSep
  entry := R.entry
  sbLt := R.sbLt
  cidLt := R.cidLt
  heap := R.heap.mono hs'pg hs'gl (by omega)
  calls := R.calls.mono (by omega) rfl rfl rfl rfl (fun _ _ => Iff.rfl) hs'rem
  live := by
    intro x
    rw [hs'stk]
    simp only [stepLive]
    have vu := view_update (sp := E.lsp) (by simp [Env.lsp]) none hk (popK_get s.stack k)
      (by rw [popK_size]; exact Nat.le_refl _) rfl (fun _ _ => rfl) (fun j hj => by cases hj) R.tpsLt R.tplLt x
    have hcons : E.live x → x ∉ (((List.range k).map fun d => enc 0 (s.stack.size - k + d)
        (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
        (none : Option Nat).toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) (tpl j))) := by
      intro he hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
        exact (R.envSep _ he).1 rfl
      · simp at hx
    have toLive : x ∈ stackView s.stack tps ∨ x ∈ localView E.lsp f.locals tpl → live x := fun h =>
      (R.live x).mpr (h.elim Or.inl (fun h => Or.inr (Or.inl h)))
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · rcases (R.live x).mp h1 with h | h | h
        · rcases vu.mpr (Or.inl ⟨Or.inl h, h2⟩) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
        · rcases vu.mpr (Or.inl ⟨Or.inr h, h2⟩) with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h)
      · rcases vu.mpr (Or.inr h3) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
    · rintro (h1 | h1 | h3)
      · rcases vu.mp (Or.inl h1) with ⟨h, h2⟩ | h
        · exact Or.inl ⟨toLive h, h2⟩
        · exact Or.inr h
      · rcases vu.mp (Or.inr h1) with ⟨h, h2⟩ | h
        · exact Or.inl ⟨toLive h, h2⟩
        · exact Or.inr h
      · exact Or.inl ⟨(R.live x).mpr (Or.inr (Or.inr h3)), hcons h3⟩

/-! ## Shifted labels -/

theorem shiftLabels_cons (sb : Nat) (l : Label) (ls : List Label) :
    shiftLabels sb (l :: ls) = { l with height := l.height + sb } :: shiftLabels sb ls := rfl

theorem shiftLabels_length (sb : Nat) (ls : List Label) : (shiftLabels sb ls).length = ls.length := by
  simp [shiftLabels]

theorem shiftLabels_get (sb : Nat) (ls : List Label) (l : Nat) :
    (shiftLabels sb ls)[l]? = (ls[l]?).map fun x => { x with height := x.height + sb } := by
  simp [shiftLabels]

theorem shiftLabels_drop (sb : Nat) (ls : List Label) (n : Nat) :
    (shiftLabels sb ls).drop n = shiftLabels sb (ls.drop n) := by
  simp [shiftLabels, List.map_drop]

/-- Control step with nothing popped (block, loop, nested end, br). -/
theorem step_ctrl0 (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {ins : Instr} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some ins) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64) (pc' : Nat) (ls' : List Label)
    (hnext : pc' < (X.pfOf E.k).code.size) (hL : (X.ckOf E.k).labels[pc']? = some ls')
    (hH : (X.ckOf E.k).heights[pc']? = some (s.stack.size - E.sb))
    (hexec : exec X.cfg X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f (X.pfOf E.k) ins =
      .cont { s with gas := { s.gas with g := s.gas.g - X.R * fee },
                     frames := { f with pc := pc', labels := shiftLabels E.sb ls' } :: E.rest }) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) E.k pc' (S + fee) E.sb E.cid (stepLive live [] []) S_seg segb := by
  refine ⟨_, by rw [step_eq_exec X R hins hfee hg hg64, hexec], ?_⟩
  have CR := ctrl_rel X R (k := 0) (fee := fee) (Nat.zero_le _) pc' ls' hnext hL (by have := R.sbLe; omega)
    (by simpa using hH) hg
    { s with gas := { s.gas with g := s.gas.g - X.R * fee },
             frames := { f with pc := pc', labels := shiftLabels E.sb ls' } :: E.rest }
    rfl rfl rfl rfl rfl rfl
  refine Rel_of_RelW_congr CR (stepLive_congr ?_ ?_)
  · intro x; simp
  · intro x; simp [popK_size]

/-- `doBr` to a non-function label under no-discard leaves the stack unchanged. -/
theorem stack_nodiscard (a : Array Val) (h ar : Nat) (hn : h + ar = a.size) :
    a.extract 0 h ++ a.extract (a.size - ar) a.size = a := by
  have : a.size - ar = h := by omega
  rw [this, Array.extract_append_extract]
  simp [Nat.max_def]
  grind

theorem doBr_label (p : Prepared) (s : St) (f : Frame) (l : Nat) (lab : Label)
    (hl : l + 1 < f.labels.length) (hlab : f.labels[l]? = some lab)
    (hn : lab.height + lab.arity = s.stack.size) :
    doBr p s f l = .cont (setFrame s { f with pc := lab.target, labels := (if lab.isLoop then f.labels.drop l else f.labels.drop (l + 1)) }) := by
  unfold doBr
  rw [if_neg (by omega), hlab]
  simp only
  rw [stack_nodiscard s.stack lab.height lab.arity hn]

/-- `doReturn` from the only frame under no-discard leaves the stack unchanged. -/
theorem doReturn_one (X : Ctx) {k : Nat} (hkn : k < X.nf) (s : St) (f : Frame) (hfr : s.frames = [f]) (hfn : f.fn = (X.fnOf k))
    (hb : f.base = 0) (har : s.stack.size = (X.pfOf k).type.results.size) :
    doReturn X.p s = .fin { s with stack := s.stack, frames := [], stackRem := s.stackRem + (X.pfOf k).stackCharge } := by
  unfold doReturn
  rw [hfr]
  simp only
  rw [hfn, (X.factsOf hkn).func]
  simp only [hb, List.isEmpty_nil, ite_true]
  rw [← har, stack_nodiscard s.stack 0 s.stack.size (by omega)]

/-! ## block, loop, nested end, br -/

theorem step_block (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {bt : BT} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.block bt)) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [] []) S_seg segb := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt _ hins (by m2_ns)
  obtain ⟨ls0, hL0, hfl⟩ := R.labels
  have hsb := R.sbLe
  unfold verifyAt at hv
  rw [hins, hL0, R.height] at hv
  simp only at hv
  cases he : (X.pfOf E.k).endOf[pc]? with
  | none => simp [he] at hv
  | some e =>
    simp only [he, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hnext, hL1⟩, hH1⟩ := hv
    apply step_ctrl0 X R hins hfee hg hg64 (pc + 1) _ hnext hL1 hH1
    simp only [exec, R.pcEq, he, setFrame, R.frames, shiftLabels_cons, hfl, Nat.sub_add_cancel hsb]

theorem step_loop (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.loop none)) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [] []) S_seg segb := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt _ hins (by m2_ns)
  obtain ⟨ls0, hL0, hfl⟩ := R.labels
  have hsb := R.sbLe
  unfold verifyAt at hv
  rw [hins, hL0, R.height] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨hnext, hL1⟩, hH1⟩ := hv
  apply step_ctrl0 X R hins hfee hg hg64 (pc + 1) _ hnext hL1 hH1
  simp only [exec, R.pcEq, setFrame, R.frames, shiftLabels_cons, hfl, Nat.sub_add_cancel hsb]

theorem step_end_nested (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {fee : Nat} {lab lab' : Label}
    {rest : List Label} (hls : f.labels = lab :: lab' :: rest)
    (hins : (X.pfOf E.k).code[pc]? = some .end_) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [] []) S_seg segb := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt _ hins (by m2_ns)
  obtain ⟨ls0, hL0, hfl⟩ := R.labels
  obtain ⟨l0, l0', rest0, rfl⟩ : ∃ l0 l0' rest0, ls0 = l0 :: l0' :: rest0 := by
    rw [hls] at hfl
    match ls0, hfl with
    | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩
  unfold verifyAt at hv
  rw [hins, hL0, R.height] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨hnext, hL1⟩, hH1⟩ := hv
  apply step_ctrl0 X R hins hfee hg hg64 (pc + 1) _ hnext hL1 hH1
  have hrest : lab' :: rest = shiftLabels E.sb (l0' :: rest0) := by
    rw [hls, shiftLabels_cons] at hfl
    exact (List.cons.inj hfl).2
  simp only [exec, hls, setFrame, R.frames, R.pcEq]
  rw [hrest]

theorem step_br (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {l fee : Nat} {lab : Label}
    (hl : l + 1 < f.labels.length) (hlab : f.labels[l]? = some lab)
    (hins : (X.pfOf E.k).code[pc]? = some (.br l)) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) E.k lab.target (S + fee) E.sb E.cid (stepLive live [] []) S_seg segb := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt _ hins (by m2_ns)
  obtain ⟨ls0, hL0, hfl⟩ := R.labels
  have hsb := R.sbLe
  have hlen : l + 1 < ls0.length := by rw [hfl, shiftLabels_length] at hl; exact hl
  obtain ⟨lab0, hlab0, rfl⟩ : ∃ lab0, ls0[l]? = some lab0 ∧ lab = { lab0 with height := lab0.height + E.sb } := by
    rw [hfl, shiftLabels_get] at hlab
    cases h : ls0[l]? with
    | none => rw [h] at hlab; simp at hlab
    | some x => rw [h] at hlab; simp only [Option.map_some, Option.some.injEq] at hlab; exact ⟨x, rfl, hlab.symm⟩
  unfold verifyAt at hv
  rw [hins, hL0, R.height] at hv
  simp only [show ¬ (l + 1 ≥ ls0.length) by omega, ite_false, hlab0, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨hn, ⟨hnext, hL1⟩, hH1⟩ := hv
  apply step_ctrl0 X R hins hfee hg hg64 lab0.target _ hnext hL1 hH1
  simp only [exec]
  rw [doBr_label X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f l _ hl hlab (by simp; omega)]
  simp only [setFrame, R.frames, hfl, shiftLabels_drop]
  split <;> rfl

/-! ## br_if -/

theorem step_brIf (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {l fee : Nat} {lab : Label}
    (hl : l + 1 < f.labels.length) (hlab : f.labels[l]? = some lab)
    (hins : (X.pfOf E.k).code[pc]? = some (.brIf l)) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (mc : Msg) (hmc : live mc) (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (if mc.val = 0 then pc + 1 else lab.target) (S + fee) E.sb E.cid (stepLive live [mc] []) S_seg segb := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt _ hins (by m2_ns)
  obtain ⟨ls0, hL0, hfl⟩ := R.labels
  have hsb := R.sbLe
  have hlen : l + 1 < ls0.length := by rw [hfl, shiftLabels_length] at hl; exact hl
  obtain ⟨lab0, hlab0, rfl⟩ : ∃ lab0, ls0[l]? = some lab0 ∧ lab = { lab0 with height := lab0.height + E.sb } := by
    rw [hfl, shiftLabels_get] at hlab
    cases h : ls0[l]? with
    | none => rw [h] at hlab; simp at hlab
    | some x => rw [h] at hlab; simp only [Option.map_some, Option.some.injEq] at hlab; exact ⟨x, rfl, hlab.symm⟩
  unfold verifyAt at hv
  rw [hins, hL0, R.height] at hv
  simp only [show ¬ (l + 1 ≥ ls0.length) by omega, ite_false, hlab0, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨⟨h1, ⟨hnext, hL1⟩, hH1⟩, hn, ⟨hnextT, hLT⟩, hHT⟩ := hv
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  have hpop : (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).1 = mc.val := by
    rw [popN_eq, vc]; simp only; rw [back_getD _ (by omega)]
  have hb' : vNum (s.stack.back?.getD (.i32 0)) = mc.val := by rw [back_getD _ (by omega), vc]
  -- both outcomes pop the condition (k = 1) and change only pc / labels
  have key : ∀ (pc' : Nat) (ls' : List Label), pc' < (X.pfOf E.k).code.size → (X.ckOf E.k).labels[pc']? = some ls' →
      (X.ckOf E.k).heights[pc']? = some (s.stack.size - 1 - E.sb) →
      exec X.cfg X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f (X.pfOf E.k) (.brIf l) =
        .cont { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := popK s.stack 1,
                       frames := { f with pc := pc', labels := shiftLabels E.sb ls' } :: E.rest } →
      ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) E.k pc' (S + fee) E.sb E.cid (stepLive live [mc] []) S_seg segb := by
    intro pc' ls' hn' hL' hH' hexec
    refine ⟨_, by rw [step_eq_exec X R hins hfee hg hg64, hexec], ?_⟩
    have CR := ctrl_rel X R (k := 1) (fee := fee) (by omega) pc' ls' hn' hL' (by omega) hH' hg
      { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := popK s.stack 1,
               frames := { f with pc := pc', labels := shiftLabels E.sb ls' } :: E.rest } rfl rfl rfl rfl rfl rfl
    refine Rel_of_RelW_congr CR (stepLive_congr ?_ ?_)
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
  by_cases h0 : mc.val = 0
  · rw [if_pos h0]
    apply key (pc + 1) ls0 hnext hL1 (by rw [hH1]; congr 1; omega)
    simp only [exec, popN_eq, hb', h0, ne_eq, not_true_eq_false, ite_false, setFrame, R.frames, R.pcEq,
      popK, Array.size_pop, ← hfl]
  · rw [if_neg h0]
    apply key lab0.target _ hnextT hLT (by rw [hHT]; congr 1; omega)
    simp only [exec, popN_eq, hb', ne_eq, h0, not_false_eq_true, ite_true]
    rw [doBr_label X.p _ f l _ hl hlab (by simp only [Array.size_pop]; omega)]
    simp only [setFrame, R.frames, popK, hfl, shiftLabels_drop]
    split <;> rfl

/-! ## return from the function (end of body, return, br / br_if to the function label) -/

/-- The halting outcome: the spec finishes with the same operand stack. -/
def Halted (X : Ctx) (s sN : St) (fee : Nat) (stk : Array Val) : Prop :=
  sN.frames = [] ∧ sN.stack = stk ∧ sN.gas.g = s.gas.g - X.R * fee

theorem step_halt (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {ins : Instr} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some ins)
    (hkind : (ins = .end_ ∧ f.labels.length = 1) ∨ ins = .ret ∨ (∃ l, ins = .br l ∧ l + 1 ≥ f.labels.length))
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64) (hent : E.rest = [] ∧ E.sb = 0) :
    ∃ sN, step X.cfg X.p s = .fin sN ∧ Halted X s sN fee s.stack := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt _ hins
    (by rcases hkind with ⟨rfl, _⟩ | rfl | ⟨_, rfl, _⟩ <;> rfl)
  obtain ⟨ls0, hL0, hfl⟩ := R.labels
  rw [hent.2, shiftLabels_zero] at hfl
  have hfr : s.frames = [f] := by rw [R.frames, hent.1]
  have hH := R.height
  rw [hent.2, Nat.sub_zero] at hH
  have hbase : f.base = 0 := by rw [R.base, hent.2]
  have hone : ins = .end_ → f.labels.length = 1 → ∃ lab0, f.labels = [lab0] := by
    intro _ h1; exact List.length_eq_one_iff.mp h1
  have har : s.stack.size = (X.pfOf E.k).type.results.size := by
    unfold verifyAt at hv
    rw [hins, hL0, hH, ← hfl] at hv
    rcases hkind with ⟨rfl, h1⟩ | rfl | ⟨l, rfl, hl⟩
    · obtain ⟨lab0, hls⟩ := hone rfl h1
      simp only [hls, decide_eq_true_eq] at hv; exact hv
    · simpa using hv
    · simp only [hl, ite_true, decide_eq_true_eq] at hv; exact hv
  rw [step_eq_exec X R hins hfee hg hg64]
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee } }
  have hd := doReturn_one X R.kLt s1 f hfr R.fn hbase har
  refine ⟨{ s1 with stack := s1.stack, frames := [], stackRem := s1.stackRem + (X.pfOf E.k).stackCharge }, ?_,
    ⟨rfl, rfl, rfl⟩⟩
  rcases hkind with ⟨rfl, h1⟩ | rfl | ⟨l, rfl, hl⟩
  · obtain ⟨lab0, hls⟩ := hone rfl h1
    simp only [exec, hls]; exact hd
  · simp only [exec]; exact hd
  · simp only [exec]; unfold doBr; rw [if_pos hl]; exact hd

theorem step_haltIf (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {l fee : Nat}
    (hl : l + 1 ≥ f.labels.length)
    (hins : (X.pfOf E.k).code[pc]? = some (.brIf l)) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64) (hent : E.rest = [] ∧ E.sb = 0)
    (mc : Msg) (hmc : live mc) (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1) :
    (mc.val ≠ 0 → ∃ sN, step X.cfg X.p s = .fin sN ∧ Halted X s sN fee s.stack.pop) ∧
    (mc.val = 0 → ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [mc] []) S_seg segb) := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt _ hins (by m2_ns)
  obtain ⟨ls0, hL0, hfl⟩ := R.labels
  rw [hent.2, shiftLabels_zero] at hfl
  have hfr : s.frames = [f] := by rw [R.frames, hent.1]
  have hH := R.height
  rw [hent.2, Nat.sub_zero] at hH
  have hbase : f.base = 0 := by rw [R.base, hent.2]
  unfold verifyAt at hv
  rw [hins, hL0, hH, ← hfl] at hv
  simp only [hl, ite_true, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨h1, ⟨hnext, hL1⟩, hH1⟩, har⟩ := hv
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  have hpop : (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).1 = mc.val := by
    rw [popN_eq, vc]; simp only; rw [back_getD _ (by omega)]
  have hb' : vNum (s.stack.back?.getD (.i32 0)) = mc.val := by rw [back_getD _ (by omega), vc]
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee } }
  let s2 : St := { s1 with stack := s1.stack.pop }
  constructor
  · intro h0
    rw [step_eq_exec X R hins hfee hg hg64]
    have hd := doReturn_one X R.kLt s2 f (by simp [s2, s1, hfr]) R.fn hbase (by simp [s2, s1]; omega)
    refine ⟨{ s2 with stack := s2.stack, frames := [], stackRem := s2.stackRem + (X.pfOf E.k).stackCharge }, ?_,
      ⟨rfl, rfl, rfl⟩⟩
    simp only [exec, popN_eq, hb', ne_eq, h0, not_false_eq_true, ite_true]
    unfold doBr; rw [if_pos hl]; exact hd
  · intro h0
    have hsl : shiftLabels E.sb f.labels = f.labels := by rw [hent.2, shiftLabels_zero]
    refine ⟨{ s1 with
      stack := popK s.stack 1
      frames := { f with pc := pc + 1, labels := shiftLabels E.sb f.labels } :: E.rest }, ?_, ?_⟩
    · rw [step_eq_exec X R hins hfee hg hg64]
      simp only [exec, popN_eq, hb', h0, ne_eq, not_true_eq_false, ite_false, setFrame, R.frames, R.pcEq,
        popK, s1, hsl]
    · have CR := ctrl_rel X R (k := 1) (fee := fee) (by omega) (pc + 1) f.labels hnext hL1 (by rw [hent.2]; omega)
        (by rw [hH1, hent.2]; rfl) hg
        { s1 with
          stack := popK s.stack 1
          frames := { f with pc := pc + 1, labels := shiftLabels E.sb f.labels } :: E.rest } rfl rfl rfl rfl rfl rfl
      refine Rel_of_RelW_congr CR (stepLive_congr ?_ ?_)
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
