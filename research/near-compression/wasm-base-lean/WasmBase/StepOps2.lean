import WasmBase.StepOps
/-!
# WasmBase.StepOps2 — generic straight-line step, and the remaining instruction classes
-/
namespace WasmBase

variable {S_seg segb : Nat}
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- A live stack message at slot `n - d` decodes to that stack entry. -/
theorem RelW.stack_dec {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {m : Msg} (hm : live m)
    {i : Nat} (hs : m.space = 0) (hi : m.slot = i) (hlt : i < s.stack.size) :
    m = enc 0 i (s.stack[i]?.getD default) (tps i) ∧ m.ok ∧
      m.val = vNum (s.stack[i]?.getD default) ∧ m.toVal = s.stack[i]?.getD default := by
  have e := R.stack_msg hm hs (by omega)
  rw [hi] at e
  have n := R.numS i hlt
  refine ⟨e, by rw [e]; exact enc_ok n _ _ _, by rw [e]; exact enc_val n _ _ _, by rw [e]; exact enc_toVal n _ _ _⟩

theorem RelW.local_dec {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {m : Msg} (hm : live m)
    {j : Nat} (hs : m.space = E.lsp) (hj : m.slot = j) (hlt : j < f.locals.size) :
    m = enc E.lsp j (f.locals[j]?.getD default) (tpl j) ∧ m.ok ∧
      m.val = vNum (f.locals[j]?.getD default) ∧ m.toVal = f.locals[j]?.getD default := by
  have e := R.local_msg hm hs (by omega)
  rw [hj] at e
  have n := R.numL j hlt
  refine ⟨e, by rw [e]; exact enc_ok n _ _ _, by rw [e]; exact enc_val n _ _ _, by rw [e]; exact enc_toVal n _ _ _⟩

/-- **Generic straight-line step**: charge, an `exec` that leaves the labels and moves to `pc + 1`,
and the channel view update with the event's consumed/produced messages. -/
theorem step_straight (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {ins : Instr} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some ins) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (k : Nat) (hk : k ≤ s.stack.size) (stk' locs' : Array Val) (J : Option Nat)
    (keep : ∀ i, i < s.stack.size - k → stk'[i]? = s.stack[i]?) (hsz : s.stack.size - k ≤ stk'.size)
    (hnum : ∀ i, i < stk'.size → isNum (stk'[i]?.getD default))
    (lsz : locs'.size = f.locals.size) (lkeep : ∀ j, some j ≠ J → locs'[j]? = f.locals[j]?)
    (hJ : ∀ j, J = some j → j < f.locals.size)
    (lnum : ∀ j, j < locs'.size → isNum (locs'[j]?.getD default))
    (hnext : pc + 1 < (X.pfOf E.k).code.size)
    (hL1 : ∃ ls, (X.ckOf E.k).labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls)
    (hsb : E.sb ≤ stk'.size) (hH1 : (X.ckOf E.k).heights[pc + 1]? = some (stk'.size - E.sb))
    (hexec : exec X.cfg X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f (X.pfOf E.k) ins =
      .cont { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := stk',
                     frames := { f with pc := pc + 1, locals := locs' } :: E.rest })
    (cons prod : List Msg)
    (hc : ∀ x, x ∈ ((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          J.toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) (tpl j)) ↔ x ∈ cons)
    (hp : ∀ x, x ∈ ((List.range (stk'.size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
          J.toList.map (fun j => enc E.lsp j (locs'[j]?.getD default) t) ↔ x ∈ prod) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live cons prod) S_seg segb := by
  refine ⟨_, by rw [step_eq_exec X R hins hfee hg hg64, hexec], ?_⟩
  have SR := straight_rel X R hk stk' locs' J keep hsz hnum lsz lkeep hJ lnum hnext hL1 hsb hH1 hg
    { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := stk',
             frames := { f with pc := pc + 1, locals := locs' } :: E.rest } rfl rfl rfl rfl rfl rfl
  exact Rel_of_RelW_congr SR (stepLive_congr hc hp)

/-- `setFrame` replaces the top frame. -/
theorem setFrame_one {s : St} {f : Frame} {fs : List Frame} (h : s.frames = f :: fs) (f' : Frame) :
    setFrame s f' = { s with frames := f' :: fs } := by
  simp [setFrame, h]

/-! ## Verification facts for straight instructions -/

theorem verify_straight (X : Ctx) {k : Nat} (hkn : k < X.nf) {pc : Nat} {ins : Instr} {ls : List Label} {h pops pushes : Nat}
    (hpc : pc < (X.pfOf k).code.size) (hins : (X.pfOf k).code[pc]? = some ins) (hL : (X.ckOf k).labels[pc]? = some ls)
    (hH : (X.ckOf k).heights[pc]? = some h) (hk : kindOf ls ins = some (.straight pops pushes))
    (hnc : ∀ bt, ins ≠ .block bt) (hnl : ins ≠ .loop none) (hne : ins ≠ .end_) (hnr : ins ≠ .ret)
    (hnb : ∀ l, ins ≠ .br l) (hnbi : ∀ l, ins ≠ .brIf l) :
    pops ≤ h ∧ pc + 1 < (X.pfOf k).code.size ∧ (X.ckOf k).labels[pc + 1]? = some ls ∧
      (X.ckOf k).heights[pc + 1]? = some (h - pops + pushes) := by
  have hv := (X.factsOf hkn).verify pc hpc _ hins (by m2_ns)
  have e : verifyAt X.p (X.pfOf k) (X.ckOf k).labels (X.ckOf k).heights pc =
      (decide (pops ≤ h) && (decide (pc + 1 < (X.pfOf k).code.size) && decide ((X.ckOf k).labels[pc + 1]? = some ls) &&
        decide ((X.ckOf k).heights[pc + 1]? = some (h - pops + pushes)))) := by
    unfold verifyAt
    rw [hins, hL, hH]
    cases ins with
    | block bt => exact absurd rfl (hnc bt)
    | loop bt => cases bt with
      | none => exact absurd rfl hnl
      | some _ => simp [kindOf] at hk
    | end_ => exact absurd rfl hne
    | ret => exact absurd rfl hnr
    | br l => exact absurd rfl (hnb l)
    | brIf l => exact absurd rfl (hnbi l)
    | call fi => simp [kindOf] at hk
    | _ => simp only [hk]
  rw [e] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨hv.1, hv.2.1.1, hv.2.1.2, hv.2.2⟩

/-! ## const, drop -/

theorem enc_eq_of_fields {m : Msg} {sp sl : Nat} {v : Val} {tp : Nat}
    (h1 : m.space = sp) (h2 : m.slot = sl) (h3 : m.tag = vTag v) (h4 : m.l0 = vNum v % 65536)
    (h5 : m.l1 = vNum v / 65536 % 65536) (h6 : m.l2 = vNum v / 2 ^ 32 % 65536)
    (h7 : m.l3 = vNum v / 2 ^ 48 % 65536) (h8 : m.tp = tp) : m = enc sp sl v tp := by
  cases m; simp_all [enc]

theorem step_const (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {ins : Instr} {v : Val} {fee : Nat}
    (hiv : (∃ x, ins = .i32Const x ∧ v = .i32 x) ∨ (∃ x, ins = .i64Const x ∧ v = .i64 x))
    (hins : (X.pfOf E.k).code[pc]? = some ins)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (mr : Msg) (hmr : mr = enc 0 s.stack.size v t) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [] [mr]) S_seg segb := by
  obtain ⟨ls0, hL, hfl⟩ := R.labels; have hH := R.height; have hsbR := R.sbLe
  have hnum : isNum v := by rcases hiv with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ <;> trivial
  have hk : kindOf ls0 ins = some (.straight 0 1) := by
    rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> rfl
  obtain ⟨-, hnext, hL1, hH1⟩ := verify_straight X R.kLt R.pcLt hins hL hH hk
    (by intro bt; rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
    (by rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp) (by rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
    (by rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
    (by intro l; rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
    (by intro l; rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
  have hsz : (s.stack.push v).size = s.stack.size - 0 + 1 := by simp
  apply step_straight X R hins hfee hg hg64 0 (Nat.zero_le _) (s.stack.push v) f.locals none
    (by intro i hi; simp only [Array.getElem?_push]; rw [if_neg (by omega)]) (by simp)
    (by intro i hi; simp only [Array.size_push] at hi; simp only [Array.getElem?_push]
        by_cases h : i = s.stack.size
        · rw [if_pos h]; exact hnum
        · rw [if_neg h]; exact R.numS i (by omega))
    rfl (fun _ _ => rfl) (by simp) R.numL hnext ⟨ls0, hL1, hfl⟩ (by rw [hsz]; omega) (by rw [hsz, hH1]; congr 1; omega)
  · rcases hiv with ⟨x, rfl, rfl⟩ | ⟨x, rfl, rfl⟩ <;> simp [exec, pushV, setFrame, R.frames, R.pcEq]
  · intro x; simp
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false, Array.size_push, Nat.sub_zero,
      Nat.add_sub_cancel_left]
    constructor
    · rintro ⟨d, hd, rfl⟩
      have : d = 0 := by omega
      subst this; rw [hmr]; simp [Array.getElem?_push]
    · rintro rfl; exact ⟨0, by omega, by rw [hmr]; simp [Array.getElem?_push]⟩

theorem step_drop (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some .drop)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (ma : Msg) (hma : live ma) (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 1) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [ma] []) S_seg segb := by
  obtain ⟨ls0, hL, hfl⟩ := R.labels; have hH := R.height; have hsbR := R.sbLe
  obtain ⟨h1, hnext, hL1, hH1⟩ := verify_straight X R.kLt R.pcLt hins hL hH (pops := 1) (pushes := 0) rfl
    (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp) (by intro l; simp)
  obtain ⟨ea, -, -, -⟩ := R.stack_dec hma sa.1 sa.2 (by omega)
  have hsz : s.stack.pop.size = s.stack.size - 1 + 0 := by simp
  apply step_straight X R hins hfee hg hg64 1 (by omega) s.stack.pop f.locals none
    (by intro i hi; simp only [Array.getElem?_pop]; rw [if_pos (by omega)]) (by simp)
    (by intro i hi; simp only [Array.size_pop] at hi; simp only [Array.getElem?_pop]
        rw [if_pos (by omega)]; exact R.numS i (by omega))
    rfl (fun _ _ => rfl) (by simp) R.numL hnext ⟨ls0, hL1, hfl⟩ (by rw [hsz]; omega) (by rw [hsz, hH1]; congr 1; omega)
  · simp [exec, popV, setFrame, R.frames, R.pcEq]
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
    constructor
    · rintro ⟨d, hd, rfl⟩
      have : d = 0 := by omega
      subst this; rw [ea, Nat.add_zero]
    · rintro rfl; exact ⟨0, by omega, by rw [ea, Nat.add_zero]⟩
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, false_and, exists_false, Array.size_pop, List.mem_nil_iff, iff_false]
    rintro ⟨d, hd, _⟩; omega

/-! ## pop-k-push-one helpers -/

def popK (a : Array Val) : Nat → Array Val
  | 0 => a
  | k + 1 => (popK a k).pop

theorem popK_size (a : Array Val) (k : Nat) : (popK a k).size = a.size - k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [popK, ih]; omega

theorem popK_get (a : Array Val) (k i : Nat) (hi : i < a.size - k) : (popK a k)[i]? = a[i]? := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [popK, Array.getElem?_pop, popK_size]
    rw [if_pos (by omega)]; exact ih (by omega)

theorem pushpop_keep (a : Array Val) (k : Nat) (v : Val) :
    ∀ i, i < a.size - k → ((popK a k).push v)[i]? = a[i]? := by
  intro i hi
  rw [Array.getElem?_push, popK_size, if_neg (by omega), popK_get a k i hi]

theorem pushpop_size (a : Array Val) (k : Nat) (v : Val) : ((popK a k).push v).size = a.size - k + 1 := by
  simp [popK_size]

theorem pushpop_num (a : Array Val) (k : Nat) (v : Val) (hv : isNum v)
    (ha : ∀ i, i < a.size → isNum (a[i]?.getD default)) :
    ∀ i, i < ((popK a k).push v).size → isNum (((popK a k).push v)[i]?.getD default) := by
  intro i hi
  rw [pushpop_size] at hi
  rw [Array.getElem?_push, popK_size]
  by_cases h : i = a.size - k
  · rw [if_pos h]; exact hv
  · rw [if_neg h, popK_get a k i (by omega)]; exact ha i (by omega)

theorem pushpop_top (a : Array Val) (k : Nat) (v : Val) :
    ((popK a k).push v)[a.size - k]?.getD default = v := by
  rw [Array.getElem?_push, popK_size, if_pos rfl]; rfl

theorem popK_two (a : Array Val) : popK a 2 = a.pop.pop := rfl
theorem popK_one (a : Array Val) : popK a 1 = a.pop := rfl
theorem popK_three (a : Array Val) : popK a 3 = a.pop.pop.pop := rfl

/-- The produced-list equivalence for "push one value at slot `n - k`". -/
theorem prod_one (a : Array Val) (k : Nat) (hk : k ≤ a.size) (v : Val) (t : Nat) (mr : Msg)
    (hmr : mr = enc 0 (a.size - k) v t) (x : Msg) :
    x ∈ ((List.range (((popK a k).push v).size - (a.size - k))).map fun d =>
        enc 0 (a.size - k + d) (((popK a k).push v)[a.size - k + d]?.getD default) t) ++
      (none : Option Nat).toList.map (fun j => enc 1 j (default : Val) t) ↔ x ∈ [mr] := by
  simp only [pushpop_size, List.mem_append, List.mem_map, List.mem_range, Option.toList_none,
    List.not_mem_nil, or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have : d = 0 := by omega
    subst this; rw [hmr, Nat.add_zero, pushpop_top]
  · rintro rfl; exact ⟨0, by omega, by rw [hmr, Nat.add_zero, pushpop_top]⟩

/-! ## relational ops and eqz -/

theorem step_relop (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {op fee : Nat} (hins : (X.pfOf E.k).code[pc]? = some (.num op)) (hop : op ∈ relops)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb)
    (hg64 : X.g0 < 2 ^ 64)
    (ma mb mr : Msg) (hma : live ma) (hmb : live mb)
    (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 2)
    (sb : mb.space = 0 ∧ mb.slot = s.stack.size - 1)
    (hmr : ∀ r, (ma.ok → mb.ok → r = Num.b2 (Num.relop (relW op) (relK op) ma.val mb.val)) →
      mr = enc 0 (s.stack.size - 2) (.i32 (UInt32.ofNat r)) t)
    (sem : True) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [ma, mb] [mr]) S_seg segb := by
  have hfam : isFamilyNum op = true ∧ numPops op = 2 := by
    simp only [relops, List.mem_cons, List.mem_nil_iff, or_false] at hop
    rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> decide
  obtain ⟨ls0, hL, hfl⟩ := R.labels; have hH := R.height; have hsbR := R.sbLe
  obtain ⟨h2, hnext, hL1, hH1⟩ := verify_straight X R.kLt R.pcLt hins hL hH (pops := 2) (pushes := 1)
    (by simp [kindOf, hfam.1, hfam.2]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  obtain ⟨ea, oka, va, -⟩ := R.stack_dec hma sa.1 sa.2 (by omega)
  obtain ⟨eb, okb, vb, -⟩ := R.stack_dec hmb sb.1 sb.2 (by omega)
  obtain ⟨r, hr⟩ : ∃ r, r = Num.b2 (Num.relop (relW op) (relK op) ma.val mb.val) := ⟨_, rfl⟩
  have emr := hmr r (fun _ _ => hr)
  apply step_straight X R hins hfee hg hg64 2 (by omega) ((popK s.stack 2).push (.i32 (UInt32.ofNat r))) f.locals none
    (pushpop_keep _ _ _) (by rw [pushpop_size]; omega) (pushpop_num _ _ _ trivial R.numS)
    rfl (fun _ _ => rfl) (by simp) R.numL hnext ⟨ls0, hL1, hfl⟩ (by rw [pushpop_size]; omega) (by rw [pushpop_size, hH1]; congr 1; omega)
  · rw [popK_two]
    simp only [exec, execNum_relop _ _ hop, popN_eq, pushI32, pushV, setFrame, R.frames, R.pcEq]
    rw [back_getD s.stack (by omega), back_getD s.stack.pop (by simp; omega)]
    simp only [Array.size_pop, Array.getElem?_pop]
    rw [if_pos (by omega), show s.stack.size - 1 - 1 = s.stack.size - 2 by omega, ← va, ← vb, hr]
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
    constructor
    · rintro ⟨d, hd, rfl⟩
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
      · left; rw [ea, Nat.add_zero]
      · right; rw [eb, show s.stack.size - 2 + 1 = s.stack.size - 1 by omega]
    · rintro (rfl | rfl)
      · exact ⟨0, by omega, by rw [ea, Nat.add_zero]⟩
      · exact ⟨1, by omega, by rw [eb, show s.stack.size - 2 + 1 = s.stack.size - 1 by omega]⟩
  · exact prod_one s.stack 2 (by omega) _ t mr emr

theorem step_eqz (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {op fee : Nat} (hins : (X.pfOf E.k).code[pc]? = some (.num op)) (hop : op = 0x45 ∨ op = 0x50)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb)
    (hg64 : X.g0 < 2 ^ 64)
    (ma mr : Msg) (hma : live ma) (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 1)
    (hmr : ∀ r, (ma.ok → r = Num.b2 (ma.val = 0)) → mr = enc 0 (s.stack.size - 1) (.i32 (UInt32.ofNat r)) t) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [ma] [mr]) S_seg segb := by
  have hfam : isFamilyNum op = true ∧ numPops op = 1 := by rcases hop with rfl | rfl <;> decide
  obtain ⟨ls0, hL, hfl⟩ := R.labels; have hH := R.height; have hsbR := R.sbLe
  obtain ⟨h1, hnext, hL1, hH1⟩ := verify_straight X R.kLt R.pcLt hins hL hH (pops := 1) (pushes := 1)
    (by simp [kindOf, hfam.1, hfam.2]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  obtain ⟨ea, oka, va, -⟩ := R.stack_dec hma sa.1 sa.2 (by omega)
  obtain ⟨r, hr⟩ : ∃ r, r = Num.b2 (ma.val = 0) := ⟨_, rfl⟩
  have emr := hmr r (fun _ => hr)
  apply step_straight X R hins hfee hg hg64 1 (by omega) ((popK s.stack 1).push (.i32 (UInt32.ofNat r))) f.locals none
    (pushpop_keep _ _ _) (by rw [pushpop_size]; omega) (pushpop_num _ _ _ trivial R.numS)
    rfl (fun _ _ => rfl) (by simp) R.numL hnext ⟨ls0, hL1, hfl⟩ (by rw [pushpop_size]; omega) (by rw [pushpop_size, hH1]; congr 1; omega)
  · rw [popK_one]
    simp only [exec, execNum_eqz _ _ hop, popN_eq, pushI32, pushV, setFrame, R.frames, R.pcEq]
    rw [back_getD s.stack (by omega), ← va, hr]
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
    constructor
    · rintro ⟨d, hd, rfl⟩
      have : d = 0 := by omega
      subst this; rw [ea, Nat.add_zero]
    · rintro rfl; exact ⟨0, by omega, by rw [ea, Nat.add_zero]⟩
  · exact prod_one s.stack 1 (by omega) _ t mr emr

/-! ## select -/

theorem pop_get (a : Array Val) (i : Nat) (h : i + 1 < a.size) : a.pop[i]? = a[i]? := by
  rw [Array.getElem?_pop, if_pos (by omega)]

theorem step_select (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {ty : Option VT} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.select ty))
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (mc m2 m1 mr : Msg) (hmc : live mc) (hm2 : live m2) (hm1 : live m1)
    (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1) (s2 : m2.space = 0 ∧ m2.slot = s.stack.size - 2)
    (s1 : m1.space = 0 ∧ m1.slot = s.stack.size - 3)
    (hmr : mc.ok → m1.ok → m2.ok →
      mr = enc 0 (s.stack.size - 3) (if mc.val = 0 then m2.toVal else m1.toVal) t) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [mc, m2, m1] [mr]) S_seg segb := by
  obtain ⟨ls0, hL, hfl⟩ := R.labels; have hH := R.height; have hsbR := R.sbLe
  obtain ⟨h3, hnext, hL1, hH1⟩ := verify_straight X R.kLt R.pcLt hins hL hH (pops := 3) (pushes := 1)
    (by simp [kindOf]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  obtain ⟨e2, ok2, -, tv2⟩ := R.stack_dec hm2 s2.1 s2.2 (by omega)
  obtain ⟨e1, ok1, -, tv1⟩ := R.stack_dec hm1 s1.1 s1.2 (by omega)
  have emr := hmr okc ok1 ok2
  obtain ⟨v, hv⟩ : ∃ v, v = (if mc.val = 0 then m2.toVal else m1.toVal) := ⟨_, rfl⟩
  have hnum : isNum v := by rw [hv]; split <;> exact isNum_toVal _
  rw [← hv] at emr
  apply step_straight X R hins hfee hg hg64 3 (by omega) ((popK s.stack 3).push v) f.locals none
    (pushpop_keep _ _ _) (by rw [pushpop_size]; omega) (pushpop_num _ _ _ hnum R.numS)
    rfl (fun _ _ => rfl) (by simp) R.numL hnext ⟨ls0, hL1, hfl⟩ (by rw [pushpop_size]; omega) (by rw [pushpop_size, hH1]; congr 1; omega)
  · rw [popK_three]
    simp only [exec, popN_eq, popV_eq, pushV, setFrame, R.frames, R.pcEq]
    rw [back_getD s.stack (by omega), back_getD s.stack.pop (by simp; omega),
      back_getD s.stack.pop.pop (by simp; omega)]
    simp only [Array.size_pop]
    rw [show s.stack.size - 1 - 1 = s.stack.size - 2 by omega,
      show s.stack.size - 2 - 1 = s.stack.size - 3 by omega,
      pop_get s.stack.pop (s.stack.size - 3) (by simp; omega), pop_get s.stack (s.stack.size - 3) (by omega),
      pop_get s.stack (s.stack.size - 2) (by omega), ← vc, ← tv1, ← tv2, hv]
    by_cases h0 : mc.val = 0 <;> simp [h0]
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
    constructor
    · rintro ⟨d, hd, rfl⟩
      rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
      · right; right; rw [e1, Nat.add_zero]
      · right; left; rw [e2, show s.stack.size - 3 + 1 = s.stack.size - 2 by omega]
      · left; rw [ec, show s.stack.size - 3 + 2 = s.stack.size - 1 by omega]
    · rintro (rfl | rfl | rfl)
      · exact ⟨2, by omega, by rw [ec, show s.stack.size - 3 + 2 = s.stack.size - 1 by omega]⟩
      · exact ⟨1, by omega, by rw [e2, show s.stack.size - 3 + 1 = s.stack.size - 2 by omega]⟩
      · exact ⟨0, by omega, by rw [e1, Nat.add_zero]⟩
  · exact prod_one s.stack 3 (by omega) _ t mr emr

/-! ## locals -/

theorem set_getElem? (a : Array Val) (x j : Nat) (v : Val) (hx : x < a.size) :
    (a.set! x v)[j]? = if j = x then some v else a[j]? := by
  grind

theorem step_localGet (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {x fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.localGet x)) (hx : x < f.locals.size)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (ml : Msg) (hml : live ml) (sl : ml.space = E.lsp ∧ ml.slot = x)
    (mo ms : Msg) (hmo : ml.ok → mo = enc E.lsp x ml.toVal t) (hms : ml.ok → ms = enc 0 s.stack.size ml.toVal t) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [ml] [ms, mo]) S_seg segb := by
  obtain ⟨ls0, hL, hfl⟩ := R.labels; have hH := R.height; have hsbR := R.sbLe
  obtain ⟨-, hnext, hL1, hH1⟩ := verify_straight X R.kLt R.pcLt hins hL hH (pops := 0) (pushes := 1)
    (by simp [kindOf]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  obtain ⟨el, okl, -, tvl⟩ := R.local_dec hml sl.1 sl.2 hx
  have emo := hmo okl; have ems := hms okl
  rw [tvl] at emo ems
  have hnum := R.numL x hx
  apply step_straight X R hins hfee hg hg64 0 (Nat.zero_le _)
    ((popK s.stack 0).push (f.locals[x]?.getD default)) f.locals (some x)
    (pushpop_keep _ _ _) (by rw [pushpop_size]; omega) (pushpop_num _ _ _ hnum R.numS)
    rfl (fun _ _ => rfl) (fun j hj => by cases hj; exact hx) R.numL hnext ⟨ls0, hL1, hfl⟩ (by rw [pushpop_size]; omega) (by rw [pushpop_size, hH1]; congr 1; omega)
  · simp only [exec, pushV, setFrame, R.frames, R.pcEq, popK]; rfl
  · intro y
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_some, List.not_mem_nil,
      or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false, List.range_zero, List.map_nil,
      List.nil_append]
    constructor
    · rintro ⟨j, rfl, rfl⟩; rw [el]
    · rintro rfl; exact ⟨x, rfl, el.symm⟩
  · intro y
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_some, List.mem_cons,
      List.mem_nil_iff, or_false, pushpop_size, Nat.sub_zero]
    constructor
    · rintro (⟨d, hd, rfl⟩ | ⟨j, rfl, rfl⟩)
      · left; have : d = 0 := by omega
        subst this; rw [ems, Nat.add_zero]; simp [popK, Array.getElem?_push]
      · right; rw [emo]
    · rintro (rfl | rfl)
      · left; exact ⟨0, by omega, by rw [ems, Nat.add_zero]; simp [popK, Array.getElem?_push]⟩
      · right; exact ⟨x, rfl, by rw [emo]⟩

theorem step_localSet (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {x fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.localSet x)) (hx : x < f.locals.size)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (mv ml mo : Msg) (hmv : live mv) (hml : live ml) (sv : mv.space = 0 ∧ mv.slot = s.stack.size - 1)
    (sl : ml.space = E.lsp ∧ ml.slot = x) (hmo : mv.ok → mo = enc E.lsp x mv.toVal t) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [mv, ml] [mo]) S_seg segb := by
  obtain ⟨ls0, hL, hfl⟩ := R.labels; have hH := R.height; have hsbR := R.sbLe
  obtain ⟨h1, hnext, hL1, hH1⟩ := verify_straight X R.kLt R.pcLt hins hL hH (pops := 1) (pushes := 0)
    (by simp [kindOf]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  obtain ⟨ev, okv, -, tvv⟩ := R.stack_dec hmv sv.1 sv.2 (by omega)
  obtain ⟨el, -, -, -⟩ := R.local_dec hml sl.1 sl.2 hx
  have emo := hmo okv
  rw [tvv] at emo
  have hnum := R.numS (s.stack.size - 1) (by omega)
  have hsz : s.stack.pop.size = s.stack.size - 1 + 0 := by simp
  apply step_straight X R hins hfee hg hg64 1 (by omega) s.stack.pop
    (f.locals.set! x (s.stack[s.stack.size - 1]?.getD default)) (some x)
    (by intro i hi; simp only [Array.getElem?_pop]; rw [if_pos (by omega)]) (by simp)
    (by intro i hi; simp only [Array.size_pop] at hi; simp only [Array.getElem?_pop]
        rw [if_pos (by omega)]; exact R.numS i (by omega))
    (by simp) (fun j hj => by rw [set_getElem? _ _ _ _ hx, if_neg (fun h => hj (by rw [h]))])
    (fun j hj => by cases hj; exact hx)
    (by intro j hj; simp only [Array.size_set!] at hj; rw [set_getElem? _ _ _ _ hx]
        split
        · exact hnum
        · exact R.numL j hj)
    hnext ⟨ls0, hL1, hfl⟩ (by rw [hsz]; omega) (by rw [hsz, hH1]; congr 1; omega)
  · simp only [exec, popV_eq, setFrame, R.frames, R.pcEq]
    rw [back_getD s.stack (by omega)]
  · intro y
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_some, List.mem_cons,
      List.mem_nil_iff, or_false]
    constructor
    · rintro (⟨d, hd, rfl⟩ | ⟨j, rfl, rfl⟩)
      · left; have : d = 0 := by omega
        subst this; rw [ev, Nat.add_zero]
      · right; rw [el]
    · rintro (rfl | rfl)
      · left; exact ⟨0, by omega, by rw [ev, Nat.add_zero]⟩
      · right; exact ⟨x, rfl, el.symm⟩
  · intro y
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_some, List.mem_cons,
      List.mem_nil_iff, or_false, Array.size_pop]
    constructor
    · rintro (⟨d, hd, _⟩ | ⟨j, rfl, rfl⟩)
      · omega
      · rw [emo, set_getElem? _ _ _ _ hx, if_pos rfl]; rfl
    · rintro rfl; right; exact ⟨x, rfl, by rw [emo, set_getElem? _ _ _ _ hx, if_pos rfl]; rfl⟩

theorem step_localTee (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {x fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.localTee x)) (hx : x < f.locals.size)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (mv ml mo ms : Msg) (hmv : live mv) (hml : live ml) (sv : mv.space = 0 ∧ mv.slot = s.stack.size - 1)
    (sl : ml.space = E.lsp ∧ ml.slot = x) (hmo : mv.ok → mo = enc E.lsp x mv.toVal t)
    (hms : mv.ok → ms = enc 0 (s.stack.size - 1) mv.toVal t) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [mv, ml] [ms, mo]) S_seg segb := by
  obtain ⟨ls0, hL, hfl⟩ := R.labels; have hH := R.height; have hsbR := R.sbLe
  obtain ⟨h1, hnext, hL1, hH1⟩ := verify_straight X R.kLt R.pcLt hins hL hH (pops := 1) (pushes := 1)
    (by simp [kindOf]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  obtain ⟨ev, okv, -, tvv⟩ := R.stack_dec hmv sv.1 sv.2 (by omega)
  obtain ⟨el, -, -, -⟩ := R.local_dec hml sl.1 sl.2 hx
  have emo := hmo okv; have ems := hms okv
  rw [tvv] at emo ems
  have hnum := R.numS (s.stack.size - 1) (by omega)
  apply step_straight X R hins hfee hg hg64 1 (by omega) s.stack
    (f.locals.set! x (s.stack[s.stack.size - 1]?.getD default)) (some x)
    (fun i _ => rfl) (by omega) R.numS
    (by simp) (fun j hj => by rw [set_getElem? _ _ _ _ hx, if_neg (fun h => hj (by rw [h]))])
    (fun j hj => by cases hj; exact hx)
    (by intro j hj; simp only [Array.size_set!] at hj; rw [set_getElem? _ _ _ _ hx]
        split
        · exact hnum
        · exact R.numL j hj)
    hnext ⟨ls0, hL1, hfl⟩ (by omega) (by rw [hH1]; congr 1; omega)
  · simp only [exec, setFrame, R.frames, R.pcEq]
    rw [back_getD s.stack (by omega)]
  · intro y
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_some, List.mem_cons,
      List.mem_nil_iff, or_false]
    constructor
    · rintro (⟨d, hd, rfl⟩ | ⟨j, rfl, rfl⟩)
      · left; have : d = 0 := by omega
        subst this; rw [ev, Nat.add_zero]
      · right; rw [el]
    · rintro (rfl | rfl)
      · left; exact ⟨0, by omega, by rw [ev, Nat.add_zero]⟩
      · right; exact ⟨x, rfl, el.symm⟩
  · intro y
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_some, List.mem_cons,
      List.mem_nil_iff, or_false]
    constructor
    · rintro (⟨d, hd, rfl⟩ | ⟨j, rfl, rfl⟩)
      · left; have : d = 0 := by omega
        subst this; rw [ems, Nat.add_zero]
      · right; rw [emo, set_getElem? _ _ _ _ hx, if_pos rfl]; rfl
    · rintro (rfl | rfl)
      · left; exact ⟨0, by omega, by rw [ems, Nat.add_zero]⟩
      · right; exact ⟨x, rfl, by rw [emo, set_getElem? _ _ _ _ hx, if_pos rfl]; rfl⟩

end WasmBase
