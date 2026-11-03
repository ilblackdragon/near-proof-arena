import WasmBase.Step
/-!
# WasmBase.StepOps — the spec step of each instruction class, from event messages

Each lemma takes the simulation relation at time `t`, the consumed messages (which the channel
argument shows are live) and the produced messages with the local semantic guarantee of the chip
(`*_sound` in `WasmBase.Local.*`), and returns the spec step and the relation at `t + 1`.
-/
namespace WasmBase

variable {S_seg segb : Nat}
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

theorem stepLive_congr {live : Msg → Prop} {c1 c2 p1 p2 : List Msg}
    (hc : ∀ x, x ∈ c1 ↔ x ∈ c2) (hp : ∀ x, x ∈ p1 ↔ x ∈ p2) :
    stepLive live c1 p1 = stepLive live c2 p2 := by
  funext x; simp only [stepLive, hc, hp]

theorem Rel_congr {X : Ctx} {s : St} {t k pc S sb cid : Nat} {live live' : Msg → Prop} {S_seg segb : Nat}
    (h : Rel X s t k pc S sb cid live S_seg segb) (e : live = live') :
    Rel X s t k pc S sb cid live' S_seg segb := by
  obtain ⟨E, f, tps, tpl, h1, h2, h3, hw⟩ := h
  exact ⟨E, f, tps, tpl, h1, h2, h3, e ▸ hw⟩

theorem Rel_of_RelW_congr {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live live' : Msg → Prop} (h : RelW X E s f tps tpl t pc S live S_seg segb) (e : live = live') :
    Rel X s t E.k pc S E.sb E.cid live' S_seg segb := ⟨E, f, tps, tpl, rfl, rfl, rfl, e ▸ h⟩

theorem isFamilyNum_of_binop {op : Nat} (h : isBinop op) : isFamilyNum op = true ∧ numPops op = 2 := by
  simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;> decide

theorem step_binop (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {op fee : Nat} (hins : (X.pfOf E.k).code[pc]? = some (.num op)) (hop : isBinop op)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb)
    (hg64 : X.g0 < 2 ^ 64)
    (ma mb mr : Msg) (hma : live ma) (hmb : live mb)
    (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 2)
    (sb : mb.space = 0 ∧ mb.slot = s.stack.size - 1)
    (sr : mr.space = 0 ∧ mr.slot = s.stack.size - 2 ∧ mr.tp = t ∧
      mr.tag = (if opW op = 64 then 1 else 0))
    (sem : ma.ok → mb.ok → mr.ok ∧ Num.binop (opW op) (opK op) ma.val mb.val = some mr.val) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [ma, mb] [mr]) S_seg segb := by
  have F := (X.factsOf R.kLt)
  obtain ⟨hfam, hpops⟩ := isFamilyNum_of_binop hop
  have hv := F.verify pc R.pcLt _ hins (by m2_ns)
  obtain ⟨ls0, hL, hfl⟩ := R.labels
  have hH := R.height
  have hsb := R.sbLe
  simp only [verifyAt, hins, hL, hH, kindOf, hfam, ite_true, hpops, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨h2, ⟨hnext, hL1⟩, hH1⟩ := hv
  -- the consumed messages are the top two stack entries
  have ea := R.stack_msg hma sa.1 (by omega)
  have eb := R.stack_msg hmb sb.1 (by omega)
  rw [sa.2] at ea; rw [sb.2] at eb
  have na := R.numS (s.stack.size - 2) (by omega)
  have nb := R.numS (s.stack.size - 1) (by omega)
  have oka : ma.ok := by rw [ea]; exact enc_ok na _ _ _
  have okb : mb.ok := by rw [eb]; exact enc_ok nb _ _ _
  obtain ⟨okr, hbin⟩ := sem oka okb
  have va : ma.val = vNum (s.stack[s.stack.size - 2]?.getD default) := by rw [ea]; exact enc_val na _ _ _
  have vb : mb.val = vNum (s.stack[s.stack.size - 1]?.getD default) := by rw [eb]; exact enc_val nb _ _ _
  -- the spec step
  rw [step_eq_exec X R hins hfee hg hg64]
  have hpopb : (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).1 = mb.val := by
    rw [popN_eq, vb]; simp only; rw [back_getD _ (by omega)]
  have hpopa : (popN (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).2).1 = ma.val := by
    rw [popN_eq, popN_eq, va]; simp only
    rw [back_getD _ (by simp; omega)]
    simp only [Array.size_pop, Array.getElem?_pop]
    rw [if_pos (by omega)]
    congr 2
  let v : Val := if opW op = 32 then .i32 (UInt32.ofNat mr.val) else .i64 (UInt64.ofNat mr.val)
  refine ⟨setFrame ({ s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := s.stack.pop.pop.push v })
    { f with pc := f.pc + 1 }, ?_, ?_⟩
  · simp only [exec, execNum_binop _ _ hop, hpopb, hpopa, hbin]
    split <;> simp [v, *, pushI32, pushI64, pushV, popN_eq]
  · have hw : opW op = 32 ∨ opW op = 64 := by unfold opW; split <;> simp
    have hvr : v = mr.toVal := by
      simp only [v, Msg.toVal, sr.2.2.2]
      rcases hw with hw | hw <;> simp [hw]
    have emr : mr = enc 0 (s.stack.size - 2) v t := by
      rw [hvr, ← sr.1, ← sr.2.1, ← sr.2.2.1]; exact (enc_of_ok okr).symm
    have hsz' : (s.stack.pop.pop.push v).size = s.stack.size - 1 := by simp; omega
    have SR := straight_rel X R (k := 2) (fee := fee) (by omega) (s.stack.pop.pop.push v) f.locals none
      (by intro i hi; simp only [Array.getElem?_push, Array.getElem?_pop, Array.size_pop]
          rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)])
      (by omega)
      (by intro i hi
          simp only [Array.getElem?_push, Array.getElem?_pop, Array.size_pop] at hi ⊢
          by_cases hi' : i = s.stack.size - 1 - 1
          · rw [if_pos hi']; rw [hvr]; exact isNum_toVal mr
          · rw [if_neg hi', if_pos (by omega), if_pos (by omega)]; exact R.numS i (by omega))
      rfl (fun _ _ => rfl) (by simp) R.numL hnext ⟨ls0, hL1, hfl⟩ (by rw [hsz']; omega)
      (by rw [hsz', hH1]; congr 1; omega) hg
      (setFrame ({ s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := s.stack.pop.pop.push v })
        { f with pc := f.pc + 1 })
      (by simp [setFrame, R.frames]) (by simp [setFrame, R.frames, R.pcEq]) (by simp [setFrame, R.frames])
      (by simp [setFrame, R.frames]) (by simp [setFrame, R.frames]) (by simp [setFrame, R.frames])
    refine Rel_of_RelW_congr SR (stepLive_congr ?_ ?_)
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
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, List.mem_cons, List.mem_nil_iff, hsz', false_and, exists_false]
      constructor
      · rintro ⟨d, hd, rfl⟩
        have : d = 0 := by omega
        subst this
        rw [emr]; simp only [Nat.add_zero, Array.getElem?_push, Array.size_pop]
        rw [if_pos (by omega)]; rfl
      · rintro rfl
        refine ⟨0, by omega, ?_⟩
        rw [emr]; simp only [Nat.add_zero, Array.getElem?_push, Array.size_pop]
        rw [if_pos (by omega)]; rfl

end WasmBase

namespace WasmBase
open NearSpecV3.Wasm
variable {S_seg segb : Nat}

/-- A trapping binary op (div/rem by zero, signed overflow): the spec step aborts, having charged
the fee. -/
theorem step_binop_trap (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {op fee : Nat} (hins : (X.pfOf E.k).code[pc]? = some (.num op)) (hop : isBinop op)
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee) (hg : X.R * (S + fee - S_seg) ≤ segb)
    (hg64 : X.g0 < 2 ^ 64)
    (ma mb : Msg) (hma : live ma) (hmb : live mb)
    (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 2)
    (sb : mb.space = 0 ∧ mb.slot = s.stack.size - 1)
    (sem : ma.ok → mb.ok → Num.binop (opW op) (opK op) ma.val mb.val = none) :
    ∃ sN e, step X.cfg X.p s = .abort sN e ∧ X.R * (S + fee - S_seg) + sN.gas.g = segb := by
  have F := (X.factsOf R.kLt)
  obtain ⟨hfam, hpops⟩ := isFamilyNum_of_binop hop
  have hv := F.verify pc R.pcLt _ hins (by m2_ns)
  obtain ⟨ls0, hL, hfl⟩ := R.labels
  have hH := R.height
  have hsb := R.sbLe
  simp only [verifyAt, hins, hL, hH, kindOf, hfam, ite_true, hpops, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨h2, -, -⟩ := hv
  have ea := R.stack_msg hma sa.1 (by omega)
  have eb := R.stack_msg hmb sb.1 (by omega)
  rw [sa.2] at ea; rw [sb.2] at eb
  have na := R.numS (s.stack.size - 2) (by omega)
  have nb := R.numS (s.stack.size - 1) (by omega)
  have oka : ma.ok := by rw [ea]; exact enc_ok na _ _ _
  have okb : mb.ok := by rw [eb]; exact enc_ok nb _ _ _
  have hbin := sem oka okb
  have va : ma.val = vNum (s.stack[s.stack.size - 2]?.getD default) := by rw [ea]; exact enc_val na _ _ _
  have vb : mb.val = vNum (s.stack[s.stack.size - 1]?.getD default) := by rw [eb]; exact enc_val nb _ _ _
  rw [step_eq_exec X R hins hfee hg hg64]
  have hpopb : (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).1 = mb.val := by
    rw [popN_eq, vb]; simp only; rw [back_getD _ (by omega)]
  have hpopa : (popN (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).2).1 = ma.val := by
    rw [popN_eq, popN_eq, va]; simp only
    rw [back_getD _ (by simp; omega)]
    simp only [Array.size_pop, Array.getElem?_pop]
    rw [if_pos (by omega)]
    congr 2
  refine ⟨{ s with gas := { s.gas with g := s.gas.g - X.R * fee } }, trapStr "IllegalArithmetic", ?_, ?_⟩
  · have htr : (trapStr "IllegalArithmetic").startsWith "WasmTrap" = true := by decide +kernel
    simp only [exec, execNum_binop _ _ hop, hpopb, hpopa, hbin, htr, ite_true]
  · exact R.step_gas hg rfl

end WasmBase
