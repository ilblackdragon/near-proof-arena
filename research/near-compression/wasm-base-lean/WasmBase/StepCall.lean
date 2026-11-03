import WasmBase.StepCtrl
import WasmBase.StepMem
/-!
# WasmBase.StepCall — `call` and the return from a callee

`step_call`: a `call` of a checked function pushes a frame (params moved from the operand stack into
the callee's locals, declared locals zero), produces a call record and decrements the stack budget;
the relation moves to the callee with the caller saved on the chain (`Chain`).  `step_return`: a
return at activation `cid ≠ 0` pops the frame (under D3 the operand stack is unchanged), consumes
the call record, restores the budget, and the callee's locals become dead.
-/
namespace WasmBase
variable {S_seg segb : Nat}
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

theorem HeapOK.congr {E E' : Env} {s s' : St} {t t' : Nat} (H : HeapOK E s t)
    (hl : ∀ x, x.space = 2 ∨ x.space = 3 → (E'.live x ↔ E.live x))
    (hpg : s'.pages = s.pages) (hgl : s'.globals = s.globals) (ht : t ≤ t') : HeapOK E' s' t' := by
  have H' := H.mono hpg hgl ht
  obtain ⟨T, tpm, hnd, hlt, htp, hv⟩ := H'.mem
  obtain ⟨tpg, hg, hgv⟩ := H'.glob
  exact ⟨H'.pages, ⟨T, tpm, hnd, hlt, htp, fun x hx => by rw [hl x (Or.inr hx)]; exact hv x hx⟩,
    ⟨tpg, hg, fun x hx => by rw [hl x (Or.inl hx)]; exact hgv x hx⟩⟩

/-- The verification facts of a `call`. -/
theorem verify_call (X : Ctx) {k : Nat} (hkn : k < X.nf) {pc fi : Nat} {ls : List Label} {h : Nat}
    (hpc : pc < (X.pfOf k).code.size) (hins : (X.pfOf k).code[pc]? = some (.call fi))
    (hfi : X.p.m.imports.size ≤ fi)
    (hL : (X.ckOf k).labels[pc]? = some ls) (hH : (X.ckOf k).heights[pc]? = some h) :
    ∃ np ar, sigOf X.p fi = some (np, ar) ∧ np ≤ h ∧ pc + 1 < (X.pfOf k).code.size ∧
      (X.ckOf k).labels[pc + 1]? = some ls ∧ (X.ckOf k).heights[pc + 1]? = some (h - np + ar) := by
  have hv := (X.factsOf hkn).verify pc hpc _ hins (by simp [m2Special]; omega)
  unfold verifyAt at hv
  rw [hins, hL, hH] at hv
  simp only at hv
  cases hs : sigOf X.p fi with
  | none => rw [hs] at hv; simp at hv
  | some na =>
    obtain ⟨np, ar⟩ := na
    rw [hs] at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hv
    exact ⟨np, ar, rfl, h1, h2, h3, h4⟩

/-- The callee of a call record: a checked function whose entry is the record's target. -/
theorem cinfo_spec (X : Ctx) {fi e : Nat} (h : X.cinfo fi = some e) :
    ∃ kc, kc < X.nf ∧ X.fnOf kc + X.p.m.imports.size = fi ∧ X.offOf kc = e := by
  unfold Ctx.cinfo callInfo at h
  split at h
  · rename_i hle
    cases hi : X.M.fns.idxOf? (fi - X.p.m.imports.size) with
    | none => rw [hi] at h; simp at h
    | some kc =>
      rw [hi] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
      refine ⟨kc, hlt, ?_, h⟩
      unfold Ctx.fnOf
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some, heq]
      omega
  · simp at h

/-- The signature of a checked callee. -/
theorem sigOf_callee (X : Ctx) {kc fi np ar : Nat} (hkc : kc < X.nf) (hfi : X.fnOf kc + X.p.m.imports.size = fi)
    (hs : sigOf X.p fi = some (np, ar)) :
    np = (X.pfOf kc).type.params.size ∧ ar = (X.pfOf kc).type.results.size := by
  have hf := (X.factsOf hkc).func
  unfold sigOf at hs
  rw [if_pos (by omega), show fi - X.p.m.imports.size = X.fnOf kc by omega, hf] at hs
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
  exact ⟨hs.1.symm, hs.2.symm⟩

/-- Activation ids decrease along the chain. -/
theorem Chain.cids_lt {X : Ctx} {t : Nat} :
    ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved}, Chain X t cid sb k rest sv → ∀ c ∈ sv, c.cid < cid
  | _, _, _, [], [], _ => by simp
  | _, _, _, _ :: _, c :: sv, h => by
    obtain ⟨-, -, -, -, a5, -, -, -, -, -, -, -, a13⟩ := h
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact a5
    · have := Chain.cids_lt a13 c' hc'; omega
  | _, _, _, [], _ :: _, h => h.elim
  | _, _, _, _ :: _, [], h => h.elim

/-- Chain messages are call records (space 4) or locals of a saved caller. -/
theorem chainMsgs_space {X : Ctx} :
    ∀ {cid k : Nat} {rest : List Frame} {sv : List Saved} {x : Msg}, chainMsgs X cid k rest sv x →
      x.space = 4 ∨ ∃ c ∈ sv, x.space = 16 + c.cid
  | _, _, [], _, _, h => by cases ‹List Saved› <;> simp [chainMsgs] at h
  | _, _, _ :: _, [], _, h => by simp [chainMsgs] at h
  | _, _, fc :: rest, c :: sv, x, h => by
    rcases h with rfl | h | h
    · exact Or.inl rfl
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h
      exact Or.inr ⟨c, List.mem_cons_self, by simp [enc]⟩
    · rcases chainMsgs_space h with h | ⟨c', hc', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', h⟩

/-- Call-record slots along the chain are activation ids `≤ cid`. -/
theorem chainMsgs_rec_slot {X : Ctx} {t : Nat} :
    ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved} {x : Msg}, Chain X t cid sb k rest sv →
      chainMsgs X cid k rest sv x → x.space = 4 → x.slot ≤ cid
  | _, _, _, [], _, _, _, h, _ => by cases ‹List Saved› <;> simp [chainMsgs] at h
  | _, _, _, _ :: _, [], _, _, h, _ => by simp [chainMsgs] at h
  | _, _, _, fc :: rest, c :: sv, x, hc, h, hs => by
    obtain ⟨-, -, -, -, a5, -, -, -, -, -, -, -, a13⟩ := hc
    rcases h with rfl | h | h
    · simp [callMsg]
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc] at hs; omega
    · have := chainMsgs_rec_slot a13 h hs; omega

end WasmBase

namespace WasmBase
variable {S_seg segb : Nat}
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-- The spec state after a `call` of checked function `kc`. -/
def callState (X : Ctx) (s : St) (f : Frame) (rest : List Frame) (pc fee kc : Nat) : St :=
  let pfc := X.pfOf kc
  let base := s.stack.size - pfc.type.params.size
  { s with gas := { s.gas with g := s.gas.g - X.R * fee - pfc.prologueGas },
           stackRem := s.stackRem - pfc.stackCharge, stack := s.stack.extract 0 base,
           frames := { fn := X.fnOf kc, pc := 0,
                       locals := s.stack.extract base s.stack.size ++ pfc.locals.map Val.default,
                       labels := [{ target := pfc.code.size, arity := pfc.type.results.size, height := base,
                                    isLoop := false }],
                       base := base } :: { f with pc := pc + 1 } :: rest }

theorem step_call_spec (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {fi fee kc : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.call fi))
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hkc : kc < X.nf) (hfi : X.fnOf kc + X.p.m.imports.size = fi)
    (hg : X.R * (S + (fee + (X.ckOf kc).prologue) - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (hrem : (X.pfOf kc).stackCharge ≤ s.stackRem) :
    step X.cfg X.p s = .cont (callState X s f E.rest pc fee kc) := by
  have CFc := X.factsOf hkc
  have hgas := R.gas
  have hpro := CFc.prologue
  have hpro' : X.R * (X.ckOf kc).prologue = (X.pfOf kc).prologueGas := by
    unfold Ctx.R; rw [Nat.mul_comm]; exact hpro
  have hg1 : X.R * (S + fee - S_seg) ≤ segb := by
    have : X.R * (S + fee - S_seg) ≤ X.R * (S + (fee + (X.ckOf kc).prologue) - S_seg) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  rw [step_eq_exec X R hins hfee hg1 hg64]
  simp only [exec]
  unfold callFunc
  rw [dif_neg (by omega)]
  unfold enter
  dsimp only
  rw [show fi - X.p.m.imports.size = X.fnOf kc by omega, CFc.func]
  simp only [setFrame, R.frames, R.pcEq]
  rw [if_neg (by omega)]
  have e1 : X.R * (S + (fee + (X.ckOf kc).prologue)) = X.R * S + X.R * fee + X.R * (X.ckOf kc).prologue := by
    rw [Nat.mul_add, Nat.mul_add, Nat.add_assoc]
  have hgl : X.R * fee + (X.pfOf kc).prologueGas ≤ s.gas.g := by
    have h1 := R.gas
    have hm : X.R * (S + (fee + (X.ckOf kc).prologue) - S_seg) =
        X.R * (S - S_seg) + X.R * fee + X.R * (X.ckOf kc).prologue := by
      rw [← Nat.mul_add, ← Nat.mul_add]; congr 1
      have := R.segLt; omega
    rw [hm, hpro'] at hg
    omega
  have hgs : s.gas.g ≤ segb := by
    have h1 := R.gas; omega
  have hamt : ¬ (0 * (Fee.const (X.pfOf kc).prologueGas).l + (Fee.const (X.pfOf kc).prologueGas).c ≥ u64Bound) := by
    simp only [Fee.const, Nat.zero_mul, Nat.zero_add, u64Bound]
    rw [← hpro']
    have h2 := R.segbLt
    omega
  have hle : ¬ (0 * (Fee.const (X.pfOf kc).prologueGas).l + (Fee.const (X.pfOf kc).prologueGas).c > s.gas.g - X.R * fee) := by
    simp only [Fee.const, Nat.zero_mul, Nat.zero_add]
    omega
  simp only [charge, hamt, hle, ite_false]
  simp only [callState, Fee.const, Nat.zero_mul, Nat.zero_add]

end WasmBase

namespace WasmBase
variable {S_seg segb : Nat}
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

theorem isNum_default {t : VT} (h : t = .i32 ∨ t = .i64) : isNum (Val.default t) := by
  rcases h with rfl | rfl <;> trivial

set_option maxHeartbeats 1600000 in
/-- **`call`**: the relation moves to the callee (`kc`, local pc 0, activation id `t`, base
`size − np`), with the caller saved on the chain. -/
theorem step_call (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {fi fee kc : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some (.call fi))
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hkc : kc < X.nf) (hfi : X.fnOf kc + X.p.m.imports.size = fi)
    (hg : X.R * (S + (fee + (X.ckOf kc).prologue) - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64)
    (hrem : (X.pfOf kc).stackCharge ≤ s.stackRem)
    (hsbL : s.stack.size - (X.pfOf kc).type.params.size < 2 ^ 28) (htL : t < 2 ^ 28)
    {tpb : Nat} (hbud : live (budMsg s.stackRem tpb)) :
    step X.cfg X.p s = .cont (callState X s f E.rest pc fee kc) ∧
    Rel X (callState X s f E.rest pc fee kc) (t + 1) kc 0 (S + (fee + (X.ckOf kc).prologue))
        (s.stack.size - (X.pfOf kc).type.params.size) t
        (stepLive live
          ((List.range (X.pfOf kc).type.params.size).map (fun d =>
              enc 0 (s.stack.size - (X.pfOf kc).type.params.size + d)
                (s.stack[s.stack.size - (X.pfOf kc).type.params.size + d]?.getD default)
                (tps (s.stack.size - (X.pfOf kc).type.params.size + d))) ++ [budMsg s.stackRem tpb])
          (localView (16 + t) (s.stack.extract (s.stack.size - (X.pfOf kc).type.params.size) s.stack.size ++
              (X.pfOf kc).locals.map Val.default) (fun _ => t) ++
            [callMsg t (X.offOf E.k + (pc + 1)) E.sb E.cid (X.pfOf kc).stackCharge t,
             budMsg (s.stackRem - (X.pfOf kc).stackCharge) t])) S_seg segb := by
  refine ⟨step_call_spec X R hins hfee hkc hfi hg hg64 hrem, ?_⟩
  have CFc := X.factsOf hkc
  obtain ⟨ls0, hL0, hfl0⟩ := R.labels
  have hH := R.height
  obtain ⟨np', ar', hsig, hnp, hnext, hL1, hH1⟩ := verify_call X R.kLt R.pcLt hins (by omega) hL0 hH
  obtain ⟨enp, ear⟩ := sigOf_callee X hkc hfi hsig
  subst enp ear
  have hsbR := R.sbLe
  have hcidT := R.calls.cidLtT
  obtain ⟨sv, hch, hin, hout, hrl⟩ := R.calls.chain
  obtain ⟨tpb0, htpb0, hbudE⟩ := R.calls.budget
  have hbE : E.live (budMsg s.stackRem tpb) := R.env_msg hbud (by simp [budMsg]) (by simp [budMsg, Env.lsp]; omega)
  have htpb : tpb = tpb0 := by
    have := (hbudE _ rfl).mp hbE; simp only [budMsg, Msg.mk.injEq] at this; exact this.2.2.2.2.2.2.2
  subst htpb
  have hgas := R.gas
  have hpro := CFc.prologue
  have hpro' : X.R * (X.ckOf kc).prologue = (X.pfOf kc).prologueGas := by
    unfold Ctx.R; rw [Nat.mul_comm]; exact hpro
  have e1 : X.R * (S + (fee + (X.ckOf kc).prologue)) = X.R * S + X.R * fee + X.R * (X.ckOf kc).prologue := by
    rw [Nat.mul_add, Nat.mul_add, Nat.add_assoc]
  -- the new environment
  let np := (X.pfOf kc).type.params.size
  let base := s.stack.size - np
  have hnpd : np = (X.pfOf kc).type.params.size := rfl
  have hbased : base = s.stack.size - np := rfl
  let bOld := budMsg s.stackRem tpb
  let bNew := budMsg (s.stackRem - (X.pfOf kc).stackCharge) t
  let rc := callMsg t (X.offOf E.k + (pc + 1)) E.sb E.cid (X.pfOf kc).stackCharge t
  let c : Saved := ⟨E.k, E.sb, E.cid, tpl, t⟩
  let E' : Env := ⟨base, t, { f with pc := pc + 1 } :: E.rest,
      fun x => (E.live x ∧ x ≠ bOld) ∨ x ∈ localView (16 + E.cid) f.locals tpl ∨ x = rc ∨ x = bNew, kc⟩
  have hspE : ∀ x, E.live x → 16 ≤ x.space → x.space < 16 + t := by
    intro x hx h16
    rcases hout x hx (Or.inr h16) with h | ⟨-, d2, -, -⟩
    · rcases chainMsgs_space h with h | ⟨c', hc', h⟩
      · omega
      · have := Chain.cids_lt hch c' hc'; omega
    · exact d2
  have hlE : ∀ x, x.space = 2 ∨ x.space = 3 → (E'.live x ↔ E.live x) := by
    intro x hx
    show ((E.live x ∧ x ≠ bOld) ∨ x ∈ localView (16 + E.cid) f.locals tpl ∨ x = rc ∨ x = bNew) ↔ _
    constructor
    · rintro (⟨h, -⟩ | h | rfl | rfl)
      · exact h
      · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc] at hx; omega
      · simp [rc, callMsg] at hx
      · simp [bNew, budMsg] at hx
    · intro h; exact Or.inl ⟨h, fun e => by subst e; simp [bOld, budMsg] at hx⟩
  let lab0 : Label := { target := (X.pfOf kc).code.size, arity := (X.pfOf kc).type.results.size, height := base, isLoop := false }
  let fr : Frame := {
    fn := X.fnOf kc
    pc := 0
    locals := s.stack.extract base s.stack.size ++ (X.pfOf kc).locals.map Val.default
    labels := [lab0]
    base := base }
  refine ⟨E', fr, fun i => if i < s.stack.size - np then tps i else t, fun _ => t, rfl, rfl, rfl, ?_⟩
  have hlen0 : 0 < (X.pfOf kc).code.size := by
    have := CFc.h0; rw [← CFc.hsize]
    rcases h : (X.ckOf kc).heights[0]? with _ | x
    · rw [h] at this; simp at this
    · exact (Array.getElem?_eq_some_iff.mp h).1
  have hbase_le : base ≤ s.stack.size := Nat.sub_le _ _
  have hext0 : (s.stack.extract 0 base).size = base := by simp [Array.size_extract]; omega
  exact {
    frames := rfl
    kLt := hkc
    fn := rfl
    pcEq := rfl
    pcLt := hlen0
    labels := ⟨[rootLabel (X.pfOf kc)], CFc.l0, by
      show [lab0] = shiftLabels base [rootLabel (X.pfOf kc)]
      simp only [shiftLabels, rootLabel, List.map_cons, List.map_nil, Nat.zero_add]; rfl⟩
    base := rfl
    sbLe := by show base ≤ (s.stack.extract 0 base).size; omega
    height := by show (X.ckOf kc).heights[0]? = some ((s.stack.extract 0 base).size - base); rw [CFc.h0, hext0]; simp
    nloc := by
      show (s.stack.extract base s.stack.size ++ (X.pfOf kc).locals.map Val.default).size =
        (X.pfOf kc).type.params.size + (X.pfOf kc).locals.size
      simp only [Array.size_append, Array.size_extract, Array.size_map, Nat.min_self]; omega
    gas := by
      show X.R * (S + (fee + (X.ckOf kc).prologue) - S_seg) +
        (s.gas.g - X.R * fee - (X.pfOf kc).prologueGas) = segb
      have hle : X.R * fee + (X.pfOf kc).prologueGas ≤ s.gas.g := by
        have h1 := R.gas
        have harg : S + (fee + (X.ckOf kc).prologue) - S_seg =
            (S - S_seg) + (fee + (X.ckOf kc).prologue) := by
          have := R.segLt; omega
        have ha : X.R * (S + (fee + (X.ckOf kc).prologue) - S_seg) =
            X.R * (S - S_seg) + X.R * fee + (X.pfOf kc).prologueGas := by
          rw [harg, Nat.mul_add, Nat.mul_add, hpro']; omega
        rw [ha] at hg
        omega
      exact R.gas_call hpro' hle
    segLt := by have := R.segLt; omega
    segbLt := R.segbLt
    numS := by
      intro i hi
      have hi' : i < base := by
        have : (callState X s f E.rest pc fee kc).stack = s.stack.extract 0 base := rfl
        rw [this, hext0] at hi; exact hi
      show isNum ((s.stack.extract 0 base)[i]?.getD default)
      rw [Array.getElem?_extract]
      rw [if_pos (by rw [Nat.min_eq_left hbase_le]; omega), Nat.zero_add]
      exact R.numS i (by omega)
    numL := by
      intro j hj
      show isNum ((s.stack.extract base s.stack.size ++ (X.pfOf kc).locals.map Val.default)[j]?.getD default)
      have hsz : (s.stack.extract base s.stack.size).size = np := by
        simp only [Array.size_extract, Nat.min_self]; omega
      by_cases hjn : j < np
      · rw [Array.getElem?_append_left (by omega), Array.getElem?_extract, if_pos (by rw [Nat.min_self]; omega)]
        exact R.numS (base + j) (by omega)
      · have hj' : j - np < (X.pfOf kc).locals.size := by
          have : j < (s.stack.extract base s.stack.size ++ (X.pfOf kc).locals.map Val.default).size := hj
          simp only [Array.size_append, Array.size_map, hsz] at this; omega
        rw [Array.getElem?_append_right (by omega), hsz, Array.getElem?_map, Array.getElem?_eq_getElem hj']
        simp only [Option.map_some, Option.getD_some]
        exact isNum_default (CFc.locTypes _ (Array.getElem_mem_toList hj'))
    tpsLt := by
      intro i _
      show (if i < s.stack.size - np then tps i else t) < t + 1
      split
      · have := R.tpsLt i (by omega); omega
      · omega
    tplLt := fun _ _ => by show t < t + 1; omega
    envSep := by
      intro x hx
      rcases hx with ⟨h, -⟩ | h | rfl | rfl
      · refine ⟨(R.envSep x h).1, fun e => ?_⟩
        have := hspE x h (by show 16 ≤ x.space; rw [e]; show 16 ≤ 16 + t; omega)
        rw [e] at this; exact absurd this (by show ¬ (16 + t < 16 + t); omega)
      · obtain ⟨j, -, rfl⟩ := mem_localView.mp h
        show 16 + E.cid ≠ 0 ∧ 16 + E.cid ≠ 16 + t
        constructor <;> omega
      · show 4 ≠ 0 ∧ 4 ≠ 16 + t
        constructor <;> omega
      · show 5 ≠ 0 ∧ 5 ≠ 16 + t
        constructor <;> omega
    entry := fun h => absurd h (by show t ≠ 0; omega)
    sbLt := hsbL
    cidLt := htL
    heap := R.heap.congr hlE rfl rfl (by omega)
    calls := by
      refine ⟨by show t < t + 1; omega, ⟨c :: sv, ?_, ?_, ?_, ?_⟩, ⟨t, by omega, ?_⟩⟩
      · show Chain X (t + 1) t base kc ({ f with pc := pc + 1 } :: E.rest) (c :: sv)
        refine ⟨R.kLt, R.fn, R.base, by show E.sb ≤ base; omega, hcidT, by show t < t + 1; omega, hnext, ⟨ls0, hL1, hfl0⟩, ?_, R.nloc,
          fun j hj => ⟨R.numL j hj, by have := R.tplLt j hj; show tpl j < t + 1; omega⟩, R.sbLt, Chain.mono (by omega) hch⟩
        show (X.ckOf E.k).heights[pc + 1]? = some (base - E.sb + (X.pfOf kc).type.results.size)
        rw [hH1]; congr 1; omega
      · intro x hx
        show (E.live x ∧ x ≠ bOld) ∨ x ∈ localView (16 + E.cid) f.locals tpl ∨ x = rc ∨ x = bNew
        rcases hx with h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · refine Or.inl ⟨hin x h, fun e => ?_⟩
          rcases chainMsgs_space h with h4 | ⟨c', -, h16⟩
          · rw [e] at h4; simp [bOld, budMsg] at h4
          · rw [e] at h16; simp [bOld, budMsg] at h16; omega
      · intro x hx hs
        rcases hx with ⟨h, hne⟩ | h | rfl | rfl
        · rcases hout x h hs with h1 | ⟨d1, d2, d3, d4⟩
          · exact Or.inl (Or.inr (Or.inr h1))
          · refine Or.inr ⟨d1, by show x.space < 16 + (t + 1); omega, by show x.space ≠ 16 + t; omega, ?_⟩
            intro c' hc'
            rcases List.mem_cons.mp hc' with rfl | hc'
            · exact d3
            · exact d4 c' hc'
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inl rfl)
        · simp [bNew, budMsg] at hs
      · show s.stackRem - (X.pfOf kc).stackCharge + chainCharge X kc (c :: sv) < 2 ^ 30
        simp only [chainCharge]
        show s.stackRem - (X.pfOf kc).stackCharge + ((X.pfOf kc).stackCharge + chainCharge X E.k sv) < 2 ^ 30
        omega
      · intro x hx
        show ((E.live x ∧ x ≠ bOld) ∨ x ∈ localView (16 + E.cid) f.locals tpl ∨ x = rc ∨ x = bNew) ↔ x = bNew
        constructor
        · rintro (⟨h, hne⟩ | h | rfl | rfl)
          · exact absurd ((hbudE x hx).mp h) hne
          · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc] at hx; omega
          · simp [rc, callMsg] at hx
          · rfl
        · intro h; exact Or.inr (Or.inr (Or.inr h))
    live := by
      intro x
      have hkeep : ∀ i, i < s.stack.size - np → (s.stack.extract 0 base)[i]? = s.stack[i]? := by
        intro i hi
        rw [Array.getElem?_extract, if_pos (by rw [Nat.min_eq_left hbase_le]; omega), Nat.zero_add]
      have vu := view_update (sp := 16 + E.cid) (by omega) none (k := np) (stk := s.stack)
        (stk' := s.stack.extract 0 base) (locs := f.locals) (locs' := f.locals) (tps := tps) (tpl := tpl) (t := t)
        (by omega) hkeep (by rw [hext0]; omega) rfl (fun _ _ => rfl) (fun j h => by simp at h) R.tpsLt R.tplLt x
      have htpl : (fun j => if some j = (none : Option Nat) then t else tpl j) = tpl := funext fun j => by simp
      rw [htpl, hext0, show base - (s.stack.size - np) = 0 by omega] at vu
      simp only [List.range_zero, List.map_nil, Option.toList_none, List.append_nil, List.not_mem_nil, or_false]
        at vu
      show (live x ∧ x ∉ _) ∨ x ∈ _ ↔ x ∈ stackView (s.stack.extract 0 base) _ ∨
        x ∈ localView (16 + t) (s.stack.extract base s.stack.size ++ (X.pfOf kc).locals.map Val.default) _ ∨
        ((E.live x ∧ x ≠ bOld) ∨ x ∈ localView (16 + E.cid) f.locals tpl ∨ x = rc ∨ x = bNew)
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, not_or]
      constructor
      · rintro (⟨hl, hnp, hnb⟩ | hL | rfl | rfl)
        · rcases (R.live x).mp hl with hs | hlc | he
          · rcases vu.mpr ⟨Or.inl hs, hnp⟩ with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hlc)))
          · exact Or.inr (Or.inr (Or.inl ⟨he, hnb⟩))
        · exact Or.inr (Or.inl hL)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · rintro (hs | hL | ⟨he, hne⟩ | hlc | rfl | rfl)
        · obtain ⟨hold, hnp⟩ := vu.mp (Or.inl hs)
          refine Or.inl ⟨?_, hnp, fun e => ?_⟩
          · rcases hold with h | h
            · exact (R.live x).mpr (Or.inl h)
            · exact (R.live x).mpr (Or.inr (Or.inl h))
          · obtain ⟨i, -, he⟩ := mem_stackView.mp hs
            rw [e] at he; have := congrArg Msg.space he; simp [bOld, budMsg, enc] at this
        · exact Or.inr (Or.inl hL)
        · refine Or.inl ⟨(R.live x).mpr (Or.inr (Or.inr he)), fun hp => ?_, hne⟩
          obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp; exact (R.envSep _ he).1 rfl
        · refine Or.inl ⟨(R.live x).mpr (Or.inr (Or.inl hlc)), fun hp => ?_, fun e => ?_⟩
          · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp
            obtain ⟨j, -, he⟩ := mem_localView.mp hlc; have := congrArg Msg.space he; simp [enc] at this; omega
          · obtain ⟨j, -, he⟩ := mem_localView.mp hlc
            rw [e] at he; have := congrArg Msg.space he; simp [bOld, budMsg, enc] at this; omega
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl)) }

end WasmBase

namespace WasmBase
variable {S_seg segb : Nat}
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 1600000 in
/-- **The relation after a return from a callee** (`cid ≠ 0`): the frame is popped, the top `kp`
operand-stack entries were consumed (the `br_if` condition, or nothing), the rest of the stack is
the caller's stack plus the results (D3), the call record `m` and the budget register are consumed
and the budget is restored.  The relation moves to the caller (the chain head), and the callee's
locals become dead. -/
theorem return_rel (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) (fee kp : Nat) (hg : X.R * (S + fee - S_seg) ≤ segb)
    (hcid : E.cid ≠ 0) (hkp : kp ≤ s.stack.size - E.sb)
    (har : s.stack.size - kp = E.sb + (X.pfOf E.k).type.results.size)
    {m : Msg} (hm : live m) (hms : m.space = 4) (hmsl : m.slot = E.cid)
    {tpb : Nat} (hmb : live (budMsg s.stackRem tpb))
    (s' : St) (hs'stk : s'.stack = s.stack.extract 0 (s.stack.size - kp)) (hs'fr : s'.frames = E.rest)
    (hs'g : s'.gas.g = s.gas.g - X.R * fee) (hs'pg : s'.pages = s.pages) (hs'gl : s'.globals = s.globals)
    (hs'rem : s'.stackRem = s.stackRem + (X.pfOf E.k).stackCharge) :
    ∃ (fc : Frame) (rest' : List Frame) (c : Saved), E.rest = fc :: rest' ∧
      m = callMsg E.cid (X.offOf c.k + fc.pc) c.sb c.cid (X.pfOf E.k).stackCharge c.tpc ∧
      Rel X s' (t + 1) c.k fc.pc (S + fee) c.sb c.cid (stepLive live
          ((List.range kp).map (fun d => enc 0 (s.stack.size - kp + d)
              (s.stack[s.stack.size - kp + d]?.getD default) (tps (s.stack.size - kp + d))) ++
            [m, budMsg s.stackRem tpb])
          [budMsg (s.stackRem + (X.pfOf E.k).stackCharge) t]) S_seg segb := by
  obtain ⟨sv, hch, hin, hout, hrl⟩ := R.calls.chain
  obtain ⟨tpb0, htpb0, hbudE⟩ := R.calls.budget
  have hcidT := R.calls.cidLtT
  have hbE : E.live (budMsg s.stackRem tpb) := R.env_msg hmb (by simp [budMsg]) (by simp [budMsg, Env.lsp]; omega)
  have htpb : tpb = tpb0 := by
    have := (hbudE _ rfl).mp hbE; simp only [budMsg, Msg.mk.injEq] at this; exact this.2.2.2.2.2.2.2
  subst htpb
  have hmE : E.live m := R.env_msg hm (by omega) (by simp [Env.lsp]; omega)
  -- the chain is non-empty
  obtain ⟨fc, rest', hrest⟩ : ∃ fc rest', E.rest = fc :: rest' := by
    cases h : E.rest with
    | nil =>
      rw [h] at hch
      cases sv with
      | nil => exact absurd hch.1 hcid
      | cons _ _ => exact hch.elim
    | cons fc rest' => exact ⟨fc, rest', rfl⟩
  rw [hrest] at hch hin hout
  obtain ⟨c, sv', rfl⟩ : ∃ c sv', sv = c :: sv' := by
    cases sv with
    | nil => exact hch.elim
    | cons c sv' => exact ⟨c, sv', rfl⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, ⟨lsc, hLc, hflc⟩, c9, c10, c11, c12, c13⟩ := hch
  -- the record
  have hmrec : m = callMsg E.cid (X.offOf c.k + fc.pc) c.sb c.cid (X.pfOf E.k).stackCharge c.tpc := by
    rcases hout m hmE (Or.inl hms) with h | ⟨d1, -, -, -⟩
    · rcases h with h | h | h
      · exact h
      · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc] at hms; omega
      · have := chainMsgs_rec_slot c13 h hms; omega
    · omega
  refine ⟨fc, rest', c, hrest, hmrec, ?_⟩
  subst hmrec
  have hcids := Chain.cids_lt c13
  let mrec := callMsg E.cid (X.offOf c.k + fc.pc) c.sb c.cid (X.pfOf E.k).stackCharge c.tpc
  let bOld := budMsg s.stackRem tpb
  let bNew := budMsg (s.stackRem + (X.pfOf E.k).stackCharge) t
  let E' : Env := ⟨c.sb, c.cid, rest',
      fun x => (E.live x ∧ x ≠ mrec ∧ x ≠ bOld ∧ x ∉ localView (16 + c.cid) fc.locals c.tpl) ∨
        x ∈ localView (16 + E.cid) f.locals tpl ∨ x = bNew, c.k⟩
  have hgas := R.gas
  have hsbR := R.sbLe
  refine ⟨E', fc, fun i => if i < s.stack.size - kp then tps i else t, c.tpl, rfl, rfl, rfl, ?_⟩
  have hext : (s.stack.extract 0 (s.stack.size - kp)).size = s.stack.size - kp := by
    simp [Array.size_extract]
  -- messages of the outer live set in the caller's locals space are its locals
  have hcl : ∀ x, E.live x → x.space = 16 + c.cid → x ∈ localView (16 + c.cid) fc.locals c.tpl := by
    intro x hx hs
    rcases hout x hx (Or.inr (by omega)) with h | ⟨-, -, -, d4⟩
    · rcases h with rfl | h | h
      · simp [callMsg] at hs; omega
      · exact h
      · rcases chainMsgs_space h with h4 | ⟨c', hc', h16⟩
        · omega
        · have := hcids c' hc'; omega
    · exact absurd hs (d4 c List.mem_cons_self)
  have hlE : ∀ x, x.space = 2 ∨ x.space = 3 → (E'.live x ↔ E.live x) := by
    intro x hx
    show ((E.live x ∧ x ≠ mrec ∧ x ≠ bOld ∧ x ∉ localView (16 + c.cid) fc.locals c.tpl) ∨
        x ∈ localView (16 + E.cid) f.locals tpl ∨ x = bNew) ↔ _
    constructor
    · rintro (⟨h, -⟩ | h | rfl)
      · exact h
      · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc] at hx; omega
      · simp [bNew, budMsg] at hx
    · intro h
      refine Or.inl ⟨h, fun e => ?_, fun e => ?_, fun hl => ?_⟩
      · rw [e] at hx; simp [mrec, callMsg] at hx
      · rw [e] at hx; simp [bOld, budMsg] at hx
      · obtain ⟨j, -, rfl⟩ := mem_localView.mp hl; simp [enc] at hx; omega
  exact {
    frames := hs'fr.trans hrest
    kLt := c1
    fn := c2
    pcEq := rfl
    pcLt := c7
    labels := ⟨lsc, hLc, hflc⟩
    base := c3
    sbLe := by show c.sb ≤ s'.stack.size; rw [hs'stk, hext]; omega
    height := by
      show (X.ckOf c.k).heights[fc.pc]? = some (s'.stack.size - c.sb)
      rw [hs'stk, hext, c9]; congr 1; omega
    nloc := c10
    gas := R.step_gas hg hs'g
    segLt := by have := R.segLt; omega
    segbLt := R.segbLt
    numS := by
      intro i hi
      rw [hs'stk, hext] at hi
      rw [hs'stk, Array.getElem?_extract, if_pos (by rw [Nat.min_eq_left (Nat.sub_le _ _)]; omega), Nat.zero_add]
      exact R.numS i (by omega)
    numL := fun j hj => (c11 j hj).1
    tpsLt := by
      intro i _
      show (if i < s.stack.size - kp then tps i else t) < t + 1
      split
      · have := R.tpsLt i (by omega); omega
      · omega
    tplLt := fun j hj => by have := (c11 j hj).2; omega
    envSep := by
      intro x hx
      rcases hx with ⟨h, -, -, hnl⟩ | h | rfl
      · refine ⟨(R.envSep x h).1, fun e => hnl (hcl x h e)⟩
      · obtain ⟨j, -, rfl⟩ := mem_localView.mp h
        show 16 + E.cid ≠ 0 ∧ 16 + E.cid ≠ 16 + c.cid
        constructor <;> omega
      · show 5 ≠ 0 ∧ 5 ≠ 16 + c.cid
        constructor <;> omega
    entry := by
      intro h0
      show rest' = [] ∧ c.sb = 0
      cases rest' with
      | nil => cases sv' with
        | nil => exact ⟨rfl, c13.2⟩
        | cons _ _ => exact c13.elim
      | cons fc' rest'' => cases sv' with
        | nil => exact c13.elim
        | cons c' sv'' => exfalso; have := c13.2.2.2.2.1; have h0' : c.cid = 0 := h0; rw [h0'] at this; omega
    sbLt := c12
    cidLt := by show c.cid < 2 ^ 28; have := R.cidLt; omega
    heap := R.heap.congr hlE hs'pg hs'gl (by omega)
    calls := by
      refine ⟨by show c.cid < t + 1; omega, ⟨sv', Chain.mono (by omega) c13, ?_, ?_, ?_⟩, ⟨t, by omega, ?_⟩⟩
      · intro x hx
        show (E.live x ∧ x ≠ mrec ∧ x ≠ bOld ∧ x ∉ localView (16 + c.cid) fc.locals c.tpl) ∨
          x ∈ localView (16 + E.cid) f.locals tpl ∨ x = bNew
        refine Or.inl ⟨hin x (Or.inr (Or.inr hx)), fun e => ?_, fun e => ?_, fun hl => ?_⟩
        · have := chainMsgs_rec_slot c13 hx (by rw [e]; rfl); rw [e] at this; simp [mrec, callMsg] at this; omega
        · rcases chainMsgs_space hx with h4 | ⟨c', -, h16⟩
          · rw [e] at h4; simp [bOld, budMsg] at h4
          · rw [e] at h16; simp [bOld, budMsg] at h16; omega
        · obtain ⟨j, -, rfl⟩ := mem_localView.mp hl
          rcases chainMsgs_space hx with h4 | ⟨c', hc', h16⟩
          · simp [enc] at h4; omega
          · simp [enc] at h16; have := Chain.cids_lt c13 c' hc'; omega
      · intro x hx hs
        rcases hx with ⟨h, hne, -, hnl⟩ | h | rfl
        · rcases hout x h hs with h1 | ⟨d1, d2, d3, d4⟩
          · rcases h1 with rfl | h1 | h1
            · exact absurd rfl hne
            · exact absurd h1 hnl
            · exact Or.inl h1
          · refine Or.inr ⟨d1, by show x.space < 16 + (t + 1); omega, d4 c List.mem_cons_self,
              fun c' hc' => d4 c' (List.mem_cons_of_mem _ hc')⟩
        · obtain ⟨j, -, rfl⟩ := mem_localView.mp h
          refine Or.inr ⟨by show 16 ≤ 16 + E.cid; omega, by show 16 + E.cid < 16 + (t + 1); omega,
            by show 16 + E.cid ≠ 16 + c.cid; omega, fun c' hc' => ?_⟩
          have := Chain.cids_lt c13 c' hc'; show 16 + E.cid ≠ 16 + c'.cid; omega
        · simp [bNew, budMsg] at hs
      · rw [hs'rem]
        show s.stackRem + (X.pfOf E.k).stackCharge + chainCharge X c.k sv' < 2 ^ 30
        simp only [chainCharge] at hrl; omega
      · intro x hx
        rw [hs'rem]
        show ((E.live x ∧ x ≠ mrec ∧ x ≠ bOld ∧ x ∉ localView (16 + c.cid) fc.locals c.tpl) ∨
          x ∈ localView (16 + E.cid) f.locals tpl ∨ x = bNew) ↔ x = bNew
        constructor
        · rintro (⟨h, -, hne, -⟩ | h | rfl)
          · exact absurd ((hbudE x hx).mp h) hne
          · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc] at hx; omega
          · rfl
        · intro h; exact Or.inr (Or.inr h)
    live := by
      intro x
      have hkeep : ∀ i, i < s.stack.size - kp → (s.stack.extract 0 (s.stack.size - kp))[i]? = s.stack[i]? := by
        intro i hi
        rw [Array.getElem?_extract, if_pos (by rw [Nat.min_eq_left (Nat.sub_le _ _)]; omega), Nat.zero_add]
      have vu := view_update (sp := 16 + E.cid) (by omega) none (k := kp) (stk := s.stack)
        (stk' := s.stack.extract 0 (s.stack.size - kp)) (locs := f.locals) (locs' := f.locals) (tps := tps)
        (tpl := tpl) (t := t) (by omega) hkeep (by rw [hext]; exact Nat.le_refl _) rfl (fun _ _ => rfl) (fun j h => by simp at h)
        R.tpsLt R.tplLt x
      have htpl : (fun j => if some j = (none : Option Nat) then t else tpl j) = tpl := funext fun j => by simp
      rw [htpl, hext, Nat.sub_self] at vu
      simp only [List.range_zero, List.map_nil, Option.toList_none, List.append_nil, List.not_mem_nil, or_false]
        at vu
      rw [hs'stk]
      show (live x ∧ x ∉ _) ∨ x ∈ _ ↔ x ∈ stackView (s.stack.extract 0 (s.stack.size - kp)) _ ∨
        x ∈ localView (16 + c.cid) fc.locals c.tpl ∨
        ((E.live x ∧ x ≠ mrec ∧ x ≠ bOld ∧ x ∉ localView (16 + c.cid) fc.locals c.tpl) ∨
          x ∈ localView (16 + E.cid) f.locals tpl ∨ x = bNew)
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.mem_singleton]
      constructor
      · rintro (⟨hl, hnp, hnr, hnb⟩ | rfl)
        · rcases (R.live x).mp hl with hs | hlc | he
          · rcases vu.mpr ⟨Or.inl hs, hnp⟩ with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hlc)))
          · by_cases hl' : x ∈ localView (16 + c.cid) fc.locals c.tpl
            · exact Or.inr (Or.inl hl')
            · exact Or.inr (Or.inr (Or.inl ⟨he, hnr, hnb, hl'⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · rintro (hs | hlc | ⟨he, hnr, hnb, -⟩ | hlc | rfl)
        · obtain ⟨hold, hnp⟩ := vu.mp (Or.inl hs)
          refine Or.inl ⟨?_, hnp, fun e => ?_, fun e => ?_⟩
          · rcases hold with h | h
            · exact (R.live x).mpr (Or.inl h)
            · exact (R.live x).mpr (Or.inr (Or.inl h))
          · obtain ⟨i, -, he⟩ := mem_stackView.mp hs
            rw [e] at he; have := congrArg Msg.space he; simp [mrec, callMsg, enc] at this
          · obtain ⟨i, -, he⟩ := mem_stackView.mp hs
            rw [e] at he; have := congrArg Msg.space he; simp [bOld, budMsg, enc] at this
        · have hE := hin x (Or.inr (Or.inl hlc))
          refine Or.inl ⟨(R.live x).mpr (Or.inr (Or.inr hE)), fun hp => ?_, fun e => ?_, fun e => ?_⟩
          · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp; exact (R.envSep _ hE).1 rfl
          · obtain ⟨j, -, he⟩ := mem_localView.mp hlc
            rw [e] at he; have := congrArg Msg.space he; simp [mrec, callMsg, enc] at this; omega
          · obtain ⟨j, -, he⟩ := mem_localView.mp hlc
            rw [e] at he; have := congrArg Msg.space he; simp [bOld, budMsg, enc] at this; omega
        · refine Or.inl ⟨(R.live x).mpr (Or.inr (Or.inr he)), fun hp => ?_, hnr, hnb⟩
          obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp; exact (R.envSep _ he).1 rfl
        · refine Or.inl ⟨(R.live x).mpr (Or.inr (Or.inl hlc)), fun hp => ?_, fun e => ?_, fun e => ?_⟩
          · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hp
            obtain ⟨j, -, he⟩ := mem_localView.mp hlc; have := congrArg Msg.space he; simp [enc] at this; omega
          · obtain ⟨j, -, he⟩ := mem_localView.mp hlc
            rw [e] at he; have := congrArg Msg.space he; simp [mrec, callMsg, enc] at this; omega
          · obtain ⟨j, -, he⟩ := mem_localView.mp hlc
            rw [e] at he; have := congrArg Msg.space he; simp [bOld, budMsg, enc] at this; omega
        · exact Or.inr rfl }

end WasmBase

namespace WasmBase
variable {S_seg segb : Nat}
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-- `doReturn` from a callee under no-discard: the stack is unchanged, the frame popped, the
budget restored, and the run continues in the caller. -/
theorem doReturn_cons (X : Ctx) {k : Nat} (hkn : k < X.nf) (s : St) (f fc : Frame) (rest : List Frame)
    (hfr : s.frames = f :: fc :: rest) (hfn : f.fn = X.fnOf k) (b : Nat) (hb : f.base = b)
    (har : s.stack.size = b + (X.pfOf k).type.results.size) :
    doReturn X.p s = .cont { s with frames := fc :: rest, stackRem := s.stackRem + (X.pfOf k).stackCharge } := by
  unfold doReturn
  rw [hfr]
  simp only
  rw [hfn, (X.factsOf hkn).func]
  simp only [hb, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  rw [stack_nodiscard s.stack b (X.pfOf k).type.results.size (by omega)]

/-- **Return from a callee** (`end` of the body, `return`, `br` to the function label at
activation `cid ≠ 0`). -/
theorem step_return (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {ins : Instr} {fee : Nat}
    (hins : (X.pfOf E.k).code[pc]? = some ins)
    (hkind : (ins = .end_ ∧ f.labels.length = 1) ∨ ins = .ret ∨ (∃ l, ins = .br l ∧ l + 1 ≥ f.labels.length))
    (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64) (hcid : E.cid ≠ 0)
    {m : Msg} (hm : live m) (hms : m.space = 4) (hmsl : m.slot = E.cid)
    {tpb : Nat} (hmb : live (budMsg s.stackRem tpb)) :
    ∃ (fc : Frame) (rest' : List Frame) (c : Saved), E.rest = fc :: rest' ∧
      m = callMsg E.cid (X.offOf c.k + fc.pc) c.sb c.cid (X.pfOf E.k).stackCharge c.tpc ∧
      ∃ s', step X.cfg X.p s = .cont s' ∧
        Rel X s' (t + 1) c.k fc.pc (S + fee) c.sb c.cid (stepLive live [m, budMsg s.stackRem tpb] [budMsg (s.stackRem + (X.pfOf E.k).stackCharge) t]) S_seg segb := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt _ hins
    (by rcases hkind with ⟨rfl, _⟩ | rfl | ⟨_, rfl, _⟩ <;> rfl)
  obtain ⟨ls0, hL0, hfl⟩ := R.labels
  have hH := R.height
  have hlen : f.labels.length = ls0.length := by rw [hfl, shiftLabels_length]
  have har : s.stack.size - E.sb = (X.pfOf E.k).type.results.size := by
    unfold verifyAt at hv
    rw [hins, hL0, hH] at hv
    rcases hkind with ⟨rfl, h1⟩ | rfl | ⟨l, rfl, hl⟩
    · rw [hlen] at h1
      obtain ⟨lab0, hls⟩ := List.length_eq_one_iff.mp h1
      simp only [hls, decide_eq_true_eq] at hv; exact hv
    · simpa using hv
    · rw [hlen] at hl
      simp only [hl, ite_true, decide_eq_true_eq] at hv; exact hv
  have hsbR := R.sbLe
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee } }
  let s' : St := { s1 with frames := E.rest, stackRem := s1.stackRem + (X.pfOf E.k).stackCharge }
  obtain ⟨fc, rest', c, hrest, hmrec, hrel⟩ := return_rel X R fee 0 hg hcid (Nat.zero_le _) (by omega) hm hms hmsl hmb
    { s' with stack := s.stack.extract 0 (s.stack.size - 0) } rfl rfl rfl rfl rfl rfl
  have hst : ({ s' with stack := s.stack.extract 0 (s.stack.size - 0) } : St) =
      { s1 with frames := fc :: rest', stackRem := s1.stackRem + (X.pfOf E.k).stackCharge } := by
    simp only [s', s1, Nat.sub_zero, Array.extract_size, hrest]
  rw [hst] at hrel
  refine ⟨fc, rest', c, hrest, hmrec, _, ?_, hrel⟩
  have hfr : s1.frames = f :: fc :: rest' := by show s.frames = _; rw [R.frames, hrest]
  have hd := doReturn_cons X R.kLt s1 f fc rest' hfr R.fn E.sb R.base (by show s.stack.size = _; omega)
  rw [step_eq_exec X R hins hfee hg hg64]
  rcases hkind with ⟨rfl, h1⟩ | rfl | ⟨l, rfl, hl⟩
  · obtain ⟨lab0, hls⟩ := List.length_eq_one_iff.mp h1
    simp only [exec, hls]; exact hd
  · simp only [exec]; exact hd
  · simp only [exec]; unfold doBr; rw [if_pos hl]; exact hd

end WasmBase

namespace WasmBase
variable {S_seg segb : Nat}
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

theorem pop_eq_extract (a : Array Val) : a.pop = a.extract 0 (a.size - 1) := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [Array.getElem_pop, Array.getElem_extract]

/-- **`br_if` to the function label at activation `cid ≠ 0`**: taken, it returns to the caller;
not taken, it continues at `pc + 1`. -/
theorem step_returnIf (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) {l fee : Nat}
    (hl : l + 1 ≥ f.labels.length)
    (hins : (X.pfOf E.k).code[pc]? = some (.brIf l)) (hfee : feeUnits X.cfg (X.pfOf E.k).gas[pc]? = some fee)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hg64 : X.g0 < 2 ^ 64) (hcid : E.cid ≠ 0)
    (mc : Msg) (hmc : live mc) (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1) :
    (mc.val ≠ 0 → ∀ {m : Msg}, live m → m.space = 4 → m.slot = E.cid → ∀ {tpb : Nat}, live (budMsg s.stackRem tpb) →
      ∃ (fc : Frame) (rest' : List Frame) (c : Saved), E.rest = fc :: rest' ∧
        m = callMsg E.cid (X.offOf c.k + fc.pc) c.sb c.cid (X.pfOf E.k).stackCharge c.tpc ∧
        ∃ s', step X.cfg X.p s = .cont s' ∧
          Rel X s' (t + 1) c.k fc.pc (S + fee) c.sb c.cid (stepLive live [mc, m, budMsg s.stackRem tpb] [budMsg (s.stackRem + (X.pfOf E.k).stackCharge) t]) S_seg segb) ∧
    (mc.val = 0 → ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) E.k (pc + 1) (S + fee) E.sb E.cid (stepLive live [mc] []) S_seg segb) := by
  have hv := (X.factsOf R.kLt).verify pc R.pcLt _ hins (by m2_ns)
  obtain ⟨ls0, hL0, hfl⟩ := R.labels
  have hH := R.height
  have hsbR := R.sbLe
  have hlen : f.labels.length = ls0.length := by rw [hfl, shiftLabels_length]
  unfold verifyAt at hv
  rw [hins, hL0, hH] at hv
  rw [hlen] at hl
  simp only [hl, ite_true, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨h1, ⟨hnext, hL1⟩, hH1⟩, har⟩ := hv
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  have hb' : vNum (s.stack.back?.getD (.i32 0)) = mc.val := by rw [back_getD _ (by omega), vc]
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee } }
  let s2 : St := { s1 with stack := s1.stack.pop }
  constructor
  · intro h0 m hm hms hmsl tpb hmb
    let s' : St := { s2 with frames := E.rest, stackRem := s2.stackRem + (X.pfOf E.k).stackCharge }
    obtain ⟨fc, rest', c, hrest, hmrec, hrel⟩ := return_rel X R fee 1 hg hcid (by omega) (by omega) hm hms hmsl hmb
      { s' with stack := s.stack.extract 0 (s.stack.size - 1) } rfl rfl rfl rfl rfl rfl
    have hst : ({ s' with stack := s.stack.extract 0 (s.stack.size - 1) } : St) =
        { s2 with frames := fc :: rest', stackRem := s2.stackRem + (X.pfOf E.k).stackCharge } := by
      simp only [s', s2, s1, ← pop_eq_extract, hrest]
    rw [hst] at hrel
    refine ⟨fc, rest', c, hrest, hmrec, { s2 with frames := fc :: rest', stackRem := s2.stackRem + (X.pfOf E.k).stackCharge },
      ?_, ?_⟩
    · have hfr : s2.frames = f :: fc :: rest' := by show s.frames = _; rw [R.frames, hrest]
      have hd := doReturn_cons X R.kLt s2 f fc rest' hfr R.fn E.sb R.base
        (by show s.stack.pop.size = _; simp; omega)
      rw [step_eq_exec X R hins hfee hg hg64]
      simp only [exec, popN_eq, hb', ne_eq, h0, not_false_eq_true, ite_true]
      unfold doBr; rw [if_pos (by rw [hlen]; exact hl)]; exact hd
    · have e : stepLive live (((List.range 1).map fun d => enc 0 (s.stack.size - 1 + d)
            (s.stack[s.stack.size - 1 + d]?.getD default) (tps (s.stack.size - 1 + d))) ++ [m, budMsg s.stackRem tpb])
          [budMsg (s.stackRem + (X.pfOf E.k).stackCharge) t] =
          stepLive live [mc, m, budMsg s.stackRem tpb] [budMsg (s.stackRem + (X.pfOf E.k).stackCharge) t] := by
        apply stepLive_congr _ (fun _ => Iff.rfl)
        intro x
        simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.cons_append, List.nil_append]
        rw [← ec]
      rw [e] at hrel; exact hrel
  · intro h0
    refine ⟨{ s1 with
      stack := popK s.stack 1
      frames := { f with pc := pc + 1, labels := shiftLabels E.sb ls0 } :: E.rest }, ?_, ?_⟩
    · rw [step_eq_exec X R hins hfee hg hg64]
      simp only [exec, popN_eq, hb', h0, ne_eq, not_true_eq_false, ite_false, setFrame, R.frames, R.pcEq,
        popK, s1]
      rw [← hfl]
    · have CR := ctrl_rel X R (k := 1) (fee := fee) (by omega) (pc + 1) ls0 hnext hL1 (by omega)
        (by rw [hH1]; congr 1; omega) hg
        { s1 with
          stack := popK s.stack 1
          frames := { f with pc := pc + 1, labels := shiftLabels E.sb ls0 } :: E.rest } rfl rfl rfl rfl rfl rfl
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

namespace WasmBase
variable {S_seg segb : Nat}
open NearSpecV3.Wasm

/-- A live call record of the current activation is the chain head's record. -/
theorem RelW.call_rec {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live S_seg segb) (hcid : E.cid ≠ 0)
    {m : Msg} (hm : live m) (hms : m.space = 4) (hmsl : m.slot = E.cid) :
    ∃ (fc : Frame) (rest' : List Frame) (c : Saved), E.rest = fc :: rest' ∧
      m = callMsg E.cid (X.offOf c.k + fc.pc) c.sb c.cid (X.pfOf E.k).stackCharge c.tpc := by
  obtain ⟨sv, hch, hin, hout, hrl⟩ := R.calls.chain
  have hmE : E.live m := R.env_msg hm (by omega) (by simp [Env.lsp]; omega)
  obtain ⟨fc, rest', hrest⟩ : ∃ fc rest', E.rest = fc :: rest' := by
    cases h : E.rest with
    | nil =>
      rw [h] at hch
      cases sv with
      | nil => exact absurd hch.1 hcid
      | cons _ _ => exact hch.elim
    | cons fc rest' => exact ⟨fc, rest', rfl⟩
  rw [hrest] at hch hout
  obtain ⟨c, sv', rfl⟩ : ∃ c sv', sv = c :: sv' := by
    cases sv with
    | nil => exact hch.elim
    | cons c sv' => exact ⟨c, sv', rfl⟩
  obtain ⟨-, -, -, -, c5, -, -, -, -, -, -, -, c13⟩ := hch
  refine ⟨fc, rest', c, hrest, ?_⟩
  rcases hout m hmE (Or.inl hms) with h | ⟨d1, -, -, -⟩
  · rcases h with h | h | h
    · exact h
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc] at hms; omega
    · have := chainMsgs_rec_slot c13 h hms; omega
  · omega

end WasmBase
