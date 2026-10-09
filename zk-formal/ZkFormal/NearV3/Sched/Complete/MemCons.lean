import ZkFormal.NearV3.Sched.Complete.MemRows

/-!
# ZkFormal.NearV3.Sched.Complete.MemCons — the `smmV3` constraints on value records (M4)

`mem_row_ok`: every constraint of `smmV3` vanishes (as an integer) on a row pair `(X, Y)` with
* `RowOk X`: boolean flags, one-hot kind, and the INIT / READ / GRANT relations in naturals;
* `X → Y`: a continuing row (`act ∧ ¬lst`) is followed by the next op of its segment (carried
  `addr, v → vin, t → tp, w → wp, al, isL`), a last row by an INIT or padding, padding by
  padding (except across the wrap, where `isLast = 1` and `X` is padding);
* the first row is INIT or padding.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched

/-- One-row facts of a memory row. -/
structure RowOk (X : MV) : Prop where
  bact : X.act ≤ 1
  bfst : X.fst ≤ 1
  blst : X.lst ≤ 1
  brd : X.isRd ≤ 1
  bgr : X.isGr ≤ 1
  bal : X.al ≤ 1
  bisL : X.isL ≤ 1
  bok : X.ok ≤ 1
  bcc : X.cc ≤ 1
  bsf : X.sf ≤ 1
  kind : X.act = X.fst + X.isRd + X.isGr
  lstAct : X.lst ≤ X.act
  init : X.fst = 1 → X.t = 0 ∧ X.vin = X.al ∧ X.inc = X.w ∧ X.ok = 0 ∧ X.cc = X.isL ∧ X.sf = 0 ∧
    X.wp = X.w
  rd : X.isRd = 1 → X.v = X.vin ∧ X.w = X.wp ∧ X.inc = 0 ∧ X.ok = 0 ∧ X.cc = 0 ∧ X.sf = 0
  gr : X.isGr = 1 → X.cc = (if X.isL = 1 then X.al else X.sf) ∧
    X.v = (if X.ok = 1 then (if X.sf = 1 then X.vin - X.inc else 0) else X.vin) ∧
    (X.sf = 1 → X.inc ≤ X.vin) ∧ (X.ok = 1 → X.cc = 1) ∧
    X.w = X.wp + (if X.isL = 1 ∧ X.ok = 1 then X.inc else 0)

theorem padV_ok : RowOk padV := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [padV]

/-- Continuation from `X` to `Y` inside a segment. -/
def Cont (X Y : MV) : Prop :=
  Y.act = 1 ∧ Y.fst = 0 ∧ Y.addr = X.addr ∧ Y.vin = X.v ∧ Y.tp = X.t ∧ Y.wp = X.w ∧ Y.al = X.al ∧
    Y.isL = X.isL

section gates

theorem gate {a : Nat} {x : Int} (ha : a ≤ 1) (h : a = 1 → x = 0) : (a : Int) * x = 0 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · simp
  · simp [h rfl]

theorem gate2 {a b : Nat} {x : Int} (ha : a ≤ 1) (hb : b ≤ 1) (h : a = 1 → b = 1 → x = 0) :
    (a : Int) * b * x = 0 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · simp
  · rw [show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul]; exact gate hb (h rfl)

theorem gateE {a l : Nat} {x : Int} (ha : a ≤ 1) (hl : l ≤ a) (h : a = 1 → l = 0 → x = 0) :
    ((a : Int) - l) * x = 0 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · rw [show l = 0 by omega]; simp
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [h rfl rfl]
    · simp

end gates

@[simp] theorem zev_isLast' (Z : ZEnv) : zev Z .isLast = Z.last := rfl
@[simp] theorem zev_isTransition' (Z : ZEnv) : zev Z .isTransition = 1 - Z.last := rfl

/-- **The memory constraints on a legal row pair.** -/
theorem mem_row_ok {Z : ZEnv} {X Y : MV} (hX : ∀ c, Z.cur c = X.cell c) (hY : ∀ c, Z.nxt c = Y.cell c)
    (hx : RowOk X) (hyb : Y.act ≤ 1)
    (hcont : X.act = 1 → X.lst = 0 → Cont X Y) (hafter : X.lst = 1 → Y.act = 1 → Y.fst = 1)
    (hfirst : Z.first = 0 ∨ (Z.first = 1 ∧ X.act = X.fst))
    (hlast : (Z.last = 0 ∧ (X.act = 0 → Y.act = 0)) ∨ (Z.last = 1 ∧ X.act = 0)) :
    ∀ e ∈ Mem.constraints, zev Z e = 0 := by
  intro e he
  simp only [Mem.constraints, Mem.carried, Mem.boolCols, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
  have hc := fun c => hX c
  have hn := fun c => hY c
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp only [ZkFormal.Chacha.Table.boolC, Mem.gE, Mem.notE, Mem.mul3, zev_mul, zev_sub,
    zev_add, zev_c, zev_n, zev_k, zev_isFirst, zev_isLast', zev_isTransition', hc, hn, MV.cell,
    Mem.act, Mem.fst, Mem.lst, Mem.isRd, Mem.isGr, Mem.addr, Mem.t, Mem.tp, Mem.vin, Mem.v, Mem.wp,
    Mem.w, Mem.al, Mem.isL, Mem.inc, Mem.ok, Mem.cc, Mem.sf]
  all_goals simp only [↓reduceIte, Nat.reduceEqDiff]
  -- booleanity (10)
  · exact gate hx.bact (fun h => by rw [h]; rfl)
  · exact gate hx.bfst (fun h => by rw [h]; rfl)
  · exact gate hx.blst (fun h => by rw [h]; rfl)
  · exact gate hx.brd (fun h => by rw [h]; rfl)
  · exact gate hx.bgr (fun h => by rw [h]; rfl)
  · exact gate hx.bal (fun h => by rw [h]; rfl)
  · exact gate hx.bisL (fun h => by rw [h]; rfl)
  · exact gate hx.bok (fun h => by rw [h]; rfl)
  · exact gate hx.bcc (fun h => by rw [h]; rfl)
  · exact gate hx.bsf (fun h => by rw [h]; rfl)
  -- kind
  · have := hx.kind; omega
  -- lst · (1 − act)
  · exact gate hx.blst (fun h => by have := hx.lstAct; have := hx.bact; rw [show X.act = 1 by omega]; rfl)
  -- isLast · act
  · rcases hlast with ⟨h0, -⟩ | ⟨h1, h2⟩
    · rw [h0]; simp
    · rw [h2]; simp
  -- isFirst · (act − fst)
  · rcases hfirst with h0 | ⟨h1, h2⟩
    · rw [h0]; simp
    · rw [h2]; simp
  -- continuity
  · exact gateE hx.bact hx.lstAct (fun h1 h2 => by rw [(hcont h1 h2).1]; rfl)
  · exact gateE hx.bact hx.lstAct (fun h1 h2 => by rw [(hcont h1 h2).2.1]; rfl)
  · exact gateE hx.bact hx.lstAct (fun h1 h2 => by rw [(hcont h1 h2).2.2.1]; simp)
  · exact gateE hx.bact hx.lstAct (fun h1 h2 => by rw [(hcont h1 h2).2.2.2.1]; simp)
  · exact gateE hx.bact hx.lstAct (fun h1 h2 => by rw [(hcont h1 h2).2.2.2.2.1]; simp)
  · exact gateE hx.bact hx.lstAct (fun h1 h2 => by rw [(hcont h1 h2).2.2.2.2.2.1]; simp)
  · exact gateE hx.bact hx.lstAct (fun h1 h2 => by rw [(hcont h1 h2).2.2.2.2.2.2.1]; simp)
  · exact gateE hx.bact hx.lstAct (fun h1 h2 => by rw [(hcont h1 h2).2.2.2.2.2.2.2]; simp)
  -- lst · next act · (1 − next fst)
  · exact gate2 hx.blst hyb (fun h1 h2 => by rw [hafter h1 h2]; rfl)
  -- isTransition · (1 − act) · next act
  · rcases hlast with ⟨h0, h2⟩ | ⟨h1, -⟩
    · rw [h0]
      rcases (by have := hx.bact; omega : X.act = 0 ∨ X.act = 1) with ha | ha
      · rw [h2 ha, ha]; simp
      · rw [ha]; simp
    · rw [h1]; simp
  -- INIT rows
  · exact gate hx.bfst (fun h => by rw [(hx.init h).1]; simp)
  · exact gate hx.bfst (fun h => by rw [(hx.init h).2.1]; simp)
  · exact gate hx.bfst (fun h => by rw [(hx.init h).2.2.1]; simp)
  · exact gate hx.bfst (fun h => by rw [(hx.init h).2.2.2.1]; rfl)
  · exact gate hx.bfst (fun h => by rw [(hx.init h).2.2.2.2.1]; simp)
  · exact gate hx.bfst (fun h => by rw [(hx.init h).2.2.2.2.2.1]; rfl)
  · exact gate hx.bfst (fun h => by rw [(hx.init h).2.2.2.2.2.2]; simp)
  -- READ rows
  · exact gate hx.brd (fun h => by rw [(hx.rd h).1]; simp)
  · exact gate hx.brd (fun h => by rw [(hx.rd h).2.1]; simp)
  · exact gate hx.brd (fun h => by rw [(hx.rd h).2.2.1]; rfl)
  · exact gate hx.brd (fun h => by rw [(hx.rd h).2.2.2.1]; rfl)
  · exact gate hx.brd (fun h => by rw [(hx.rd h).2.2.2.2.1]; rfl)
  · exact gate hx.brd (fun h => by rw [(hx.rd h).2.2.2.2.2]; rfl)
  -- GRANT rows
  · refine gate hx.bgr (fun h => ?_)
    obtain ⟨h1, -, -, -, -⟩ := hx.gr h
    rw [h1]
    have := hx.bisL; have := hx.bsf; have := hx.bal
    rcases (by omega : X.isL = 0 ∨ X.isL = 1) with e | e <;> rw [e] <;> simp
  · refine gate hx.bgr (fun h => ?_)
    obtain ⟨-, h2, h3, -, -⟩ := hx.gr h
    rw [h2]
    have := hx.bok; have := hx.bsf
    rcases (by omega : X.ok = 0 ∨ X.ok = 1) with e | e <;>
      rcases (by omega : X.sf = 0 ∨ X.sf = 1) with f | f <;> rw [e, f] <;> simp
    have := h3 f
    omega
  · exact gate2 hx.bgr hx.bok (fun h1 h2 => by rw [(hx.gr h1).2.2.2.1 h2]; rfl)
  · refine gate hx.bgr (fun h => ?_)
    obtain ⟨-, -, -, -, h5⟩ := hx.gr h
    rw [h5]
    have := hx.bisL; have := hx.bok
    rcases (by omega : X.isL = 0 ∨ X.isL = 1) with e | e <;>
      rcases (by omega : X.ok = 0 ∨ X.ok = 1) with f | f <;> rw [e, f] <;> simp

end ZkFormal.NearV3.Sched.Complete
