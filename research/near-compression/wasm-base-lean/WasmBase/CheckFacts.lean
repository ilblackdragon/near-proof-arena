import WasmBase.Check
/-!
# Facts established by a successful `check`
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

theorem mapM_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (rs : List β), l.mapM f = some rs →
      rs.length = l.length ∧ ∀ i (hi : i < l.length), f l[i] = rs[i]? := by
  intro l
  induction l with
  | nil => intro rs h; simp at h; subst h; simp
  | cons a l ih =>
    intro rs h
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      simp only [hfa] at h
      cases hml : l.mapM f with
      | none => simp [hml] at h
      | some rs' =>
        simp only [hml, pure, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hall⟩ := ih rs' hml
        refine ⟨by simp [hlen], ?_⟩
        intro i hi
        cases i with
        | zero => simp [hfa]
        | succ i => simpa using hall i (by simpa using hi)

theorem foldl_max_ge (l : List Nat) (a : Nat) : ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih =>
    intro x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · have := foldl_max_init l (max a x)
      omega
    · exact ih _ x hx
where
  foldl_max_init : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons y l ih => intro a; simp only [List.foldl_cons]; have := ih (max a y); omega

/-- **Instructions outside the base checker's domain** (the E2E M2 additions): conversions,
`unreachable`, `if`, `else`, `memory.grow`/`memory.size`, and a call of an import.  The base
checker rejects each of them (`verifyAt_special`); the M2 checker admits them with its own records.
`CheckFacts` states the base facts (`verifyAt`, `recordOf`) only at the other pcs, so it holds for
both checkers. -/
def m2Special (p : Prepared) : Instr → Bool
  | .num op => op == 0xA7 || op == 0xAC || op == 0xAD
  | .unreachable => true
  | .if_ _ => true
  | .else_ => true
  | .memGrow => true
  | .memSize => true
  | .call fi => decide (fi < p.m.imports.size)
  | _ => false

/-- The opcodes an M2-addition record carries (conversions, `unreachable` = 0, `else` = `opJump`,
`if` = `opIf`, a host call `opHost`/`0x242`, `memory.grow`/`size` `0x240`/`0x241`). -/
def m2OpNat (n : Nat) : Bool :=
  n == 0 || n == 0xA7 || n == 0xAC || n == 0xAD || n == 0x102 || n == 0x106 || n == 0x1FF ||
  n == 0x240 || n == 0x241 || n == 0x242

/-- Everything the base-faithful proof uses from `check`. -/
structure CheckFacts (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat) (pf : PFunc)
    (ck : CheckOut) : Prop where
  func : p.funcs[fn]? = some pf
  params : pf.type.params.size ≤ 8
  nloc : pf.type.params.size + pf.locals.size ≤ 64
  results : pf.type.results.size ≤ 1
  resTypes : ∀ t ∈ pf.type.results.toList, t = .i32 ∨ t = .i64
  locTypes : ∀ t ∈ pf.locals.toList, t = .i32 ∨ t = .i64
  parTypes : ∀ t ∈ pf.type.params.toList, t = .i32 ∨ t = .i64
  codeLt : pf.code.size < 2 ^ 20
  gasSize : pf.gas.size = pf.code.size
  lsize : ck.labels.size = pf.code.size
  hsize : ck.heights.size = pf.code.size
  l0 : ck.labels[0]? = some [rootLabel pf]
  h0 : ck.heights[0]? = some 0
  /-- the base successor obligations, at every pc whose instruction is not an M2 addition -/
  verify : ∀ pc, pc < pf.code.size → ∀ ins, pf.code[pc]? = some ins → m2Special p ins = false →
    verifyAt p pf ck.labels ck.heights pc = true
  hBound : ∀ pc, pc < pf.code.size → ck.heights[pc]?.getD 0 < 2 ^ 16
  records : ck.records.size = pf.code.size
  /-- the base record, at every pc whose instruction is not an M2 addition -/
  recs : ∀ pc, pc < pf.code.size → ∃ ins, pf.code[pc]? = some ins ∧ (m2Special p ins = false →
    ∃ fee, feeUnits cfg pf.gas[pc]? = some fee ∧ fee ≤ ck.maxFee ∧
    recordOf off cinfo (ck.labels[pc]?.getD []) (ck.heights[pc]?.getD 0) fee (off + pc) ins = ck.records[pc]?)
  /-- at an M2 addition the record carries an M2 opcode (so no base chip's FETCH can match it) -/
  special : ∀ pc, pc < pf.code.size → ∀ ins, pf.code[pc]? = some ins → m2Special p ins = true →
    ∃ op rest, ck.records[pc]? = some ((off + pc) :: op :: rest) ∧ m2OpNat op = true ∧
      (op = Chips.Ctrl.opJump → ins = .else_)
  /-- at an `else` (M2): the true arm ends at `label.height + arity`, the label target carries the
  outer labels at that height, and the record is CTRL's jump to the target -/
  elseF : ∀ pc, pc < pf.code.size → pf.code[pc]? = some .else_ → ∃ lab rest fee,
    ck.labels[pc]? = some (lab :: rest) ∧ ck.heights[pc]?.getD 0 = lab.height + lab.arity ∧
    lab.target < pf.code.size ∧ ck.labels[lab.target]? = some rest ∧
    ck.heights[lab.target]? = some (ck.heights[pc]?.getD 0) ∧
    feeUnits cfg pf.gas[pc]? = some fee ∧ fee ≤ ck.maxFee ∧
    ck.records[pc]? = some [off + pc, Chips.Ctrl.opJump, ck.heights[pc]?.getD 0, fee, lab.target + off, 0, 0, 0]
  arity : ck.arity = pf.type.results.size
  resTag : ck.resTag = if pf.type.results[0]? == some .i64 then 1 else 0
  localTags : ck.localTags = (pf.type.params.toList ++ pf.locals.toList).map vtTag
  locIdx : ∀ i ∈ pf.code.toList, ∀ x, (i = .localGet x ∨ i = .localSet x ∨ i = .localTee x) →
    x < pf.type.params.size + pf.locals.size
  np : ck.np = pf.type.params.size
  nl : ck.nl = pf.type.params.size + pf.locals.size
  charge : ck.charge = pf.stackCharge
  chargeLt : pf.stackCharge < 2 ^ 26
  prologue : ck.prologue * cfg.regularOpCost = pf.prologueGas
  prologueLt : ck.prologue < 2 ^ 16
  regPos : cfg.regularOpCost ≠ 0

theorem recordOf_fee {off : Nat} {cinfo : Nat → Option Nat} {ls : List Label} {h fee pc : Nat}
    {ins : Instr} {r : List Nat} (hr : recordOf off cinfo ls h fee pc ins = some r) : r.getD 3 0 = fee := by
  unfold recordOf at hr
  split at hr <;> (try split at hr) <;> (try split at hr) <;> simp_all <;>
    (try (obtain ⟨_, rfl⟩ := hr; rfl)) <;> (try (subst hr; rfl))

/-- A family numeric opcode is not a conversion. -/
theorem m2Special_fam {p : Prepared} {op : Nat} (h : isFamilyNum op = true) : m2Special p (.num op) = false := by
  simp only [isFamilyNum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [m2Special, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  omega

/-- An instruction with a base kind is not an M2 addition. -/
theorem m2Special_kind {p : Prepared} {ls : List Label} {ins : Instr} {k : Kind}
    (h : kindOf ls ins = some k) : m2Special p ins = false := by
  cases ins <;> simp only [m2Special] <;> simp_all [kindOf]
  rename_i op
  have := m2Special_fam (p := p) h.1
  simpa [m2Special] using this

/-- Discharge `m2Special p ins = false` at a base step lemma's pc. -/
macro "m2_ns" : tactic => `(tactic| first
  | rfl
  | (subst_vars; rfl)
  | (apply m2Special_fam; assumption)
  | (apply m2Special_kind; assumption))

/-- A pc the base `verifyAt` accepts holds no M2 addition. -/
theorem verifyAt_special {p : Prepared} {pf : PFunc} {L : Array (List Label)} {H : Array Nat} {pc : Nat}
    {ins : Instr} (hv : verifyAt p pf L H pc = true) (hins : pf.code[pc]? = some ins) :
    m2Special p ins = false := by
  cases hs : m2Special p ins
  · rfl
  · exfalso
    unfold verifyAt at hv
    rw [hins] at hv
    cases hL : L[pc]? <;> cases hH : H[pc]? <;> simp only [hL, hH, reduceCtorEq] at hv
    cases ins <;> simp only [m2Special, reduceCtorEq] at hs <;> (try simp [kindOf, sigOf] at hv)
    · rename_i fi
      have : ¬ p.m.imports.size ≤ fi := by simpa using hs
      simp [this] at hv
    · rename_i op
      simp only [Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with (rfl | rfl) | rfl <;> simp [isFamilyNum] at hv

end WasmBase

namespace WasmBase
open NearSpecV3.Wasm

theorem check_sound {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat} {ck : CheckOut}
    (h : check cfg p fn off cinfo = some ck) : ∃ pf, CheckFacts cfg p fn off cinfo pf ck := by
  unfold check at h
  cases hpf : p.funcs[fn]? with
  | none => simp [hpf] at h
  | some pf =>
    simp only [hpf] at h
    cases hb : basicOk cfg pf with
    | false => simp [hb] at h
    | true =>
      simp only [hb, ite_true] at h
      cases han : analyze p pf with
      | none => simp [han] at h
      | some LH =>
        obtain ⟨L, H⟩ := LH
        simp only [han] at h
        cases hs : structOk p pf L H with
        | false => simp [hs] at h
        | true =>
          simp only [hs, ite_true] at h
          cases hm : (List.range pf.code.size).mapM (recordAt cfg pf L H off cinfo) with
          | none => simp [hm] at h
          | some recs =>
            simp only [hm, Option.some.injEq] at h
            subst h
            obtain ⟨hlen, hall⟩ := mapM_some _ _ _ hm
            simp only [List.length_range] at hlen
            simp only [basicOk, Bool.and_eq_true, decide_eq_true_eq] at hb
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨g1, g1a⟩, g1b⟩, g2⟩, g3⟩, g4⟩, g5⟩, g5a⟩, gp⟩, gch⟩, greg⟩, gpro⟩, gprl⟩ := hb
            simp only [structOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
              at hs
            obtain ⟨⟨⟨⟨g6, g6a⟩, g6b⟩, g6c⟩, g7⟩ := hs
            have fee_of : ∀ pc (hpc : pc < pf.code.size), ∃ ins fee, pf.code[pc]? = some ins ∧
                feeUnits cfg pf.gas[pc]? = some fee ∧
                recordOf off cinfo (L[pc]?.getD []) (H[pc]?.getD 0) fee (off + pc) ins = recs[pc]? := by
              intro pc hpc
              have := hall pc (by simpa using hpc)
              simp only [List.getElem_range, recordAt] at this
              revert this
              have hr : recs[pc]? = some (recs[pc]'(by omega)) := List.getElem?_eq_getElem (by omega)
              cases hc : pf.code[pc]? with
              | none => intro e; simp [hr] at e
              | some ins =>
                cases hfu : feeUnits cfg pf.gas[pc]? with
                | none => intro e; simp [hr] at e
                | some fee => intro e; exact ⟨ins, fee, rfl, rfl, e⟩
            have recMax : ∀ pc (hpc : pc < pf.code.size),
                (recs[pc]'(by omega)).getD 3 0 ≤ (recs.map fun r => r.getD 3 0).foldl max 0 := by
              intro pc hpc
              apply foldl_max_ge
              simp only [List.mem_map]
              exact ⟨recs[pc]'(by omega), List.getElem_mem _, rfl⟩
            refine ⟨pf, {
              func := hpf, params := g1, nloc := g1a, results := g1b,
              resTypes := ?_, locTypes := ?_, parTypes := ?_, codeLt := g5, gasSize := g5a,
              lsize := g6, hsize := g6a, l0 := g6b, h0 := g6c,
              verify := fun pc hpc _ _ _ => by have := g7 pc hpc; simp_all,
              hBound := fun pc hpc => by have := g7 pc hpc; simp_all,
              records := by simp [hlen],
              recs := ?_, special := ?_, elseF := ?_,
              arity := rfl, resTag := rfl, localTags := rfl, locIdx := ?_,
              np := rfl, nl := rfl, charge := rfl, chargeLt := gch,
              prologue := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero gpro), prologueLt := gprl, regPos := greg }⟩
            · intro t ht
              rw [Array.all_eq_true] at g2
              obtain ⟨x, hx, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp ht)
              have := g2 x hx
              revert this
              cases pf.type.results[x] <;> decide
            · intro t ht
              rw [Array.all_eq_true] at g3
              obtain ⟨x, hx, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp ht)
              have := g3 x hx
              revert this
              cases pf.locals[x] <;> decide
            · intro t ht
              rw [Array.all_eq_true] at gp
              obtain ⟨x, hx, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp ht)
              have := gp x hx
              revert this
              cases pf.type.params[x] <;> decide
            · intro pc hpc
              obtain ⟨ins, fee, h1, h2, h3⟩ := fee_of pc hpc
              have hr : recs[pc]? = some (recs[pc]'(by omega)) := List.getElem?_eq_getElem (by omega)
              refine ⟨ins, h1, fun _ => ⟨fee, h2, ?_, by simpa using h3⟩⟩
              rw [hr] at h3
              have := recMax pc hpc
              rw [recordOf_fee h3] at this
              exact this
            · intro pc hpc ins hins hs
              have := verifyAt_special (g7 pc hpc).1 hins
              rw [hs] at this; cases this
            · intro pc hpc hins
              have := verifyAt_special (g7 pc hpc).1 hins
              simp [m2Special] at this
            · intro i hi x hx
              rw [Array.all_eq_true] at g4
              obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hi)
              have := g4 k hk
              rcases hx with e | e | e <;> rw [e] at this <;> simpa using this

/-- A base `check` admits no M2 addition at any pc. -/
theorem check_nonspecial {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat}
    {ck : CheckOut} (h : check cfg p fn off cinfo = some ck) {pf : PFunc} (hpf : p.funcs[fn]? = some pf)
    {pc : Nat} {ins : Instr} (hins : pf.code[pc]? = some ins) : m2Special p ins = false := by
  have hpc : pc < pf.code.size := by
    rcases Nat.lt_or_ge pc pf.code.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hins; simp at hins
  unfold check at h
  simp only [hpf] at h
  cases hb : basicOk cfg pf with
  | false => simp [hb] at h
  | true =>
    simp only [hb, ite_true] at h
    cases han : analyze p pf with
    | none => simp [han] at h
    | some LH =>
      obtain ⟨L, H⟩ := LH
      simp only [han] at h
      cases hs : structOk p pf L H with
      | false => simp [hs] at h
      | true =>
        simp only [structOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hs
        exact verifyAt_special (hs.2 pc hpc).1 hins

/-- **`CheckFacts` from its parts**: the shape facts follow from `basicOk`; the rest are given.
Used for checkers other than the base `check` (the M2 checker, `M2Ctx.lean`). -/
theorem CheckFacts.of_parts {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat}
    {pf : PFunc} {ck : CheckOut} (hpf : p.funcs[fn]? = some pf) (hb : basicOk cfg pf = true)
    (lsize : ck.labels.size = pf.code.size) (hsize : ck.heights.size = pf.code.size)
    (l0 : ck.labels[0]? = some [rootLabel pf]) (h0 : ck.heights[0]? = some 0)
    (verify : ∀ pc, pc < pf.code.size → ∀ ins, pf.code[pc]? = some ins → m2Special p ins = false →
      verifyAt p pf ck.labels ck.heights pc = true)
    (hBound : ∀ pc, pc < pf.code.size → ck.heights[pc]?.getD 0 < 2 ^ 16)
    (records : ck.records.size = pf.code.size)
    (recs : ∀ pc, pc < pf.code.size → ∃ ins, pf.code[pc]? = some ins ∧ (m2Special p ins = false →
      ∃ fee, feeUnits cfg pf.gas[pc]? = some fee ∧ fee ≤ ck.maxFee ∧
      recordOf off cinfo (ck.labels[pc]?.getD []) (ck.heights[pc]?.getD 0) fee (off + pc) ins = ck.records[pc]?))
    (special : ∀ pc, pc < pf.code.size → ∀ ins, pf.code[pc]? = some ins → m2Special p ins = true →
      ∃ op rest, ck.records[pc]? = some ((off + pc) :: op :: rest) ∧ m2OpNat op = true ∧
      (op = Chips.Ctrl.opJump → ins = .else_))
    (elseF : ∀ pc, pc < pf.code.size → pf.code[pc]? = some .else_ → ∃ lab rest fee,
      ck.labels[pc]? = some (lab :: rest) ∧ ck.heights[pc]?.getD 0 = lab.height + lab.arity ∧
      lab.target < pf.code.size ∧ ck.labels[lab.target]? = some rest ∧
      ck.heights[lab.target]? = some (ck.heights[pc]?.getD 0) ∧
      feeUnits cfg pf.gas[pc]? = some fee ∧ fee ≤ ck.maxFee ∧
      ck.records[pc]? = some [off + pc, Chips.Ctrl.opJump, ck.heights[pc]?.getD 0, fee, lab.target + off, 0, 0, 0])
    (arity : ck.arity = pf.type.results.size)
    (resTag : ck.resTag = if pf.type.results[0]? == some .i64 then 1 else 0)
    (localTags : ck.localTags = (pf.type.params.toList ++ pf.locals.toList).map vtTag)
    (np : ck.np = pf.type.params.size) (nl : ck.nl = pf.type.params.size + pf.locals.size)
    (charge : ck.charge = pf.stackCharge) (prologue : ck.prologue = pf.prologueGas / cfg.regularOpCost) :
    CheckFacts cfg p fn off cinfo pf ck := by
  simp only [basicOk, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨g1, g1a⟩, g1b⟩, g2⟩, g3⟩, g4⟩, g5⟩, g5a⟩, gp⟩, gch⟩, greg⟩, gpro⟩, gprl⟩ := hb
  refine
    { func := hpf, params := g1, nloc := g1a, results := g1b,
      resTypes := ?_, locTypes := ?_, parTypes := ?_, codeLt := g5, gasSize := g5a,
      lsize := lsize, hsize := hsize, l0 := l0, h0 := h0, verify := verify, hBound := hBound,
      records := records, recs := recs, special := special, elseF := elseF, arity := arity, resTag := resTag, localTags := localTags,
      locIdx := ?_, np := np, nl := nl, charge := charge, chargeLt := gch,
      prologue := by rw [prologue]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero gpro),
      prologueLt := by rw [prologue]; exact gprl, regPos := greg }
  · intro t ht
    rw [Array.all_eq_true] at g2
    obtain ⟨x, hx, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp ht)
    have := g2 x hx
    revert this
    cases pf.type.results[x] <;> decide
  · intro t ht
    rw [Array.all_eq_true] at g3
    obtain ⟨x, hx, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp ht)
    have := g3 x hx
    revert this
    cases pf.locals[x] <;> decide
  · intro t ht
    rw [Array.all_eq_true] at gp
    obtain ⟨x, hx, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp ht)
    have := gp x hx
    revert this
    cases pf.type.params[x] <;> decide
  · intro i hi x hx
    rw [Array.all_eq_true] at g4
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hi)
    have := g4 k hk
    rcases hx with e | e | e <;> rw [e] at this <;> simpa using this

/-- **The module facts the soundness proof uses.**  A successful `checkModule` gives them
(`checkModule_sound`), and so does `checkModuleM2` (`M2Ctx.lean`): the per-function facts are
`CheckFacts`, whose base obligations are stated only at pcs that are not M2 additions. -/
structure ModFacts (cfg : NearCfg) (p : Prepared) (entry : Nat) (M : ModOut) : Prop where
  head : M.fns.head? = some entry
  cks : ∀ k, k < M.fns.length → ∃ pf,
    CheckFacts cfg p (M.fns.getD k 0) (M.offs.getD k 0) (callInfo p M.fns M.offs) pf (M.cks.getD k default)
  pfs : ∀ k, k < M.fns.length → ∃ pf, p.funcs[M.fns.getD k 0]? = some pf ∧ M.sizes.getD k 0 = pf.code.size
  total : M.codeSize < 2 ^ 20
  layout : layoutOk M.fns M.offs M.sizes M.codeSize = true
  recSize : M.records.size = M.codeSize
  recs : ∀ j, j < M.codeSize → M.records[j]? =
      some (((M.cks.getD (locate M.offs M.sizes j).1 default).records)[(locate M.offs M.sizes j).2]?.getD [])
  feeLe : ∀ k j, k < M.fns.length → j < M.fns.length →
    (M.cks.getD k default).maxFee + (M.cks.getD j default).prologue ≤ M.maxFee
  closed : M.fns.all (fun fn => ((p.funcs[fn]?.map (calleesOf p)).getD []).all (M.fns.contains ·)) = true
  offs0 : M.offs.getD 0 0 = 0
  entryParams : ∃ pf, p.funcs[entry]? = some pf ∧ pf.type.params.size = 0
  funcs : ∀ k, k < M.fns.length → M.funcs.getD k [] = funcRow (M.offs.getD k 0) (M.cks.getD k default)
  funcsLen : M.funcs.length = M.fns.length

end WasmBase
