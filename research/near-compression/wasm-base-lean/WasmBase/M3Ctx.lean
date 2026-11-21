import WasmBase.M2Ctx
import WasmBase.M3Check
import WasmBase.Main.SegGrowCode
/-!
# WasmBase.M3Ctx — the static context of an M3 run, from `checkModuleM3 = some _` (E2E M6, GROW2)

`ModFacts` (`CheckFacts.lean`) requires the record at every M2-addition pc to carry an M2 opcode
(`m2OpNat`).  `checkModuleM3`'s `memory.grow` / `memory.size` records carry the MEMG opcodes
`0x40` / `0x3F` (`Chips.opMemGrow` / `Chips.opMemSize`), which `m2OpNat` omits, so **no `Ctx` has
an M3 module's records**: a module with a `memory.grow` has no `ModFacts` for its M3 output.

This file adds, without touching `m2OpNat` or any of its users:

* `m3OpNat` (`m2OpNat` plus `0x3F`, `0x40`), `CheckFacts3` / `ModFacts3` / `Ctx3` (the generalised
  facts with `m3OpNat` in `special`), and the inclusions `CheckFacts.to3`, `ModFacts.to3`,
  `Ctx.to3`, `M2Ctx.toCtx3` (every `M2Ctx` fact is an M3 fact);
* `CheckFactsM3` / `checkM3_sound`, `ModFactsM3` / `checkModuleM3_sound`, and **`M3Ctx`** with the
  `M2Ctx` API (`factsOf`, `recG`, `loc_unique`, `off_bound`, `rec_at`, `rec_fee_le`, `layout`, …);
* `checkM3_facts` / `checkModuleM3_modFacts3` / **`M3Ctx.toCtx3`**: the M3 module's generalised
  facts (from the checker, nothing assumed);
* **the M2 shadow** `checkModuleM3_M2` / **`M3Ctx.toM2`**: a module `checkModuleM3` admits is also
  admitted by `checkModuleM2`, with the same functions, offsets, sizes, code size, function table
  and per-function labels / heights / arity / tags / counts / charge / prologue — only the records
  (at `memory.grow`, `memory.size` and import calls, `recordAtM3_eq_M2`) and the fee bounds differ.
  So the semantic stack over `Ctx` (`RelW`, the step lemmas, `exec_rowsJQ`) runs on
  `X.toM2.toCtx`, whose `cfg`, `p`, `fn`, offsets and static labels/heights are `X`'s
  (`M3Ctx.toM2_*`), while the CODE table of a grow trace is bound to the M3 records (`CodeOK3`);
* the MEMG code facts at module level: `M3Ctx.recG_memGrow` / `recG_memSize` (a global record with
  opcode `0x40` / `0x3F` is the record of `memory.grow` / `memory.size` at its location, with its
  fee, linear flag and static height) and `M3Ctx.memGrow_succ` / `memSize_succ` (the successor).
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-! ## 1. `m3OpNat` and the generalised facts -/

/-- The opcodes an M3-addition record carries: the M2 ones and the MEMG opcodes `0x3F` / `0x40`. -/
def m3OpNat (n : Nat) : Bool := m2OpNat n || n == Chips.opMemSize || n == Chips.opMemGrow

theorem m3OpNat_of_m2 {n : Nat} (h : m2OpNat n = true) : m3OpNat n = true := by
  simp [m3OpNat, h]

theorem m3OpNat_lt {n : Nat} (h : m3OpNat n = true) : n < 0x243 := by
  simp only [m3OpNat, m2OpNat, Chips.opMemSize, Chips.opMemGrow, Bool.or_eq_true, beq_iff_eq] at h; omega

/-- `CheckFacts` with `m3OpNat` in place of `m2OpNat` in `special` (all other fields verbatim). -/
structure CheckFacts3 (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat) (pf : PFunc)
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
  verify : ∀ pc, pc < pf.code.size → ∀ ins, pf.code[pc]? = some ins → m2Special p ins = false →
    verifyAt p pf ck.labels ck.heights pc = true
  hBound : ∀ pc, pc < pf.code.size → ck.heights[pc]?.getD 0 < 2 ^ 16
  records : ck.records.size = pf.code.size
  recs : ∀ pc, pc < pf.code.size → ∃ ins, pf.code[pc]? = some ins ∧ (m2Special p ins = false →
    ∃ fee, feeUnits cfg pf.gas[pc]? = some fee ∧ fee ≤ ck.maxFee ∧
    recordOf off cinfo (ck.labels[pc]?.getD []) (ck.heights[pc]?.getD 0) fee (off + pc) ins = ck.records[pc]?)
  special : ∀ pc, pc < pf.code.size → ∀ ins, pf.code[pc]? = some ins → m2Special p ins = true →
    ∃ op rest, ck.records[pc]? = some ((off + pc) :: op :: rest) ∧ m3OpNat op = true ∧
      (op = Chips.Ctrl.opJump → ins = .else_)
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

/-- **Every `CheckFacts` is a `CheckFacts3`** (`m2OpNat ⊆ m3OpNat`). -/
theorem CheckFacts.to3 {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat} {pf : PFunc}
    {ck : CheckOut} (F : CheckFacts cfg p fn off cinfo pf ck) : CheckFacts3 cfg p fn off cinfo pf ck :=
  { F with
    special := fun pc hpc ins hins hs => by
      obtain ⟨op, rest, h1, h2, h3⟩ := F.special pc hpc ins hins hs
      exact ⟨op, rest, h1, m3OpNat_of_m2 h2, h3⟩ }

/-- `ModFacts` with `CheckFacts3` per function. -/
structure ModFacts3 (cfg : NearCfg) (p : Prepared) (entry : Nat) (M : ModOut) : Prop where
  head : M.fns.head? = some entry
  cks : ∀ k, k < M.fns.length → ∃ pf,
    CheckFacts3 cfg p (M.fns.getD k 0) (M.offs.getD k 0) (callInfo p M.fns M.offs) pf (M.cks.getD k default)
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

theorem ModFacts.to3 {cfg : NearCfg} {p : Prepared} {entry : Nat} {M : ModOut} (F : ModFacts cfg p entry M) :
    ModFacts3 cfg p entry M :=
  { F with cks := fun k hk => by obtain ⟨pf, h⟩ := F.cks k hk; exact ⟨pf, h.to3⟩ }

/-- The static context with the generalised (M3) module facts. -/
structure Ctx3 where
  cfg : NearCfg
  p : Prepared
  fn : Nat
  M : ModOut
  g0 : Nat
  hM : ModFacts3 cfg p fn M

def Ctx.to3 (X : Ctx) : Ctx3 := ⟨X.cfg, X.p, X.fn, X.M, X.g0, X.hM.to3⟩

/-- **Every M2 context is an M3-fact context.** -/
def M2Ctx.toCtx3 (X : M2Ctx) : Ctx3 := X.toCtx.to3

/-! ## 2. Per-function facts of `checkM3` -/

/-- Everything a successful `checkM3` gives about one function (`CheckFactsM2` with `recordAtM3`). -/
structure CheckFactsM3 (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat)
    (pf : PFunc) (ck : CheckOut) : Prop where
  func : p.funcs[fn]? = some pf
  basic : basicOk cfg pf = true
  lsize : ck.labels.size = pf.code.size
  hsize : ck.heights.size = pf.code.size
  l0 : ck.labels[0]? = some [rootLabel pf]
  h0 : ck.heights[0]? = some 0
  verify : ∀ pc, pc < pf.code.size → verifyAtM2 p pf ck.labels ck.heights pc = true
  hBound : ∀ pc, pc < pf.code.size → ck.heights[pc]?.getD 0 < 2 ^ 16
  records : ck.records.size = pf.code.size
  recs : ∀ pc, pc < pf.code.size → recordAtM3 cfg p pf ck.labels ck.heights off cinfo pc = ck.records[pc]?
  feeLe : ∀ pc, pc < pf.code.size → (ck.records[pc]?.getD []).getD 3 0 ≤ ck.maxFee
  arity : ck.arity = pf.type.results.size
  resTag : ck.resTag = if pf.type.results[0]? == some .i64 then 1 else 0
  localTags : ck.localTags = (pf.type.params.toList ++ pf.locals.toList).map vtTag
  np : ck.np = pf.type.params.size
  nl : ck.nl = pf.type.params.size + pf.locals.size
  charge : ck.charge = pf.stackCharge
  prologue : ck.prologue = pf.prologueGas / cfg.regularOpCost

theorem checkM3_sound {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat}
    {ck : CheckOut} (h : checkM3 cfg p fn off cinfo = some ck) :
    ∃ pf, CheckFactsM3 cfg p fn off cinfo pf ck := by
  unfold checkM3 at h
  cases hpf : p.funcs[fn]? with
  | none => simp [hpf] at h
  | some pf =>
    simp only [hpf] at h
    cases hb : basicOk cfg pf with
    | false => simp [hb] at h
    | true =>
      simp only [hb, ite_true] at h
      cases han : analyzeM2 p pf with
      | none => simp [han] at h
      | some LH =>
        obtain ⟨L, H⟩ := LH
        simp only [han] at h
        cases hs : structOkM2 p pf L H with
        | false => simp [hs] at h
        | true =>
          simp only [hs, ite_true] at h
          cases hm : (List.range pf.code.size).mapM (recordAtM3 cfg p pf L H off cinfo) with
          | none => simp [hm] at h
          | some recs =>
            simp only [hm, Option.some.injEq] at h
            subst h
            obtain ⟨hlen, hall⟩ := mapM_some _ _ _ hm
            simp only [List.length_range] at hlen
            simp only [structOkM2, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
              at hs
            obtain ⟨⟨⟨⟨g6, g6a⟩, g6b⟩, g6c⟩, g7⟩ := hs
            refine ⟨pf, ⟨hpf, hb, g6, g6a, g6b, g6c, fun pc hpc => (g7 pc hpc).1,
              fun pc hpc => by have := (g7 pc hpc).2; simpa using this, by simp [hlen], ?_, ?_,
              rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
            · intro pc hpc
              have := hall pc (by simpa using hpc)
              simp only [List.getElem_range] at this
              rw [this]; simp
            · intro pc hpc
              simp only [List.getElem?_toArray]
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              apply foldl_max_ge
              simp only [List.mem_map]
              exact ⟨recs[pc]'(by omega), List.getElem_mem _, rfl⟩

/-- The labels/heights at `pc` exist (sizes match the code). -/
theorem CheckFactsM3.lh {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat}
    {pf : PFunc} {ck : CheckOut} (F : CheckFactsM3 cfg p fn off cinfo pf ck) {pc : Nat}
    (hpc : pc < pf.code.size) :
    ∃ ls h, ck.labels[pc]? = some ls ∧ ck.heights[pc]? = some h :=
  ⟨ck.labels[pc]'(by rw [F.lsize]; exact hpc), ck.heights[pc]'(by rw [F.hsize]; exact hpc),
    Array.getElem?_eq_getElem _, Array.getElem?_eq_getElem _⟩

/-! ## 3. Module facts of `checkModuleM3` -/

/-- What a successful `checkModuleM3` gives (`ModFactsM2` with `checkM3`, the M3 host rows and the
memory limit). -/
structure ModFactsM3 (cfg : NearCfg) (p : Prepared) (entry : Nat) (MH : ModOutH) : Prop where
  head : MH.mod.fns.head? = some entry
  cks : ∀ k, k < MH.mod.fns.length →
    checkM3 cfg p (MH.mod.fns.getD k 0) (MH.mod.offs.getD k 0) (callInfo p MH.mod.fns MH.mod.offs) =
      some (MH.mod.cks.getD k default)
  pfs : ∀ k, k < MH.mod.fns.length → ∃ pf, p.funcs[MH.mod.fns.getD k 0]? = some pf ∧
    MH.mod.sizes.getD k 0 = pf.code.size
  total : MH.mod.codeSize < 2 ^ 20
  layout : layoutOk MH.mod.fns MH.mod.offs MH.mod.sizes MH.mod.codeSize = true
  recSize : MH.mod.records.size = MH.mod.codeSize
  recs : ∀ j, j < MH.mod.codeSize → MH.mod.records[j]? =
      some (((MH.mod.cks.getD (locate MH.mod.offs MH.mod.sizes j).1 default).records)[
        (locate MH.mod.offs MH.mod.sizes j).2]?.getD [])
  feeLe : ∀ k j, k < MH.mod.fns.length → j < MH.mod.fns.length →
    (MH.mod.cks.getD k default).maxFee + (MH.mod.cks.getD j default).prologue ≤ MH.mod.maxFee
  closed : MH.mod.fns.all (fun fn => ((p.funcs[fn]?.map (calleesOf p)).getD []).all (MH.mod.fns.contains ·)) = true
  offs0 : MH.mod.offs.getD 0 0 = 0
  entryParams : ∃ pf, p.funcs[entry]? = some pf ∧ pf.type.params.size = 0
  imports : calledImportsOkM2 p MH.mod.fns = true
  funcs : ∀ k, k < MH.mod.fns.length →
    MH.mod.funcs.getD k [] = funcRow (MH.mod.offs.getD k 0) (MH.mod.cks.getD k default)
  funcsLen : MH.mod.funcs.length = MH.mod.fns.length
  hostRows : MH.hostRows = hostFnsM2.map hostRowM3
  maxPages : cfg.maxMemoryPages = Chips.maxPagesM3

theorem checkModuleM3_sound {cfg : NearCfg} {p : Prepared} {entry : Nat} {MH : ModOutH}
    (h : checkModuleM3 cfg p entry = some MH) : ModFactsM3 cfg p entry MH := by
  unfold checkModuleM3 at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i pfs hp
    split at h
    · simp at h
    · rename_i cks hc
      split at h
      · rename_i hcond
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hhd, htot, hlay, hcl, hent, himp, hmp⟩ := hcond
        obtain ⟨hcl1, hcl2⟩ := mapM_some _ _ _ hc
        obtain ⟨hpl1, hpl2⟩ := mapM_some _ _ _ hp
        simp only [List.length_range] at hcl1
        refine ⟨hhd, ?_, ?_, htot, hlay, by simp, ?_, ?_, hcl, ?_, ?_, himp, ?_, by simp, rfl, hmp⟩
        · intro k hk
          dsimp only at hk ⊢
          have := hcl2 k (by simpa using hk)
          simp only [List.getElem_range] at this
          rw [this, List.getD_eq_getElem?_getD (l := cks), List.getElem?_eq_getElem (by omega), Option.getD_some]
        · intro k hk
          dsimp only at hk ⊢
          have := hpl2 k hk
          refine ⟨pfs[k]'(by omega), ?_, ?_⟩
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, this,
              List.getElem?_eq_getElem (by omega)]
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem (show k < pfs.length by omega), Option.map_some, Option.getD_some]
        · intro j hj
          dsimp only at hj ⊢
          simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj, Option.map_some]
        · intro k j hk hj
          dsimp only at hk hj ⊢
          have a1 : (cks.getD k default).maxFee ≤ (cks.map (·.maxFee)).foldl max 0 := by
            apply foldl_max_ge
            simp only [List.mem_map]
            refine ⟨cks[k]'(by omega), List.getElem_mem _, ?_⟩
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
          have a2 : (cks.getD j default).prologue ≤ (cks.map (·.prologue)).foldl max 0 := by
            apply foldl_max_ge
            simp only [List.mem_map]
            refine ⟨cks[j]'(by omega), List.getElem_mem _, ?_⟩
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
          omega
        · dsimp only
          cases pfs with
          | nil => rfl
          | cons _ _ => rfl
        · cases hf : closureFns p entry with
          | nil => rw [hf] at hhd; simp at hhd
          | cons a rest =>
            rw [hf] at hhd hpl1 hpl2
            simp only [List.head?_cons, Option.some.injEq] at hhd
            subst hhd
            cases pfs with
            | nil => simp at hpl1
            | cons pf0 pfs' =>
              have := hpl2 0 (by simp)
              simp only [List.getElem_cons_zero, List.getElem?_cons_zero] at this
              simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hent
              exact ⟨pf0, this, hent⟩
        · intro k hk
          dsimp only at hk ⊢
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
      · simp at h

/-! ## 4. `recordAtM3` against `recordAtM2` -/

/-- **Away from `memory.grow`, `memory.size` and import calls, the M3 record is the M2 record.** -/
theorem recordAtM3_eq_M2 {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)} {H : Array Nat}
    {off pc : Nat} {cinfo : Nat → Option Nat} {ins : Instr} (hins : pf.code[pc]? = some ins)
    (hg : ins ≠ .memGrow) (hs : ins ≠ .memSize) (hc : ∀ fi, ins = .call fi → p.m.imports.size ≤ fi) :
    recordAtM3 cfg p pf L H off cinfo pc = recordAtM2 cfg p pf L H off cinfo pc := by
  unfold recordAtM3
  rw [hins]
  cases ins with
  | memGrow => exact absurd rfl hg
  | memSize => exact absurd rfl hs
  | call fi =>
    have := hc fi rfl
    simp only [show ¬ fi < p.m.imports.size by omega, if_false]
  | _ => rfl

/-- `hostChipM3` implies `hostAnyM2` (the latter's `find?` has the weaker predicate). -/
theorem hostAnyM2_of_chipM3 {name : String} {x : Nat × Nat × Nat × Nat × Nat} (h : hostChipM3 name = some x) :
    ∃ y, hostAnyM2 name = some y := by
  unfold hostChipM3 at h
  cases hf : hostFnsM2.find? (fun x => x.2.1 = name && Chips.hostShapeOk x.2.2.1 x.2.2.2) with
  | none => simp [hf] at h
  | some e =>
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    unfold hostAnyM2
    cases hf2 : hostFnsM2.find? (fun x => decide (x.2.1 = name)) with
    | none =>
      rw [List.find?_eq_none] at hf2
      exact absurd (by simpa using hp.1) (hf2 e hm)
    | some e2 => exact ⟨_, rfl⟩

/-- **Where the M3 record exists, so does the M2 record.** -/
theorem recordAtM2_of_M3 {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)} {H : Array Nat}
    {off pc : Nat} {cinfo : Nat → Option Nat} {r : List Nat}
    (hr : recordAtM3 cfg p pf L H off cinfo pc = some r) :
    ∃ r', recordAtM2 cfg p pf L H off cinfo pc = some r' := by
  cases hins : pf.code[pc]? with
  | none =>
    unfold recordAtM3 at hr; rw [hins] at hr
    exact ⟨r, hr⟩
  | some ins =>
    by_cases hg : ins = .memGrow
    · subst hg
      unfold recordAtM2
      rw [hins]
      cases feeUnits cfg pf.gas[pc]? <;> exact ⟨_, rfl⟩
    by_cases hs : ins = .memSize
    · subst hs
      unfold recordAtM3 at hr
      rw [hins] at hr
      cases hf : feeUnits cfg pf.gas[pc]? with
      | none => simp [hf] at hr
      | some fee => unfold recordAtM2; rw [hins, hf]; exact ⟨_, rfl⟩
    by_cases hc : ∃ fi, ins = .call fi ∧ fi < p.m.imports.size
    · obtain ⟨fi, rfl, hfi⟩ := hc
      have hr0 := hr
      unfold recordAtM3 at hr
      rw [hins] at hr
      simp only [hfi, if_true] at hr
      split at hr
      · rename_i hid np ar _ _ fee hch hfee
        unfold recordAtM2
        rw [hins, hfee]
        simp only [hfi, if_true]
        cases hc2 : (importName p fi).bind hostChipM2 with
        | some _ => exact ⟨_, rfl⟩
        | none =>
          cases hn : importName p fi with
          | none => rw [hn] at hch; simp at hch
          | some name =>
            rw [hn] at hch
            obtain ⟨y, hy⟩ := hostAnyM2_of_chipM3 (by simpa using hch)
            simp only [hn, Option.bind_some, hy]
            exact ⟨_, rfl⟩
      · exact ⟨r, hr⟩
    · rw [recordAtM3_eq_M2 hins hg hs (fun fi e => by
        subst e; exact Nat.le_of_not_lt (fun hlt => hc ⟨fi, rfl, hlt⟩))] at hr
      exact ⟨r, hr⟩

/-- `mapM` succeeds when `f` does on every element. -/
theorem mapM_isSome {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, ∃ y, f x = some y) → ∃ ys, l.mapM f = some ys := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons a l ih =>
    intro h
    obtain ⟨y, hy⟩ := h a (by simp)
    obtain ⟨ys, hys⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- **`checkM3` succeeding gives `checkM2` succeeding** with the same output except the records and
the fee bound. -/
theorem checkM2_of_M3 {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat}
    {ck : CheckOut} (h : checkM3 cfg p fn off cinfo = some ck) :
    ∃ ck2, checkM2 cfg p fn off cinfo = some ck2 ∧ ck2 = { ck with records := ck2.records, maxFee := ck2.maxFee } := by
  unfold checkM3 at h
  unfold checkM2
  cases hpf : p.funcs[fn]? with
  | none => simp [hpf] at h
  | some pf =>
    simp only [hpf] at h ⊢
    cases hb : basicOk cfg pf with
    | false => simp [hb] at h
    | true =>
      simp only [hb, ite_true] at h ⊢
      cases han : analyzeM2 p pf with
      | none => simp [han] at h
      | some LH =>
        obtain ⟨L, H⟩ := LH
        simp only [han] at h ⊢
        cases hs : structOkM2 p pf L H with
        | false => simp [hs] at h
        | true =>
          simp only [hs, ite_true] at h ⊢
          cases hm : (List.range pf.code.size).mapM (recordAtM3 cfg p pf L H off cinfo) with
          | none => simp [hm] at h
          | some recs =>
            simp only [hm, Option.some.injEq] at h
            subst h
            obtain ⟨hlen, hall⟩ := mapM_some _ _ _ hm
            obtain ⟨recs2, hm2⟩ := mapM_isSome (recordAtM2 cfg p pf L H off cinfo) (List.range pf.code.size)
              (fun x hx => by
                obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
                have := hall i hi
                have hi' : i < recs.length := by rw [hlen]; exact hi
                rw [List.getElem?_eq_getElem hi'] at this
                exact recordAtM2_of_M3 this)
            simp only [hm2]
            exact ⟨_, rfl, rfl⟩

/-! ## 5. The module bridge `checkModuleM3 → checkModuleM2` -/

/-- **A module `checkModuleM3` admits is admitted by `checkModuleM2`** with the same layout and
function table; each function's check output differs only in its records and fee bound. -/
theorem checkModuleM3_M2 {cfg : NearCfg} {p : Prepared} {entry : Nat} {MH : ModOutH}
    (h : checkModuleM3 cfg p entry = some MH) :
    ∃ MH2, checkModuleM2 cfg p entry = some MH2 ∧ MH2.mod.fns = MH.mod.fns ∧ MH2.mod.offs = MH.mod.offs ∧
      MH2.mod.sizes = MH.mod.sizes ∧ MH2.mod.codeSize = MH.mod.codeSize ∧ MH2.mod.funcs = MH.mod.funcs ∧
      MH2.mod.cks.length = MH.mod.cks.length ∧
      ∀ k, MH2.mod.cks.getD k default =
        { MH.mod.cks.getD k default with records := (MH2.mod.cks.getD k default).records,
                                         maxFee := (MH2.mod.cks.getD k default).maxFee } := by
  unfold checkModuleM3 at h
  unfold checkModuleM2
  dsimp only at h ⊢
  split at h
  · simp at h
  · rename_i pfs hp
    rw [hp]
    dsimp only
    split at h
    · simp at h
    · rename_i cks hc
      obtain ⟨hcl1, hcl2⟩ := mapM_some _ _ _ hc
      simp only [List.length_range] at hcl1
      -- each `checkM3` gives a `checkM2`
      have hex : ∀ k ∈ List.range (closureFns p entry).length, ∃ ck2,
          checkM2 cfg p ((closureFns p entry).getD k 0) ((prefixOffs (pfs.map (·.code.size)) 0).getD k 0)
            (callInfo p (closureFns p entry) (prefixOffs (pfs.map (·.code.size)) 0)) = some ck2 := by
        intro k hk
        have hk2 : k < (closureFns p entry).length := List.mem_range.mp hk
        have hk' : k < (List.range (closureFns p entry).length).length := by simpa using hk2
        have := hcl2 k hk'
        simp only [List.getElem_range] at this
        rw [List.getElem?_eq_getElem (by omega)] at this
        obtain ⟨ck2, h2, -⟩ := checkM2_of_M3 this
        exact ⟨ck2, h2⟩
      obtain ⟨cks2, hc2⟩ := mapM_isSome _ _ hex
      rw [hc2]
      dsimp only
      obtain ⟨hcl1', hcl2'⟩ := mapM_some _ _ _ hc2
      simp only [List.length_range] at hcl1'
      -- per-function agreement
      have hag : ∀ k, cks2.getD k default =
          { cks.getD k default with records := (cks2.getD k default).records,
                                    maxFee := (cks2.getD k default).maxFee } := by
        intro k
        by_cases hk : k < (closureFns p entry).length
        · have e3 := hcl2 k (by simpa using hk)
          have e2 := hcl2' k (by simpa using hk)
          simp only [List.getElem_range] at e3 e2
          rw [List.getElem?_eq_getElem (by omega)] at e3 e2
          obtain ⟨ck2, h2, hck2⟩ := checkM2_of_M3 e3
          rw [h2, Option.some.injEq] at e2
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
            List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some, ← e2]
          exact hck2
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
            List.getElem?_eq_none (by omega)]
      have hfr : ∀ k, funcRow ((prefixOffs (pfs.map (·.code.size)) 0).getD k 0) (cks2.getD k default) =
          funcRow ((prefixOffs (pfs.map (·.code.size)) 0).getD k 0) (cks.getD k default) := by
        intro k; rw [hag k]; rfl
      split at h
      · rename_i hcond
        obtain ⟨hhd, htot, hlay, hcl, hent, himp, -⟩ := hcond
        simp only [Option.some.injEq] at h
        subst h
        rw [if_pos ⟨hhd, htot, hlay, hcl, hent, himp⟩]
        refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, by simp only [List.length]; omega, hag⟩
        dsimp only
        exact List.map_congr_left (fun k _ => hfr k)
      · simp at h

/-! ## 6. The M3 context -/

/-- **The static context of an M3 run** (`M2Ctx` with `checkModuleM3`). -/
structure M3Ctx where
  cfg : NearCfg
  p : Prepared
  fn : Nat
  MH : ModOutH
  g0 : Nat
  hM : checkModuleM3 cfg p fn = some MH

namespace M3Ctx
variable (X : M3Ctx)

def M : ModOut := X.MH.mod
def R : Nat := X.cfg.regularOpCost
def nf : Nat := X.M.fns.length
def fnOf (k : Nat) : Nat := X.M.fns.getD k 0
def pfOf (k : Nat) : PFunc := (X.p.funcs[X.fnOf k]?).getD default
def ckOf (k : Nat) : CheckOut := X.M.cks.getD k default
def offOf (k : Nat) : Nat := X.M.offs.getD k 0
def maxFee : Nat := X.M.maxFee
def cinfo : Nat → Option Nat := callInfo X.p X.M.fns X.M.offs

theorem mf : ModFactsM3 X.cfg X.p X.fn X.MH := checkModuleM3_sound X.hM

theorem layout :
    X.M.offs.length = X.nf ∧ X.M.sizes.length = X.nf ∧
    (∀ j, j < X.M.codeSize → (locate X.M.offs X.M.sizes j).1 < X.nf ∧
      (locate X.M.offs X.M.sizes j).2 < X.M.sizes.getD (locate X.M.offs X.M.sizes j).1 0 ∧
      X.M.offs.getD (locate X.M.offs X.M.sizes j).1 0 + (locate X.M.offs X.M.sizes j).2 = j) ∧
    (∀ k, k < X.nf → X.M.offs.getD k 0 + X.M.sizes.getD k 0 ≤ X.M.codeSize ∧
      ∀ l, l < X.M.sizes.getD k 0 → locate X.M.offs X.M.sizes (X.M.offs.getD k 0 + l) = (k, l)) := by
  have h := X.mf.layout
  simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, fun j hj => by have := h3 j hj; exact ⟨this.1.1, this.1.2, this.2⟩,
    fun k hk => ⟨(h4 k hk).1, fun l hl => (h4 k hk).2 l hl⟩⟩

theorem sizeOf {k : Nat} (hk : k < X.nf) : X.M.sizes.getD k 0 = (X.pfOf k).code.size := by
  obtain ⟨pf, h1, h2⟩ := X.mf.pfs k hk
  simp only [pfOf, fnOf, M, h1, Option.getD_some, h2]

/-- The facts of `checkM3` for every checked function. -/
theorem factsOf {k : Nat} (hk : k < X.nf) :
    CheckFactsM3 X.cfg X.p (X.fnOf k) (X.offOf k) X.cinfo (X.pfOf k) (X.ckOf k) := by
  obtain ⟨pf', h⟩ := checkM3_sound (X.mf.cks k hk)
  have : pf' = X.pfOf k := by
    have := h.func; simp only [pfOf, fnOf, M, this, Option.getD_some]
  subst this; exact h

theorem nf_pos : 0 < X.nf := by
  have := X.mf.head
  unfold nf M; cases h : X.MH.mod.fns with
  | nil => rw [h] at this; simp at this
  | cons _ _ => simp

theorem maxFee_ge {k : Nat} (hk : k < X.nf) : (X.ckOf k).maxFee ≤ X.maxFee := by
  have := X.mf.feeLe k 0 hk X.nf_pos; unfold ckOf maxFee M; omega

/-- A global record is a shifted local record of the checked function containing it. -/
theorem recG {j : Nat} (hj : j < X.M.codeSize) :
    ∃ k l, k < X.nf ∧ l < (X.pfOf k).code.size ∧ X.offOf k + l = j ∧
      X.M.records[j]? = some ((X.ckOf k).records[l]?.getD []) := by
  obtain ⟨-, -, h3, -⟩ := X.layout
  obtain ⟨a, b, c⟩ := h3 j hj
  exact ⟨_, _, a, by rw [← X.sizeOf a]; exact b, c, X.mf.recs j hj⟩

/-- Global pcs determine the function and the local pc. -/
theorem loc_unique {k l k' l' : Nat} (hk : k < X.nf) (hl : l < (X.pfOf k).code.size)
    (hk' : k' < X.nf) (hl' : l' < (X.pfOf k').code.size) (h : X.offOf k + l = X.offOf k' + l') :
    k = k' ∧ l = l' := by
  obtain ⟨-, -, -, h4⟩ := X.layout
  have e1 := (h4 k hk).2 l (by rw [X.sizeOf hk]; exact hl)
  have e2 := (h4 k' hk').2 l' (by rw [X.sizeOf hk']; exact hl')
  unfold offOf at h
  rw [h, e2] at e1
  simp only [Prod.mk.injEq] at e1
  exact ⟨e1.1.symm, e1.2.symm⟩

theorem off_bound {k : Nat} (hk : k < X.nf) : X.offOf k + (X.pfOf k).code.size ≤ X.M.codeSize := by
  obtain ⟨-, -, -, h4⟩ := X.layout
  have := (h4 k hk).1; rw [X.sizeOf hk] at this; exact this

/-- The record of a local pc (`checkM3`'s `recordAtM3`). -/
theorem rec_at {k pc : Nat} (hk : k < X.nf) (hpc : pc < (X.pfOf k).code.size) :
    recordAtM3 X.cfg X.p (X.pfOf k) (X.ckOf k).labels (X.ckOf k).heights (X.offOf k) X.cinfo pc =
      (X.ckOf k).records[pc]? := (X.factsOf hk).recs pc hpc

/-- Every global record's fee is within the module fee bound. -/
theorem rec_fee_le {j : Nat} (hj : j < X.M.codeSize) : (X.M.records[j]?.getD []).getD 3 0 ≤ X.maxFee := by
  obtain ⟨k, l, hk, hl, -, hrj⟩ := X.recG hj
  rw [hrj, Option.getD_some]
  exact Nat.le_trans ((X.factsOf hk).feeLe l hl) (X.maxFee_ge hk)

end M3Ctx

/-! ## 7. `checkM3` gives the generalised facts (`CheckFacts3`, `ModFacts3`, `Ctx3`) -/

/-- An M2 addition's M2 record carries an M2 opcode (the `special` argument of `checkM2_facts`). -/
theorem recordAtM2_special {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)} {H : Array Nat}
    {off pc : Nat} {cinfo : Nat → Option Nat} {ins : Instr} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) (hins : pf.code[pc]? = some ins)
    (hs : m2Special p ins = true) :
    ∃ op rest, rec = (off + pc) :: op :: rest ∧ m2OpNat op = true ∧ (op = Chips.Ctrl.opJump → ins = .else_) := by
  unfold recordAtM2 at hr
  rw [hins] at hr
  cases hfee : feeUnits cfg pf.gas[pc]? <;> rw [hfee] at hr <;>
    cases ins <;> simp only [m2Special, reduceCtorEq, Bool.false_eq_true] at hs <;> simp only at hr
  all_goals (repeat' split at hr)
  all_goals first
    | (simp at hr; done)
    | (simp only [Option.some.injEq] at hr; rw [← hr]
       refine ⟨_, _, rfl, ?_, ?_⟩
       · simp only [m2OpNat, opMemGrowX, opMemSizeX, opUnreach, opHostX, Chips.opHost, Chips.IfC.opIf,
           Chips.Ctrl.opJump]
         decide
       · first
         | (intro _; rfl)
         | (intro h; simp [opMemGrowX, opMemSizeX, opUnreach, opHostX, Chips.opHost, Chips.IfC.opIf,
             Chips.Ctrl.opJump] at h))
    | (exfalso; simp_all [isConvOp]; done)
    | (simp only [Option.some.injEq] at hr; rw [← hr]
       refine ⟨_, _, rfl, ?_, ?_⟩
       · simp only [m2OpNat, Bool.or_eq_true, beq_iff_eq] at hs ⊢; omega
       · simp only [Bool.or_eq_true, beq_iff_eq] at hs; simp only [Chips.Ctrl.opJump]; omega)
  all_goals done

/-- An M2 addition's M3 record carries an M3 opcode. -/
theorem recordAtM3_special {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)} {H : Array Nat}
    {off pc : Nat} {cinfo : Nat → Option Nat} {ins : Instr} {rec : List Nat}
    (hr : recordAtM3 cfg p pf L H off cinfo pc = some rec) (hins : pf.code[pc]? = some ins)
    (hs : m2Special p ins = true) :
    ∃ op rest, rec = (off + pc) :: op :: rest ∧ m3OpNat op = true ∧ (op = Chips.Ctrl.opJump → ins = .else_) := by
  have hm2 : ∀ r, recordAtM2 cfg p pf L H off cinfo pc = some r → rec = r →
      ∃ op rest, rec = (off + pc) :: op :: rest ∧ m3OpNat op = true ∧ (op = Chips.Ctrl.opJump → ins = .else_) := by
    intro r h2 e
    subst e
    obtain ⟨op, rest, a, b, c⟩ := recordAtM2_special h2 hins hs
    exact ⟨op, rest, a, m3OpNat_of_m2 b, c⟩
  unfold recordAtM3 at hr
  rw [hins] at hr
  cases ins with
  | memGrow =>
    cases hg : growFee cfg pf.gas[pc]? with
    | none => simp [hg] at hr
    | some fl =>
      simp only [hg, Option.map_some, Option.some.injEq] at hr
      subst hr
      exact ⟨_, _, rfl, by simp [m3OpNat], by simp [Chips.opMemGrow, Chips.Ctrl.opJump]⟩
  | memSize =>
    cases hf : feeUnits cfg pf.gas[pc]? with
    | none => simp [hf] at hr
    | some fee =>
      simp only [hf, Option.map_some, Option.some.injEq] at hr
      subst hr
      exact ⟨_, _, rfl, by simp [m3OpNat], by simp [Chips.opMemSize, Chips.Ctrl.opJump]⟩
  | call fi =>
    simp only at hr
    split at hr
    · split at hr
      · simp only [Option.some.injEq] at hr
        subst hr
        exact ⟨_, _, rfl, by simp [m3OpNat, m2OpNat, Chips.opHost], by simp [Chips.opHost, Chips.Ctrl.opJump]⟩
      · exact hm2 rec hr rfl
    · exact hm2 rec hr rfl
  | _ => exact hm2 rec hr rfl

/-- At a pc that is not an M2 addition, `recordAtM3` is `recordAtM2`. -/
theorem recordAtM3_base {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)} {H : Array Nat}
    {off pc : Nat} {cinfo : Nat → Option Nat} {ins : Instr} (hins : pf.code[pc]? = some ins)
    (hns : m2Special p ins = false) :
    recordAtM3 cfg p pf L H off cinfo pc = recordAtM2 cfg p pf L H off cinfo pc := by
  refine recordAtM3_eq_M2 hins ?_ ?_ ?_
  · rintro rfl; simp [m2Special] at hns
  · rintro rfl; simp [m2Special] at hns
  · rintro fi rfl; simp only [m2Special, decide_eq_false_iff_not] at hns; omega

/-- `CheckFacts3` from its parts (`CheckFacts.of_parts` with `m3OpNat`). -/
theorem CheckFacts3.of_parts {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat}
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
      ∃ op rest, ck.records[pc]? = some ((off + pc) :: op :: rest) ∧ m3OpNat op = true ∧
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
    CheckFacts3 cfg p fn off cinfo pf ck := by
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

/-- **`checkM3` gives the generalised `CheckFacts3`.** -/
theorem checkM3_facts {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat}
    {ck : CheckOut} (h : checkM3 cfg p fn off cinfo = some ck) :
    ∃ pf, CheckFacts3 cfg p fn off cinfo pf ck := by
  obtain ⟨pf, F⟩ := checkM3_sound h
  have hrec : ∀ pc, pc < pf.code.size → ∀ ins, pf.code[pc]? = some ins → m2Special p ins = false →
      recordAtM2 cfg p pf ck.labels ck.heights off cinfo pc = ck.records[pc]? := by
    intro pc hpc ins hins hns
    rw [← recordAtM3_base hins hns]; exact F.recs pc hpc
  refine ⟨pf, CheckFacts3.of_parts F.func F.basic F.lsize F.hsize F.l0 F.h0 ?_ F.hBound F.records ?_
    ?_ ?_ F.arity F.resTag F.localTags F.np F.nl F.charge F.prologue⟩
  · intro pc hpc ins hins hns
    rw [← verifyAtM2_base hins hns]; exact F.verify pc hpc
  · intro pc hpc
    obtain ⟨ins, hins⟩ : ∃ ins, pf.code[pc]? = some ins := ⟨pf.code[pc], Array.getElem?_eq_getElem hpc⟩
    refine ⟨ins, hins, fun hns => ?_⟩
    have hr := hrec pc hpc ins hins hns
    have hsz : pc < ck.records.size := by rw [F.records]; exact hpc
    rw [Array.getElem?_eq_getElem hsz] at hr
    cases hfee : feeUnits cfg pf.gas[pc]? with
    | none =>
      exfalso
      unfold recordAtM2 at hr
      rw [hins, hfee] at hr
      cases ins <;> simp_all [m2Special]
    | some fee =>
      rw [recordAtM2_base hins hns hfee] at hr
      refine ⟨fee, rfl, ?_, by rw [hr, Array.getElem?_eq_getElem hsz]⟩
      have := F.feeLe pc hpc
      rw [Array.getElem?_eq_getElem hsz, Option.getD_some, recordOf_fee hr] at this
      exact this
  · intro pc hpc ins hins hs
    have hr := F.recs pc hpc
    have hsz : pc < ck.records.size := by rw [F.records]; exact hpc
    rw [Array.getElem?_eq_getElem hsz] at hr ⊢
    obtain ⟨op, rest, e, h1, h2⟩ := recordAtM3_special hr hins hs
    exact ⟨op, rest, by rw [e], h1, h2⟩
  · intro pc hpc hins
    have hv := F.verify pc hpc
    have hr := F.recs pc hpc
    rw [recordAtM3_eq_M2 hins (by simp) (by simp) (by simp)] at hr
    have hfl := F.feeLe pc hpc
    obtain ⟨ls, h, hl, hh⟩ := F.lh hpc
    simp only [verifyAtM2, hins, hl, hh] at hv
    cases ls with
    | nil => simp at hv
    | cons lab rest =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hv
      cases hfee : feeUnits cfg pf.gas[pc]? with
      | none =>
        exfalso
        have hsz : pc < ck.records.size := by rw [F.records]; exact hpc
        rw [Array.getElem?_eq_getElem hsz] at hr
        unfold recordAtM2 at hr; rw [hins, hfee] at hr; simp at hr
      | some fee =>
        unfold recordAtM2 at hr; rw [hins, hfee] at hr; simp only [hl] at hr
        rw [← hr] at hfl
        simp only [Option.getD_some, List.getD_cons_succ, List.getD_cons_zero] at hfl
        refine ⟨lab, rest, fee, hl, by rw [hh]; exact h1, h2, h3, by rw [hh]; exact h4, rfl, hfl, ?_⟩
        rw [← hr, hh]

/-- **`checkModuleM3` gives the generalised `ModFacts3`.** -/
theorem checkModuleM3_modFacts3 {cfg : NearCfg} {p : Prepared} {entry : Nat} {MH : ModOutH}
    (h : checkModuleM3 cfg p entry = some MH) : ModFacts3 cfg p entry MH.mod := by
  have F := checkModuleM3_sound h
  exact ⟨F.head, fun k hk => checkM3_facts (F.cks k hk), F.pfs, F.total, F.layout, F.recSize, F.recs,
    F.feeLe, F.closed, F.offs0, F.entryParams, F.funcs, F.funcsLen⟩

/-- **The M3 context as a `Ctx3`.** -/
def M3Ctx.toCtx3 (X : M3Ctx) : Ctx3 := ⟨X.cfg, X.p, X.fn, X.MH.mod, X.g0, checkModuleM3_modFacts3 X.hM⟩

/-! ## 8. The M2 shadow of an M3 context -/

namespace M3Ctx
variable (X : M3Ctx)

theorem m2_isSome : (checkModuleM2 X.cfg X.p X.fn).isSome := by
  obtain ⟨MH2, h, -⟩ := checkModuleM3_M2 X.hM
  rw [h]; rfl

/-- The `checkModuleM2` output of the same module. -/
def MH2 : ModOutH := (checkModuleM2 X.cfg X.p X.fn).get X.m2_isSome

theorem MH2_eq : checkModuleM2 X.cfg X.p X.fn = some X.MH2 := by
  unfold MH2; exact (Option.some_get _).symm

/-- **The M2 shadow**: the M2 context of the same module, entry, config and budget. -/
def toM2 : M2Ctx := ⟨X.cfg, X.p, X.fn, X.MH2, X.g0, X.MH2_eq⟩

theorem toM2_agree :
    X.MH2.mod.fns = X.M.fns ∧ X.MH2.mod.offs = X.M.offs ∧ X.MH2.mod.sizes = X.M.sizes ∧
      X.MH2.mod.codeSize = X.M.codeSize ∧ X.MH2.mod.funcs = X.M.funcs ∧
      ∀ k, X.MH2.mod.cks.getD k default =
        { X.ckOf k with records := (X.MH2.mod.cks.getD k default).records,
                        maxFee := (X.MH2.mod.cks.getD k default).maxFee } := by
  obtain ⟨MH2, h, h1, h2, h3, h4, h5, -, h7⟩ := checkModuleM3_M2 X.hM
  have : MH2 = X.MH2 := by have := X.MH2_eq; rw [h] at this; exact Option.some.inj this
  subst this
  exact ⟨h1, h2, h3, h4, h5, h7⟩

@[simp] theorem toM2_cfg : X.toM2.cfg = X.cfg := rfl
@[simp] theorem toM2_p : X.toM2.p = X.p := rfl
@[simp] theorem toM2_fn : X.toM2.fn = X.fn := rfl
@[simp] theorem toM2_g0 : X.toM2.g0 = X.g0 := rfl
theorem toM2_R : X.toM2.R = X.R := rfl
theorem toM2_MH : X.toM2.MH = X.MH2 := rfl
theorem toM2_nf : X.toM2.nf = X.nf := by
  unfold M2Ctx.nf M2Ctx.M nf M; rw [toM2_MH, X.toM2_agree.1]; rfl
theorem toM2_fnOf (k : Nat) : X.toM2.fnOf k = X.fnOf k := by
  unfold M2Ctx.fnOf M2Ctx.M fnOf M; rw [toM2_MH, X.toM2_agree.1]; rfl
theorem toM2_pfOf (k : Nat) : X.toM2.pfOf k = X.pfOf k := by
  unfold M2Ctx.pfOf pfOf; rw [toM2_fnOf]; rfl
theorem toM2_offOf (k : Nat) : X.toM2.offOf k = X.offOf k := by
  unfold M2Ctx.offOf M2Ctx.M offOf M; rw [toM2_MH, X.toM2_agree.2.1]; rfl
theorem toM2_codeSize : X.toM2.M.codeSize = X.M.codeSize := X.toM2_agree.2.2.2.1
theorem toM2_funcs : X.toM2.M.funcs = X.M.funcs := X.toM2_agree.2.2.2.2.1
theorem toM2_cinfo : X.toM2.cinfo = X.cinfo := by
  unfold M2Ctx.cinfo cinfo M2Ctx.M M; rw [toM2_MH, X.toM2_agree.1, X.toM2_agree.2.1]; rfl
theorem toM2_ck (k : Nat) : (X.toM2.ckOf k).labels = (X.ckOf k).labels ∧
    (X.toM2.ckOf k).heights = (X.ckOf k).heights ∧ (X.toM2.ckOf k).arity = (X.ckOf k).arity ∧
    (X.toM2.ckOf k).resTag = (X.ckOf k).resTag ∧ (X.toM2.ckOf k).localTags = (X.ckOf k).localTags ∧
    (X.toM2.ckOf k).np = (X.ckOf k).np ∧ (X.toM2.ckOf k).nl = (X.ckOf k).nl ∧
    (X.toM2.ckOf k).charge = (X.ckOf k).charge ∧ (X.toM2.ckOf k).prologue = (X.ckOf k).prologue := by
  have e := X.toM2_agree.2.2.2.2.2 k
  unfold M2Ctx.ckOf M2Ctx.M
  rw [toM2_MH, e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Records of the shadow**: away from `memory.grow`, `memory.size` and import calls, the M2 shadow
has the M3 record. -/
theorem toM2_rec {k pc : Nat} (hk : k < X.nf) (hpc : pc < (X.pfOf k).code.size) {ins : Instr}
    (hins : (X.pfOf k).code[pc]? = some ins) (hg : ins ≠ .memGrow) (hs : ins ≠ .memSize)
    (hc : ∀ fi, ins = .call fi → X.p.m.imports.size ≤ fi) :
    (X.toM2.ckOf k).records[pc]? = (X.ckOf k).records[pc]? := by
  have h2 := X.toM2.rec_at (k := k) (pc := pc) (by rw [toM2_nf]; exact hk) (by rw [toM2_pfOf]; exact hpc)
  have h3 := X.rec_at hk hpc
  obtain ⟨e1, e2, -⟩ := X.toM2_ck k
  rw [← h2, ← h3, toM2_pfOf, toM2_offOf, e1, e2, toM2_cinfo, toM2_cfg, toM2_p, recordAtM3_eq_M2 hins hg hs hc]

/-! ## 9. MEMG code facts at module level -/

/-- **A global record with opcode `0x40` is the record of `memory.grow`** at its location, with
`growFee`'s fee units and linear flag and the static height. -/
theorem recG_memGrow {j : Nat} (hj : j < X.M.codeSize) (hop : (X.M.records[j]?.getD []).getD 1 0 = Chips.opMemGrow) :
    ∃ k l fee lin, k < X.nf ∧ l < (X.pfOf k).code.size ∧ X.offOf k + l = j ∧
      (X.pfOf k).code[l]? = some .memGrow ∧ growFee X.cfg (X.pfOf k).gas[l]? = some (fee, lin) ∧
      X.M.records[j]? = some [X.offOf k + l, Chips.opMemGrow, (X.ckOf k).heights[l]?.getD 0, fee, lin, 0, 0, 0] := by
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hr := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hr hrj
  rw [hrj, Option.getD_some] at hop
  obtain ⟨fee, lin, hc, hg, hrec⟩ := recordAtM3_memGrow_op hr hop
  exact ⟨k, l, fee, lin, hk, hl, hoff, hc, hg, by rw [hrj, hrec]; rfl⟩

/-- **A global record with opcode `0x3F` is the record of `memory.size`.** -/
theorem recG_memSize {j : Nat} (hj : j < X.M.codeSize) (hop : (X.M.records[j]?.getD []).getD 1 0 = Chips.opMemSize) :
    ∃ k l fee, k < X.nf ∧ l < (X.pfOf k).code.size ∧ X.offOf k + l = j ∧
      (X.pfOf k).code[l]? = some .memSize ∧ feeUnits X.cfg (X.pfOf k).gas[l]? = some fee ∧
      X.M.records[j]? = some [X.offOf k + l, Chips.opMemSize, (X.ckOf k).heights[l]?.getD 0, fee, 0, 0, 0, 0] := by
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hr := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hr hrj
  rw [hrj, Option.getD_some] at hop
  obtain ⟨fee, hc, hf, hrec⟩ := recordAtM3_memSize_op hr hop
  exact ⟨k, l, fee, hk, hl, hoff, hc, hf, by rw [hrj, hrec]; rfl⟩

/-- **The successor of a `memory.grow` pc**: `1 ≤ h`, `pc + 1` in the code, same labels and height. -/
theorem memGrow_succ {k pc : Nat} (hk : k < X.nf) (hc : (X.pfOf k).code[pc]? = some .memGrow)
    {ls : List Label} {h : Nat} (hL : (X.ckOf k).labels[pc]? = some ls) (hH : (X.ckOf k).heights[pc]? = some h) :
    1 ≤ h ∧ pc + 1 < (X.pfOf k).code.size ∧ (X.ckOf k).labels[pc + 1]? = some ls ∧
      (X.ckOf k).heights[pc + 1]? = some h := by
  have hpc : pc < (X.pfOf k).code.size := by
    rcases Nat.lt_or_ge pc (X.pfOf k).code.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hc; simp at hc
  exact verifyAtM2_memGrow ((X.factsOf hk).verify pc hpc) hc hL hH

/-- **The successor of a `memory.size` pc**: same labels, height `h + 1`. -/
theorem memSize_succ {k pc : Nat} (hk : k < X.nf) (hc : (X.pfOf k).code[pc]? = some .memSize)
    {ls : List Label} {h : Nat} (hL : (X.ckOf k).labels[pc]? = some ls) (hH : (X.ckOf k).heights[pc]? = some h) :
    pc + 1 < (X.pfOf k).code.size ∧ (X.ckOf k).labels[pc + 1]? = some ls ∧
      (X.ckOf k).heights[pc + 1]? = some (h + 1) := by
  have hpc : pc < (X.pfOf k).code.size := by
    rcases Nat.lt_or_ge pc (X.pfOf k).code.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hc; simp at hc
  exact verifyAtM2_memSize ((X.factsOf hk).verify pc hpc) hc hL hH

end M3Ctx

/-! ## Axiom guards -/

#print axioms m3OpNat_of_m2
#print axioms CheckFacts.to3
#print axioms ModFacts.to3
#print axioms checkM3_sound
#print axioms checkModuleM3_sound
#print axioms recordAtM3_eq_M2
#print axioms recordAtM2_of_M3
#print axioms checkM2_of_M3
#print axioms checkModuleM3_M2
#print axioms recordAtM2_special
#print axioms recordAtM3_special
#print axioms CheckFacts3.of_parts
#print axioms checkM3_facts
#print axioms checkModuleM3_modFacts3
#print axioms M3Ctx.toM2_agree
#print axioms M3Ctx.toM2_rec
#print axioms M3Ctx.recG_memGrow
#print axioms M3Ctx.recG_memSize
#print axioms M3Ctx.memGrow_succ
#print axioms M3Ctx.memSize_succ

end WasmBase
