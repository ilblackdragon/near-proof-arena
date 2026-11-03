import WasmBase.M2Check
import WasmBase.SpecLemmas
/-!
# WasmBase.M2Ctx — the static context of an M2 run, from `checkModuleM2 = some _`

The base soundness stack's `Ctx` (`WasmBase/Event.lean`) carries `hM : checkModule cfg p fn = some M`,
and every code fact it uses (`CheckFacts`, `ModFacts`) is derived from that.  `checkModule` rejects
every module that contains an M2 instruction (`kindOf` has no arm for the conversions, `unreachable`,
`else`, `if`, or an import call), so **no `Ctx` exists for an M2 module**: a theorem quantified over
`X : Ctx` says nothing about a module that `checkModuleM2` admits but `checkModule` does not.

This file is the M2 counterpart: `M2Ctx` carries `hM : checkModuleM2 cfg p fn = some MH`, and every
code fact below is **derived** from that equation (no fact is assumed):

* `checkM2_sound` / `CheckFactsM2`: per-function facts of `checkM2` (the function, the static
  label/height arrays, `verifyAtM2` at every pc, the records are `recordAtM2`, the fee bound);
* `checkModuleM2_sound` / `ModFactsM2`: module facts (layout, global records, fee bound, closure,
  imports listed);
* `M2Ctx.factsOf`, `M2Ctx.recG`, `M2Ctx.loc_unique`, … — the same accessors the base `Ctx` has;
* **successor facts** at the M2 pcs, exactly in the form the step lemmas consume:
  * `M2Ctx.conv_succ` (conversions: `1 ≤ h`, `pc + 1` in the code, same labels, same height — the
    hypotheses `hnext`/`hL1`/`hH1`/`hstk` of `Main/M2Link.lean:step_conv`);
  * `M2Ctx.ifres_succ` (`if` with a result: both successors carry the pushed label at `h − 1`);
  * `M2Ctx.else_succ` (`else`: `h = label.height + arity` and the label target's facts);
  * `M2Ctx.conv_record`, `M2Ctx.unreach_record` (the code record of the pc);
* **the FETCH converse**: `recordAtM2_conv_op` / `recordAtM2_unreach_op` — a record of an M2-checked
  function whose opcode is `0xA7`/`0xAC`/`0xAD` (resp. `0x00`) is the record of exactly that
  conversion (resp. of `unreachable`), so a CONV (UNREACH) row's FETCH answer pins its instruction.
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-! ## Per-function facts of `checkM2` -/

/-- Everything a successful `checkM2` gives about one function. -/
structure CheckFactsM2 (cfg : NearCfg) (p : Prepared) (fn off : Nat) (cinfo : Nat → Option Nat)
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
  recs : ∀ pc, pc < pf.code.size → recordAtM2 cfg p pf ck.labels ck.heights off cinfo pc = ck.records[pc]?
  feeLe : ∀ pc, pc < pf.code.size → (ck.records[pc]?.getD []).getD 3 0 ≤ ck.maxFee
  arity : ck.arity = pf.type.results.size
  resTag : ck.resTag = if pf.type.results[0]? == some .i64 then 1 else 0
  localTags : ck.localTags = (pf.type.params.toList ++ pf.locals.toList).map vtTag
  np : ck.np = pf.type.params.size
  nl : ck.nl = pf.type.params.size + pf.locals.size
  charge : ck.charge = pf.stackCharge
  prologue : ck.prologue = pf.prologueGas / cfg.regularOpCost

theorem checkM2_sound {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat}
    {ck : CheckOut} (h : checkM2 cfg p fn off cinfo = some ck) :
    ∃ pf, CheckFactsM2 cfg p fn off cinfo pf ck := by
  unfold checkM2 at h
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
          cases hm : (List.range pf.code.size).mapM (recordAtM2 cfg p pf L H off cinfo) with
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

/-! ## Module facts of `checkModuleM2` -/

/-- What a successful `checkModuleM2` gives (all from its decidable checks and `checkM2`). -/
structure ModFactsM2 (cfg : NearCfg) (p : Prepared) (entry : Nat) (MH : ModOutH) : Prop where
  head : MH.mod.fns.head? = some entry
  cks : ∀ k, k < MH.mod.fns.length →
    checkM2 cfg p (MH.mod.fns.getD k 0) (MH.mod.offs.getD k 0) (callInfo p MH.mod.fns MH.mod.offs) =
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
  hostRows : MH.hostRows = hostFnsM2.map fun x => Chips.hostRow x.1 x.2.2.1 x.2.2.2

theorem checkModuleM2_sound {cfg : NearCfg} {p : Prepared} {entry : Nat} {MH : ModOutH}
    (h : checkModuleM2 cfg p entry = some MH) : ModFactsM2 cfg p entry MH := by
  unfold checkModuleM2 at h
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
        obtain ⟨hhd, htot, hlay, hcl, hent, himp⟩ := hcond
        obtain ⟨hcl1, hcl2⟩ := mapM_some _ _ _ hc
        obtain ⟨hpl1, hpl2⟩ := mapM_some _ _ _ hp
        simp only [List.length_range] at hcl1
        refine ⟨hhd, ?_, ?_, htot, hlay, by simp, ?_, ?_, hcl, ?_, ?_, himp, ?_, by simp, rfl⟩
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

/-! ## The M2 context -/

/-- **The static context of an M2 run**: the prepared module, the entry function, its config and
initial budget, and the module-level M2 check.  The only proof field is `hM`; every code fact is
derived from it. -/
structure M2Ctx where
  cfg : NearCfg
  p : Prepared
  fn : Nat
  MH : ModOutH
  g0 : Nat
  hM : checkModuleM2 cfg p fn = some MH

namespace M2Ctx
variable (X : M2Ctx)

def M : ModOut := X.MH.mod
def R : Nat := X.cfg.regularOpCost
def nf : Nat := X.M.fns.length
def fnOf (k : Nat) : Nat := X.M.fns.getD k 0
def pfOf (k : Nat) : PFunc := (X.p.funcs[X.fnOf k]?).getD default
def ckOf (k : Nat) : CheckOut := X.M.cks.getD k default
def offOf (k : Nat) : Nat := X.M.offs.getD k 0
def maxFee : Nat := X.M.maxFee
def cinfo : Nat → Option Nat := callInfo X.p X.M.fns X.M.offs

theorem mf : ModFactsM2 X.cfg X.p X.fn X.MH := checkModuleM2_sound X.hM

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

/-- The facts of `checkM2` for every checked function. -/
theorem factsOf {k : Nat} (hk : k < X.nf) :
    CheckFactsM2 X.cfg X.p (X.fnOf k) (X.offOf k) X.cinfo (X.pfOf k) (X.ckOf k) := by
  obtain ⟨pf', h⟩ := checkM2_sound (X.mf.cks k hk)
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

/-- The record of a local pc, with its instruction and fee (`checkM2`'s `recordAtM2`). -/
theorem rec_at {k pc : Nat} (hk : k < X.nf) (hpc : pc < (X.pfOf k).code.size) :
    recordAtM2 X.cfg X.p (X.pfOf k) (X.ckOf k).labels (X.ckOf k).heights (X.offOf k) X.cinfo pc =
      (X.ckOf k).records[pc]? := (X.factsOf hk).recs pc hpc

end M2Ctx

/-! ## Successor facts at the M2 pcs -/

/-- The labels/heights at `pc` exist (sizes match the code). -/
theorem CheckFactsM2.lh {cfg : NearCfg} {p : Prepared} {fn off : Nat} {cinfo : Nat → Option Nat}
    {pf : PFunc} {ck : CheckOut} (F : CheckFactsM2 cfg p fn off cinfo pf ck) {pc : Nat}
    (hpc : pc < pf.code.size) :
    ∃ ls h, ck.labels[pc]? = some ls ∧ ck.heights[pc]? = some h := by
  refine ⟨ck.labels[pc]'(by rw [F.lsize]; exact hpc), ck.heights[pc]'(by rw [F.hsize]; exact hpc),
    Array.getElem?_eq_getElem _, Array.getElem?_eq_getElem _⟩

/-- **Conversions (checker side).**  At a conversion pc the stack is non-empty, the next pc is in
the code and carries the same labels and the same height.  These are exactly the successor
hypotheses of `Main/M2Link.lean:step_conv`, here derived from `verifyAtM2`. -/
theorem M2Ctx.conv_succ (X : M2Ctx) {k pc op : Nat} (hk : k < X.nf)
    (hins : (X.pfOf k).code[pc]? = some (.num op)) (hop : isConvOp op = true)
    {ls : List Label} {h : Nat} (hls : (X.ckOf k).labels[pc]? = some ls)
    (hh : (X.ckOf k).heights[pc]? = some h) :
    1 ≤ h ∧ pc + 1 < (X.pfOf k).code.size ∧ (X.ckOf k).labels[pc + 1]? = some ls ∧
      (X.ckOf k).heights[pc + 1]? = some h := by
  have hpc : pc < (X.pfOf k).code.size := by
    rcases Nat.lt_or_ge pc (X.pfOf k).code.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hins; simp at hins
  have hv := (X.factsOf hk).verify pc hpc
  simp only [verifyAtM2, hins, hls, hh, hop, ite_true, Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨hv.1, hv.2.1.1, hv.2.1.2, hv.2.2⟩

/-- **`if` (checker side).**  At an `if` pc the static step `ifStepM2` succeeds, and both successors
(`pc + 1` and the false target) are in the code with the labels/heights it computes. -/
theorem M2Ctx.if_succ (X : M2Ctx) {k pc : Nat} {bt : BT} (hk : k < X.nf)
    (hins : (X.pfOf k).code[pc]? = some (.if_ bt))
    {ls : List Label} {h : Nat} (hls : (X.ckOf k).labels[pc]? = some ls)
    (hh : (X.ckOf k).heights[pc]? = some h) :
    ∃ lsT hT ftgt lsF hF, ifStepM2 (X.pfOf k) ls h pc bt = some (lsT, hT, ftgt, lsF, hF) ∧
      pc + 1 < (X.pfOf k).code.size ∧ (X.ckOf k).labels[pc + 1]? = some lsT ∧
      (X.ckOf k).heights[pc + 1]? = some hT ∧
      ftgt < (X.pfOf k).code.size ∧ (X.ckOf k).labels[ftgt]? = some lsF ∧
      (X.ckOf k).heights[ftgt]? = some hF := by
  have hpc : pc < (X.pfOf k).code.size := by
    rcases Nat.lt_or_ge pc (X.pfOf k).code.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hins; simp at hins
  have hv := (X.factsOf hk).verify pc hpc
  simp only [verifyAtM2, hins, hls, hh] at hv
  revert hv
  cases hs : ifStepM2 (X.pfOf k) ls h pc bt with
  | none => simp
  | some r =>
    obtain ⟨lsT, hT, ftgt, lsF, hF⟩ := r
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨⟨⟨a1, a2⟩, a3⟩, ⟨⟨b1, b2⟩, b3⟩⟩
    exact ⟨lsT, hT, ftgt, lsF, hF, rfl, a1, a2, a3, b1, b2, b3⟩

/-- **`if` with a result (checker side).**  Both successors carry the pushed label
`mkIfLabel bt e (h − 1)` and height `h − 1`, the `if` has an `else` (`el ≠ e`), and the true arm
starts at `pc + 1`, the false arm at `el + 1`. -/
theorem M2Ctx.ifres_succ (X : M2Ctx) {k pc : Nat} {bt : BT} (hk : k < X.nf)
    (hins : (X.pfOf k).code[pc]? = some (.if_ bt)) (hr : (btResults bt).size = 1)
    {ls : List Label} {h : Nat} (hls : (X.ckOf k).labels[pc]? = some ls)
    (hh : (X.ckOf k).heights[pc]? = some h) :
    ∃ e el, (X.pfOf k).endOf[pc]? = some e ∧ (X.pfOf k).elseOf[pc]? = some el ∧ el ≠ e ∧ 1 ≤ h ∧
      pc + 1 < (X.pfOf k).code.size ∧
      (X.ckOf k).labels[pc + 1]? = some (mkIfLabel bt e (h - 1) :: ls) ∧
      (X.ckOf k).heights[pc + 1]? = some (h - 1) ∧
      el + 1 < (X.pfOf k).code.size ∧
      (X.ckOf k).labels[el + 1]? = some (mkIfLabel bt e (h - 1) :: ls) ∧
      (X.ckOf k).heights[el + 1]? = some (h - 1) := by
  obtain ⟨lsT, hT, ftgt, lsF, hF, hs, a1, a2, a3, b1, b2, b3⟩ := X.if_succ hk hins hls hh
  have hs' := hs
  unfold ifStepM2 at hs'
  rw [hr] at hs'
  simp only [Nat.le_refl, ite_true] at hs'
  revert hs'
  cases he : (X.pfOf k).endOf[pc]? with
  | none => simp
  | some e =>
    cases hel : (X.pfOf k).elseOf[pc]? with
    | none => simp
    | some el =>
      intro hs'
      simp only at hs'
      split at hs'
      · rename_i hc
        obtain ⟨hne, eF, eT, ehT, ehF⟩ := ifStepM2_result_else he hel hr hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs'
        obtain ⟨-, -, hft, -, -⟩ := hs'
        subst hft
        rw [eT, eF] at a2
        rw [eF] at b2
        rw [ehT] at a3
        rw [ehF] at b3
        exact ⟨e, el, rfl, rfl, hne, hc.1, a1, a2, a3, b1, b2, b3⟩
      · simp at hs'

/-- **`else` (checker side).**  At an `else` pc the true arm ends at exactly `label.height + arity`
(no discard) and the label target carries the outer labels at that height. -/
theorem M2Ctx.else_succ (X : M2Ctx) {k pc : Nat} (hk : k < X.nf)
    (hins : (X.pfOf k).code[pc]? = some .else_)
    {ls : List Label} {h : Nat} (hls : (X.ckOf k).labels[pc]? = some ls)
    (hh : (X.ckOf k).heights[pc]? = some h) :
    ∃ lab rest, ls = lab :: rest ∧ h = lab.height + lab.arity ∧ lab.target < (X.pfOf k).code.size ∧
      (X.ckOf k).labels[lab.target]? = some rest ∧ (X.ckOf k).heights[lab.target]? = some h := by
  have hpc : pc < (X.pfOf k).code.size := by
    rcases Nat.lt_or_ge pc (X.pfOf k).code.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hins; simp at hins
  have hv := (X.factsOf hk).verify pc hpc
  simp only [verifyAtM2, hins, hls, hh] at hv
  revert hv
  cases ls with
  | nil => simp
  | cons lab rest =>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    exact ⟨lab, rest, rfl, h1, h2, h3, h4⟩

/-! ## Records of the M2 pcs and the FETCH converse -/

/-- The record of a conversion pc: `[off + pc, op, h, fee, 0, 0, 0, 0]`. -/
theorem M2Ctx.conv_record (X : M2Ctx) {k pc op : Nat} (hk : k < X.nf)
    (hins : (X.pfOf k).code[pc]? = some (.num op)) (hop : isConvOp op = true)
    {fee : Nat} (hfee : feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee) :
    (X.ckOf k).records[pc]? =
      some [X.offOf k + pc, op, (X.ckOf k).heights[pc]?.getD 0, fee, 0, 0, 0, 0] := by
  have hpc : pc < (X.pfOf k).code.size := by
    rcases Nat.lt_or_ge pc (X.pfOf k).code.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hins; simp at hins
  rw [← X.rec_at hk hpc]
  simp only [recordAtM2, hins, hfee, hop, ite_true]

/-- The record of an `unreachable` pc: `[off + pc, 0, h, fee, 0, 0, 0, 0]`. -/
theorem M2Ctx.unreach_record (X : M2Ctx) {k pc : Nat} (hk : k < X.nf)
    (hins : (X.pfOf k).code[pc]? = some .unreachable)
    {fee : Nat} (hfee : feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee) :
    (X.ckOf k).records[pc]? =
      some [X.offOf k + pc, opUnreach, (X.ckOf k).heights[pc]?.getD 0, fee, 0, 0, 0, 0] := by
  have hpc : pc < (X.pfOf k).code.size := by
    rcases Nat.lt_or_ge pc (X.pfOf k).code.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hins; simp at hins
  rw [← X.rec_at hk hpc]
  simp only [recordAtM2, hins, hfee]

/-- Opcodes a base `recordOf` can emit are never a conversion opcode nor `0x00`. -/
theorem recordOf_op_not_m2 {cof : Nat} {ci : Nat → Option Nat} {ls : List Label} {h fee pc : Nat}
    {ins : Instr} {rec : List Nat} (hr : recordOf cof ci ls h fee pc ins = some rec) :
    rec.getD 1 0 ≠ 0xA7 ∧ rec.getD 1 0 ≠ 0xAC ∧ rec.getD 1 0 ≠ 0xAD ∧ rec.getD 1 0 ≠ opUnreach := by
  unfold recordOf at hr
  split at hr <;> (try split at hr) <;> (try split at hr) <;>
    simp only [Option.some.injEq, reduceCtorEq] at hr <;> (try subst hr) <;>
    simp_all [opUnreach, Chips.Ctrl.opNext, Chips.Ctrl.opJump, Chips.Ctrl.opJif, Chips.Ctrl.opHalt,
      Chips.Ctrl.opHif, opCall, isFamilyNum, isLoadOp, isStoreOp] <;> omega

/-- **The FETCH converse for conversions.**  A record of an M2-checked pc whose opcode is a
conversion opcode is the record of that conversion: the instruction is `.num op`, the fee field is
the pc's fee, and the height field is the pc's static height. -/
theorem recordAtM2_conv_op {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) (hop : isConvOp (rec.getD 1 0) = true) :
    ∃ fee, pf.code[pc]? = some (.num (rec.getD 1 0)) ∧ feeUnits cfg pf.gas[pc]? = some fee ∧
      rec = [off + pc, rec.getD 1 0, H[pc]?.getD 0, fee, 0, 0, 0, 0] := by
  have hc : rec.getD 1 0 = 0xA7 ∨ rec.getD 1 0 = 0xAC ∨ rec.getD 1 0 = 0xAD := by
    simp only [isConvOp, Bool.or_eq_true, beq_iff_eq] at hop; omega
  unfold recordAtM2 at hr
  repeat' split at hr
  all_goals first
    | (exact absurd hc (by have := recordOf_op_not_m2 hr; omega))
    | (simp at hr; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       simp [Chips.IfC.opIf, Chips.Ctrl.opJump, Chips.opHost, opHostX, opUnreach, opMemGrowX,
         opMemSizeX] at hc; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       exact ⟨_, by simp_all, by simp_all, rfl⟩)

/-- **The FETCH converse for `unreachable`.**  A record of an M2-checked pc with opcode `0x00` is
the record of `unreachable`. -/
theorem recordAtM2_unreach_op {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) (hop : rec.getD 1 0 = opUnreach) :
    ∃ fee, pf.code[pc]? = some .unreachable ∧ feeUnits cfg pf.gas[pc]? = some fee ∧
      rec = [off + pc, opUnreach, H[pc]?.getD 0, fee, 0, 0, 0, 0] := by
  unfold recordAtM2 at hr
  repeat' split at hr
  all_goals first
    | (exact absurd hop (recordOf_op_not_m2 hr).2.2.2)
    | (simp at hr; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       simp_all [Chips.IfC.opIf, Chips.Ctrl.opJump, Chips.opHost, opHostX, opUnreach, opMemGrowX,
         opMemSizeX, isConvOp]; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       exact ⟨_, by simp_all, by simp_all, rfl⟩)

/-- **Global FETCH converse (conversions).**  A global code record `j` of an M2 context whose opcode
is a conversion opcode is the record of a conversion at a unique `(k, pc)`. -/
theorem M2Ctx.recG_conv (X : M2Ctx) {j : Nat} (hj : j < X.M.codeSize)
    (hop : isConvOp ((X.M.records[j]?.getD []).getD 1 0) = true) :
    ∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = j ∧
      (X.pfOf k).code[pc]? = some (.num ((X.M.records[j]?.getD []).getD 1 0)) ∧
      feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧
      X.M.records[j]?.getD [] = [j, (X.M.records[j]?.getD []).getD 1 0,
        (X.ckOf k).heights[pc]?.getD 0, fee, 0, 0, 0, 0] := by
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  rw [hrj, Array.getElem?_eq_getElem hsz, Option.getD_some, Option.getD_some] at hop ⊢
  obtain ⟨fee, h1, h2, h3⟩ := recordAtM2_conv_op hrec hop
  exact ⟨k, l, fee, hk, hl, hoff, h1, h2, by rw [h3, hoff]; simp⟩

/-- **Global FETCH converse (`unreachable`).** -/
theorem M2Ctx.recG_unreach (X : M2Ctx) {j : Nat} (hj : j < X.M.codeSize)
    (hop : (X.M.records[j]?.getD []).getD 1 0 = opUnreach) :
    ∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = j ∧
      (X.pfOf k).code[pc]? = some .unreachable ∧ feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧
      X.M.records[j]?.getD [] = [j, opUnreach, (X.ckOf k).heights[pc]?.getD 0, fee, 0, 0, 0, 0] := by
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  rw [hrj, Array.getElem?_eq_getElem hsz, Option.getD_some, Option.getD_some] at hop ⊢
  obtain ⟨fee, h1, h2, h3⟩ := recordAtM2_unreach_op hrec hop
  exact ⟨k, l, fee, hk, hl, hoff, h1, h2, by rw [h3, hoff]⟩

/-- The fee of any M2 record is bounded by the module's `maxFee`. -/
theorem M2Ctx.recFee_le (X : M2Ctx) {j : Nat} (hj : j < X.M.codeSize) :
    (X.M.records[j]?.getD []).getD 3 0 ≤ X.maxFee := by
  obtain ⟨k, l, hk, hl, -, hrj⟩ := X.recG hj
  rw [hrj, Option.getD_some]
  exact Nat.le_trans ((X.factsOf hk).feeLe l hl) (X.maxFee_ge hk)

/-! ## Axiom guards -/

#print axioms checkM2_sound
#print axioms checkModuleM2_sound
#print axioms M2Ctx.conv_succ
#print axioms M2Ctx.ifres_succ
#print axioms M2Ctx.else_succ
#print axioms M2Ctx.conv_record
#print axioms M2Ctx.unreach_record
#print axioms recordAtM2_conv_op
#print axioms recordAtM2_unreach_op
#print axioms M2Ctx.recG_conv
#print axioms M2Ctx.recG_unreach

end WasmBase
