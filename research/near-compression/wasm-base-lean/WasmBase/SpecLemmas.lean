import WasmBase.Event
import WasmBase.CheckFacts
/-!
# Spec-side lemmas: `execNum` on family opcodes, popping, pushing
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-- Binary arithmetic family opcodes (incl. div/rem) and their width / binop index. -/
def binops : List Nat := [0x6A, 0x6B, 0x6C, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x7C, 0x7D, 0x7E,
  0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8A, 0x6D, 0x6E, 0x6F, 0x70, 0x7F, 0x80, 0x81, 0x82]
def isBinop (op : Nat) : Prop := op ∈ binops

def opW (op : Nat) : Nat := if op ≤ 0x78 then 32 else 64
def opK (op : Nat) : Nat := if op ≤ 0x78 then op - 0x6A else op - 0x7C

theorem execNum_binop (s : St) (op : Nat) (hop : isBinop op) :
    execNum s op =
      (match Num.binop (opW op) (opK op) (popN (popN s).2).1 (popN s).1 with
       | some r => .ok (if opW op = 32 then pushI32 (popN (popN s).2).2 r else pushI64 (popN (popN s).2).2 r)
       | none => .error (trapStr "IllegalArithmetic")) := by
  simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop
  rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;> simp [execNum, opW, opK] <;> rfl

end WasmBase

namespace WasmBase
open NearSpecV3.Wasm

theorem checkModule_sound {cfg : NearCfg} {p : Prepared} {entry : Nat} {M : ModOut}
    (h : checkModule cfg p entry = some M) : ModFacts cfg p entry M := by
  unfold checkModule at h
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
        obtain ⟨hhd, htot, hlay, hcl, hent⟩ := hcond
        obtain ⟨hcl1, hcl2⟩ := mapM_some _ _ _ hc
        obtain ⟨hpl1, hpl2⟩ := mapM_some _ _ _ hp
        simp only [List.length_range] at hcl1
        refine ⟨hhd, ?_, ?_, htot, hlay, by simp, ?_, ?_, hcl, ?_, ?_, ?_, by simp⟩
        · intro k hk
          dsimp only at hk ⊢
          have := hcl2 k (by simpa using hk)
          simp only [List.getElem_range] at this
          apply check_sound
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

theorem Ctx.mf (X : Ctx) : ModFacts X.cfg X.p X.fn X.M := X.hM

/-- **The base context**: built from a successful base `checkModule`. -/
def Ctx.ofCheck (cfg : NearCfg) (p : Prepared) (fn : Nat) (M : ModOut) (g0 : Nat)
    (h : checkModule cfg p fn = some M) : Ctx := ⟨cfg, p, fn, M, g0, checkModule_sound h⟩

/-- No checked function of the context contains an M2 addition: the base checker's domain. -/
def Ctx.Base (X : Ctx) : Prop :=
  ∀ k, k < X.nf → ∀ (pc : Nat) (ins : Instr), (X.pfOf k).code[pc]? = some ins → m2Special X.p ins = false

/-- The per-function `check` equations of a successful `checkModule`. -/
theorem checkModule_check {cfg : NearCfg} {p : Prepared} {entry : Nat} {M : ModOut}
    (h : checkModule cfg p entry = some M) : ∀ k, k < M.fns.length →
      check cfg p (M.fns.getD k 0) (M.offs.getD k 0) (callInfo p M.fns M.offs) = some (M.cks.getD k default) := by
  unfold checkModule at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i cks hc
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hcl1, hcl2⟩ := mapM_some _ _ _ hc
        simp only [List.length_range] at hcl1
        intro k hk
        dsimp only at hk ⊢
        have := hcl2 k (by simpa using hk)
        simp only [List.getElem_range] at this
        rw [this, List.getD_eq_getElem?_getD (l := cks), List.getElem?_eq_getElem (by omega), Option.getD_some]
      · simp at h

/-- A base-checked context is `Base`. -/
theorem Ctx.ofCheck_base {cfg : NearCfg} {p : Prepared} {fn : Nat} {M : ModOut} {g0 : Nat}
    (h : checkModule cfg p fn = some M) : (Ctx.ofCheck cfg p fn M g0 h).Base := by
  unfold Ctx.Base
  intro k hk pc ins hins
  have hc := checkModule_check h k hk
  simp only [Ctx.ofCheck, Ctx.pfOf, Ctx.fnOf, Ctx.nf] at hins hk ⊢
  cases hpf : p.funcs[M.fns.getD k 0]? with
  | none => obtain ⟨pf, F⟩ := check_sound hc; rw [F.func] at hpf; cases hpf
  | some pf =>
    rw [hpf, Option.getD_some] at hins
    exact check_nonspecial hc hpf hins

theorem Ctx.layout (X : Ctx) :
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

theorem Ctx.sizeOf (X : Ctx) {k : Nat} (hk : k < X.nf) : X.M.sizes.getD k 0 = (X.pfOf k).code.size := by
  obtain ⟨pf, h1, h2⟩ := X.mf.pfs k hk
  simp only [Ctx.pfOf, Ctx.fnOf, h1, Option.getD_some, h2]

/-- Call-target info of the module's records. -/
def Ctx.cinfo (X : Ctx) : Nat → Option Nat := callInfo X.p X.M.fns X.M.offs

/-- The facts of `check` for every checked function. -/
theorem Ctx.factsOf (X : Ctx) {k : Nat} (hk : k < X.nf) :
    CheckFacts X.cfg X.p (X.fnOf k) (X.offOf k) X.cinfo (X.pfOf k) (X.ckOf k) := by
  obtain ⟨pf', h⟩ := X.mf.cks k hk
  have : pf' = X.pfOf k := by
    have := h.func; simp only [Ctx.pfOf, Ctx.fnOf, this, Option.getD_some]
  subst this; exact h

theorem Ctx.nf_pos (X : Ctx) : 0 < X.nf := by
  have := X.mf.head
  unfold Ctx.nf; cases h : X.M.fns with
  | nil => rw [h] at this; simp at this
  | cons _ _ => simp

theorem Ctx.fnOf_zero (X : Ctx) : X.fnOf 0 = X.fn := by
  have := X.mf.head
  unfold Ctx.fnOf; cases h : X.M.fns with
  | nil => rw [h] at this; simp at this
  | cons a _ => rw [h] at this; simp at this; simp [this]

theorem Ctx.off_zero (X : Ctx) : X.offOf 0 = 0 := X.mf.offs0

/-- The entry function's `check` facts. -/
theorem Ctx.facts (X : Ctx) : CheckFacts X.cfg X.p X.fn 0 X.cinfo X.pf X.ck := by
  have := X.factsOf X.nf_pos
  rw [X.fnOf_zero, X.off_zero] at this; exact this

/-- The entry function has no params. -/
theorem Ctx.entry_params (X : Ctx) : X.pf.type.params.size = 0 := by
  obtain ⟨pf, h1, h2⟩ := X.mf.entryParams
  have : X.pf = pf := by
    unfold Ctx.pf Ctx.pfOf; rw [X.fnOf_zero, h1]; rfl
  rw [this]; exact h2

theorem Ctx.maxFee_ge (X : Ctx) {k : Nat} (hk : k < X.nf) : (X.ckOf k).maxFee ≤ X.maxFee := by
  have := X.mf.feeLe k 0 hk X.nf_pos; unfold Ctx.ckOf Ctx.maxFee; omega

/-- A call's fee plus the callee's prologue units fit the module-wide fee bound. -/
theorem Ctx.callFee_le (X : Ctx) {k j : Nat} (hk : k < X.nf) (hj : j < X.nf) :
    (X.ckOf k).maxFee + (X.ckOf j).prologue ≤ X.maxFee := X.mf.feeLe k j hk hj

/-- A global record is a shifted local record of the checked function containing it. -/
theorem Ctx.recG (X : Ctx) {j : Nat} (hj : j < X.M.codeSize) :
    ∃ k l, k < X.nf ∧ l < (X.pfOf k).code.size ∧ X.offOf k + l = j ∧
      X.M.records[j]? = some ((X.ckOf k).records[l]?.getD []) := by
  obtain ⟨-, -, h3, -⟩ := X.layout
  obtain ⟨a, b, c⟩ := h3 j hj
  refine ⟨_, _, a, by rw [← X.sizeOf a]; exact b, c, X.mf.recs j hj⟩

/-- Global pcs determine the function and the local pc. -/
theorem Ctx.loc_unique (X : Ctx) {k l k' l' : Nat} (hk : k < X.nf) (hl : l < (X.pfOf k).code.size)
    (hk' : k' < X.nf) (hl' : l' < (X.pfOf k').code.size) (h : X.offOf k + l = X.offOf k' + l') :
    k = k' ∧ l = l' := by
  obtain ⟨-, -, -, h4⟩ := X.layout
  have e1 := (h4 k hk).2 l (by rw [X.sizeOf hk]; exact hl)
  have e2 := (h4 k' hk').2 l' (by rw [X.sizeOf hk']; exact hl')
  unfold Ctx.offOf at h
  rw [h, e2] at e1
  simp only [Prod.mk.injEq] at e1
  exact ⟨e1.1.symm, e1.2.symm⟩

theorem Ctx.off_bound (X : Ctx) {k : Nat} (hk : k < X.nf) : X.offOf k + (X.pfOf k).code.size ≤ X.M.codeSize := by
  obtain ⟨-, -, -, h4⟩ := X.layout
  have := (h4 k hk).1; rw [X.sizeOf hk] at this; exact this

end WasmBase

namespace WasmBase
open NearSpecV3.Wasm

theorem popN_eq (s : St) :
    popN s = (vNum (s.stack.back?.getD (.i32 0)), { s with stack := s.stack.pop }) := by
  unfold popN popV
  cases s.stack.back?.getD (.i32 0) <;> rfl

theorem popV_eq (s : St) : popV s = (s.stack.back?.getD (.i32 0), { s with stack := s.stack.pop }) := rfl

theorem back_getD (a : Array Val) (h : 0 < a.size) :
    a.back?.getD (.i32 0) = a[a.size - 1]?.getD default := by
  rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  rfl

theorem getD_eq_of_getElem? {a : Array Val} {i : Nat} (h : i < a.size) :
    a[i]?.getD default = a[i] := by
  rw [Array.getElem?_eq_getElem h]; rfl

/-- `vNum` of a well-formed message's decoded value is its value. -/
theorem vNum_toVal {m : Msg} (hm : m.ok) : vNum m.toVal = m.val := by
  have := enc_val (v := m.toVal) (by unfold Msg.toVal; split <;> trivial) m.space m.slot m.tp
  rw [enc_of_ok hm] at this
  exact this.symm

theorem isNum_toVal (m : Msg) : isNum m.toVal := by unfold Msg.toVal; split <;> trivial

end WasmBase

namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

def relops : List Nat := [0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F,
  0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]
def relW (op : Nat) : Nat := if op ≤ 0x4F then 32 else 64
def relK (op : Nat) : Nat := if op ≤ 0x4F then op - 0x46 else op - 0x51

theorem execNum_relop (s : St) (op : Nat) (hop : op ∈ relops) :
    execNum s op = .ok (pushI32 (popN (popN s).2).2
      (Num.b2 (Num.relop (relW op) (relK op) (popN (popN s).2).1 (popN s).1))) := by
  simp only [relops, List.mem_cons, List.mem_nil_iff, or_false] at hop
  rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;> simp [execNum, relW, relK] <;> rfl

theorem execNum_eqz (s : St) (op : Nat) (hop : op = 0x45 ∨ op = 0x50) :
    execNum s op = .ok (pushI32 (popN s).2 (Num.b2 ((popN s).1 = 0))) := by
  rcases hop with rfl | rfl <;> simp [execNum] <;> rfl

end WasmBase
