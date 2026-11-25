import WasmBase.PrepDec
import WasmBase.M2Ctx
/-!
# WasmBase.PrepCert — what a decoded instruction fixes in the M2 records (A-T4)

`PrepDec.decFields j (dimg ins)` lists the record fields the PREP AIR's decoder fixes for
instruction `ins` at global pc `j`.  This file proves the spec side: **every record
`recordAtM2` produces agrees with them** (`recordAtM2_agree`), and so does every record of a
checked module (`checkModuleM2_agree`).  The AIR side (the cached CODE row agrees with the same
fields) is `PrepDecSound`; together they leave only the fields marked `none` — the static analysis —
to the residual `StaticCert`.
-/
namespace WasmBase
namespace PrepDec
open NearSpecV3.Wasm

theorem clsOf_num : ∀ op, op < 256 → (isFamilyNum op = true ∨ isConvOp op = true) →
    clsOf op = some .eq0 := by decide +kernel

theorem clsOf_load : ∀ op, op < 256 → isLoadOp op = true → clsOf op = some .mem := by decide +kernel
theorem clsOf_store : ∀ op, op < 256 → isStoreOp op = true → clsOf op = some .mem := by decide +kernel

theorem famNum_lt {op : Nat} (h : isFamilyNum op = true ∨ isConvOp op = true) : op < 256 := by
  simp only [isFamilyNum, isConvOp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  omega

theorem load_lt {op : Nat} (h : isLoadOp op = true) : op < 256 := by
  simp only [isLoadOp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; omega
theorem store_lt {op : Nat} (h : isStoreOp op = true) : op < 256 := by
  simp only [isStoreOp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; omega

theorem agree8 (fs : List (Option Nat)) (r : List Nat) (h : agreeB fs r = true) : Agree fs r := h

theorem clsOf_1000 : clsOf 1000 = none := by decide +kernel

macro "agree_tac" : tactic => `(tactic| (simp only [dimg]; (first | rw [decFields_eq rfl] | simp only [decFields, clsOf_1000]); simp [Agree, agreeB, fieldsOf, List.range_succ, opMemGrowX, opMemSizeX, opUnreach]))

/-- **The spec's records agree with the decoded fields.** -/
theorem recordAtM2_agree {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off : Nat} {cinfo : Nat → Option Nat} {pc : Nat} {r : List Nat} {ins : Instr}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some r) (hi : pf.code[pc]? = some ins) :
    Agree (decFields (off + pc) (dimg ins)) r := by
  unfold recordAtM2 at hr
  rw [hi] at hr
  cases hf : feeUnits cfg pf.gas[pc]? with
  | none =>
    rw [hf] at hr
    cases ins <;> simp at hr
    subst hr; agree_tac
  | some fee =>
    rw [hf] at hr
    cases ins with
    | num op =>
      simp only at hr
      split at hr
      · rename_i hc
        cases hr
        simp only [dimg]; rw [decFields_eq (clsOf_num op (famNum_lt (.inr hc)) (.inr hc))]
        simp [Agree, agreeB, fieldsOf, List.range_succ]
      · simp only [recordOf] at hr
        split at hr
        · rename_i hf2
          cases hr
          simp only [dimg]; rw [decFields_eq (clsOf_num op (famNum_lt (.inl hf2)) (.inl hf2))]
          simp [Agree, agreeB, fieldsOf, List.range_succ]
        · cases hr
    | load op a o =>
      simp only [recordOf] at hr
      split at hr
      · rename_i hc
        cases hr
        simp only [dimg]; rw [decFields_eq (clsOf_load op (load_lt hc.1) hc.1)]
        simp [Agree, agreeB, fieldsOf, List.range_succ]
      · cases hr
    | store op a o =>
      simp only [recordOf] at hr
      split at hr
      · rename_i hc
        cases hr
        simp only [dimg]; rw [decFields_eq (clsOf_store op (store_lt hc.1) hc.1)]
        simp [Agree, agreeB, fieldsOf, List.range_succ]
      · cases hr
    | i32Const v =>
      simp only [recordOf] at hr
      cases hr
      have hv := v.toNat_lt
      have h1 : v.toNat / 2 ^ 32 = 0 := Nat.div_eq_of_lt (by simpa using hv)
      have h2 : v.toNat / 2 ^ 48 = 0 := Nat.div_eq_of_lt (by simp at hv; omega)
      simp only [dimg]; rw [decFields_eq rfl]
      simp [Agree, agreeB, fieldsOf, List.range_succ, limbs4, h1, h2]
    | i64Const v =>
      simp only [recordOf] at hr
      cases hr
      simp only [dimg]; rw [decFields_eq rfl]
      simp [Agree, agreeB, fieldsOf, List.range_succ, limbs4]
    | call fi =>
      simp only at hr
      split at hr
      · split at hr
        · cases hr; agree_tac
        · split at hr
          · cases hr; agree_tac
          · cases hr
      · simp only [recordOf] at hr
        split at hr
        · cases hr; agree_tac
        · cases hr
    | if_ bt =>
      simp only at hr
      split at hr
      · cases hr; agree_tac
      · cases hr
    | else_ =>
      simp only at hr
      split at hr
      · cases hr; agree_tac
      · cases hr
    | unreachable => cases hr; agree_tac
    | memGrow => cases hr; agree_tac
    | memSize => cases hr; agree_tac
    | globalGet x =>
      simp only [recordOf] at hr; split at hr
      · cases hr; agree_tac
      · cases hr
    | globalSet x =>
      simp only [recordOf] at hr; split at hr
      · cases hr; agree_tac
      · cases hr
    | select t =>
      simp only [recordOf] at hr
      cases hr
      cases t <;> agree_tac
    | localGet x => simp only [recordOf] at hr; cases hr; agree_tac
    | localSet x => simp only [recordOf] at hr; cases hr; agree_tac
    | localTee x => simp only [recordOf] at hr; cases hr; agree_tac
    | drop => simp only [recordOf] at hr; cases hr; agree_tac
    | block bt => simp only [recordOf, kindOf] at hr; cases hr; agree_tac
    | loop bt =>
      cases bt with
      | none => simp only [recordOf, kindOf] at hr; cases hr; agree_tac
      | some t => simp [recordOf, kindOf] at hr
    | ret => simp only [recordOf, kindOf] at hr; cases hr; agree_tac
    | end_ =>
      simp only [recordOf, kindOf] at hr
      cases hL : L[pc]?.getD [] with
      | nil => simp [hL] at hr
      | cons a t =>
        cases t with
        | nil => simp [hL] at hr; subst hr; agree_tac
        | cons b t => simp [hL] at hr; subst hr; agree_tac
    | br l =>
      simp only [recordOf] at hr
      split at hr <;> first | (cases hr; agree_tac) | simp at hr
    | brIf l =>
      simp only [recordOf] at hr
      split at hr <;> first | (cases hr; agree_tac) | simp at hr
    | _ => simp [recordOf, kindOf] at hr

/-- **Per checked function**: its records agree with the decoded fields of its instructions. -/
theorem checkModuleM2_agree {cfg : NearCfg} {p : Prepared} {entry : Nat} {MH : ModOutH}
    (h : checkModuleM2 cfg p entry = some MH) (k : Nat) (hk : k < MH.mod.fns.length) :
    ∃ pf, p.funcs[MH.mod.fns.getD k 0]? = some pf ∧ MH.mod.sizes.getD k 0 = pf.code.size ∧
      ∀ l, l < pf.code.size → ∃ ins r, pf.code[l]? = some ins ∧
        (MH.mod.cks.getD k default).records[l]? = some r ∧
        Agree (decFields (MH.mod.offs.getD k 0 + l) (dimg ins)) r := by
  have F := checkModuleM2_sound h
  obtain ⟨pf, F2⟩ := checkM2_sound (F.cks k hk)
  obtain ⟨pf', hpf', hsz⟩ := F.pfs k hk
  have e : pf' = pf := by rw [F2.func] at hpf'; exact (Option.some.inj hpf').symm
  subst e
  refine ⟨pf', hpf', hsz, fun l hl => ?_⟩
  obtain ⟨ins, hins⟩ : ∃ ins, pf'.code[l]? = some ins := ⟨pf'.code[l], Array.getElem?_eq_getElem hl⟩
  have hr := F2.recs l hl
  cases hrr : (MH.mod.cks.getD k default).records[l]? with
  | none => rw [hrr] at hr
            unfold recordAtM2 at hr; rw [hins] at hr
            have : (MH.mod.cks.getD k default).records.size = pf'.code.size := F2.records
            have : l < (MH.mod.cks.getD k default).records.size := by omega
            rw [Array.getElem?_eq_getElem this] at hrr; cases hrr
  | some r => rw [hrr] at hr; exact ⟨ins, r, hins, rfl, recordAtM2_agree hr hins⟩

end PrepDec
end WasmBase
