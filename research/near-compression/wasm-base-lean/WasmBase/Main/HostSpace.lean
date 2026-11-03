import WasmBase.Main.SegSoundX

/-!
# WasmBase.Main.HostSpace — the space clause at HOST rows (E2E M6, `HostRely.sp`)

Every CH interaction of the tables a HOST row's traffic is fused from has a **constant** space:
HOST's argument receives / result send (space 0, operand stack), `HOSTB`'s MEMIO link (space 3,
linear memory), REG-C's register traffic (`RegW`, space 6 = `Register.space`) and the gas register
(`GasT`, space 7 = `spaceGas`).  So every message a HOST row consumes or produces (`consCHS`/`prodCHS`,
including its fused `HOSTB` bytes, REG-C net traffic and gas-register messages) is in space 0, 3, 6
or 7 — allowed (`SpaceOK`).  This is syntactic (`constSp_*`, by `decide`): no trace fact, no
grouping premise (`HostBLinked`/`RegCLinked`) and no host contract is needed.

* `host_prod_space`, `host_cons_space` — the spaces of a HOST row's fused messages;
* **`host_rowQ_sp`** — `RowQ … SpC …` at every HOST row (any trace);
* **`hostRely_sp`** — the `sp` field of `HostRely`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false

/-- The spaces of a HOST row's fused traffic: operand stack, memory, registers, gas register. -/
def hostSpaces : List Nat := [0, 3, Register.space, spaceGas]

/-- Every CH interaction of `T` has a constant space expression `.c k` with `k ∈ hostSpaces`. -/
def ConstSp (T : Table) : Bool :=
  T.inters.all fun i => decide (i.bus ≠ busStk) ||
    hostSpaces.any fun k => decide (i.msg.head? = some (.c k))

theorem constSp_host : ConstSp Host.table = true := by decide +kernel
theorem constSp_hostb : ConstSp HostB.table = true := by decide +kernel
theorem constSp_regw : ConstSp RegW.table = true := by decide +kernel
theorem constSp_gas : ConstSp GasT = true := by decide +kernel

/-- A CH message of a constant-space table is in one of `hostSpaces`. -/
theorem constSp_msg {T : Table} (hS : ConstSp T = true)
    {tr : Trace} {pub : List F} {t r : Nat} {s : Bool} {m : List F}
    (hm : m ∈ rowMsgs T tr pub t r busStk s) : (decMsg m).space ∈ hostSpaces := by
  have hP := P_val
  obtain ⟨i, hi, rfl⟩ := mem_rowMsgs hm
  have hb := (List.mem_filter.mp hi).2
  simp only [decide_eq_true_eq] at hb
  have hc := List.all_eq_true.mp hS i (List.mem_filter.mp hi).1
  simp only [Bool.or_eq_true, decide_eq_true_eq, hb.1, ne_eq, not_true_eq_false, false_or,
    List.any_eq_true] at hc
  obtain ⟨k, hk, hc⟩ := hc
  have sp : (decMsg (i.msg.map (·.eval (tr.row pub t r)))).space =
      (match i.msg.head? with | some e => e.eval (tr.row pub t r) | none => 0).toNat := by
    cases hmsg : i.msg <;> simp [decMsg, hmsg]
  have hkP : k < P := by
    simp only [hostSpaces, Register.space, spaceGas, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> omega
  rw [sp, hc]
  show (((k : Nat) : F)).toNat ∈ hostSpaces
  rw [Fp.toNat_cast_of_lt hkP]; exact hk

theorem constSp_rowProd {T : Table} (hS : ConstSp T = true)
    {tr : Trace} {pub : List F} {t r : Nat} : ∀ x ∈ rowProd T tr pub t r, x.space ∈ hostSpaces := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  exact constSp_msg hS hm

theorem constSp_rowCons {T : Table} (hS : ConstSp T = true)
    {tr : Trace} {pub : List F} {t r : Nat} : ∀ x ∈ rowCons T tr pub t r, x.space ∈ hostSpaces := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  exact constSp_msg hS hm

/-- The spaces of a HOST row's fused traffic. -/
def HostSp (x : Msg) : Prop := x.space ∈ hostSpaces

theorem hostSp_ok {x : Msg} (h : HostSp x) : SpaceOK x := by
  unfold HostSp at h
  unfold SpaceOK
  simp only [hostSpaces, Register.space, spaceGas, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> rw [h] <;> simp

/-- **Every message a HOST row produces** (its own, its `HOSTB` bytes, its REG-C net traffic and its
gas register) is in space 0, 3, 6 or 7. -/
theorem host_prod_space (tr : Trace) (pub : List F) {ρ : Nat × Nat} (h22 : ρ.1 = 22) :
    ∀ x ∈ prodCHS tr pub ρ, HostSp x := by
  obtain ⟨t, r⟩ := ρ
  simp only at h22; subst h22
  intro x hx
  simp only [prodCHS, prodCHM2, rowProdM, hostbProdH, regProdH, gasProdH, chipTM2, ite_true,
    List.mem_append] at hx
  rcases hx with ((hx | hx | hx) | hx)
  · exact constSp_rowProd constSp_host x hx
  · unfold hostbProdOf at hx
    obtain ⟨r', -, hx⟩ := List.mem_flatMap.mp hx
    exact constSp_rowProd constSp_hostb x hx
  · unfold regProdOf at hx
    obtain ⟨r', -, hx⟩ := List.mem_flatMap.mp hx
    unfold regNetProd at hx
    split at hx
    · simp at hx
    · exact constSp_rowProd constSp_regw x hx
  · unfold gasProdOf at hx
    exact constSp_rowProd constSp_gas x hx

/-- **Every message a HOST row consumes** is in space 0, 3, 6 or 7. -/
theorem host_cons_space (tr : Trace) (pub : List F) {ρ : Nat × Nat} (h22 : ρ.1 = 22) :
    ∀ x ∈ consCHS tr pub ρ, HostSp x := by
  obtain ⟨t, r⟩ := ρ
  simp only at h22; subst h22
  intro x hx
  simp only [consCHS, consCHM2, rowConsM, hostbConsH, regConsH, gasConsH, chipTM2, ite_true,
    List.mem_append] at hx
  rcases hx with ((hx | hx | hx) | hx)
  · exact constSp_rowCons constSp_host x hx
  · unfold hostbConsOf at hx
    obtain ⟨r', -, hx⟩ := List.mem_flatMap.mp hx
    exact constSp_rowCons constSp_hostb x hx
  · unfold regConsOf at hx
    obtain ⟨r', -, hx⟩ := List.mem_flatMap.mp hx
    unfold regNetCons at hx
    exact constSp_rowCons constSp_regw x hx
  · unfold gasConsOf at hx
    exact constSp_rowCons constSp_gas x hx

/-- **The space clause at a HOST row** (`RowQ` for `SpC`), for any trace: the row's fused messages
are in allowed spaces. -/
theorem host_rowQ_sp (X : Ctx) (tr : Trace) (pub : List F) {ρ : Nat × Nat} (h22 : ρ.1 = 22) :
    RowQ X (fun _ live => SpC live) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) :=
  rowQ_space fun _ _ _ _ _ _ _ _ _ _ _ _ _ x hx => hostSp_ok (host_prod_space tr pub h22 x hx)

/-- **`HostRely.sp` is a theorem** (no premise). -/
theorem hostRely_sp (X : Ctx) (tr : Trace) (pub : List F) :
    ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 →
      RowQ X (fun _ live => SpC live) (rowInM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) :=
  fun _ _ h22 => host_rowQ_sp X tr pub h22

#print axioms host_prod_space
#print axioms host_cons_space
#print axioms hostRely_sp

end WasmBase
