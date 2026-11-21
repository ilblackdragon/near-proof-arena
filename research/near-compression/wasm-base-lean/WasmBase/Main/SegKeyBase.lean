import WasmBase.Main.SegHoldsS
import WasmBase.Main.SegMemb

/-!
# WasmBase.Main.SegKeyBase — the call-key lookup (bus 214), upstream of the CH fold (E2E A-T1)

The generic part of `Main/SegKey.lean` (moved here unchanged so that `Main/SegBus.lean` can use it):
the interactions on the call-key bus (`seg_key_inters`), the `act` bits, and **`seg_key_lookup`** —
a send on bus 214 with count 1 carries the key of an active HOST row.  New here:
**`hostb_key_linked`** — every `HOSTB` row with `act = 1` (request, response/write and register
rows alike) carries the `(ts, hid)` key of an active HOST row.  `HostBLinked.linked` only covers
the request rows (`rowAct HostB.table` is `memCnt = 1`); the memory-write rows of A-T1
(`HostBK.wcnt`) are grouped by this lemma instead (`Main/SegBus.lean`, `seg_hostbW_partition`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

theorem okBus_hkey : OkBus busHKey := by decide

/-- The only interactions on the call-key bus (Boolean form, checked by the kernel). -/
theorem seg_key_inters_b :
    ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length),
      ((wasmBaseSegAir 0 0).tables[t]'ht).inters.all (fun i => !decide (i.bus = busHKey) ||
        (decide (t = 22) && decide (i = HostG.keyRecv)) || (decide (t = 25) && decide (i = HostBK.keySend)) ||
        (decide (t = 27) && decide (i = RegCK.keySend))) = true := by
  decide +kernel

/-- **The interactions on the call-key bus**: HOST's offer, HOSTB's and REG-C's lookups. -/
theorem seg_key_inters (nloc ngl : Nat) {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length)
    {i : Inter} (hi : i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters) (hb : i.bus = busHKey) :
    (t = 22 ∧ i = HostG.keyRecv) ∨ (t = 25 ∧ i = HostBK.keySend) ∨ (t = 27 ∧ i = RegCK.keySend) := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have ht0 : t < (wasmBaseSegAir 0 0).tables.length := by rw [← e]; exact ht
  have h1 := seg_key_inters_b t ht0
  have hi0 : i ∈ ((wasmBaseSegAir 0 0).tables[t]'ht0).inters := by simp only [← e]; exact hi
  have := List.all_eq_true.mp h1 i hi0
  simp only [hb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, not_true_eq_false, false_or] at this
  rcases this with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem fp_bit_toNat {x : F} (h : x * (x - 1) = 0) : x.toNat ≤ 1 := by
  rcases bool_cases h with rfl | rfl <;> decide

theorem fp_toNat_one {x : F} (h : x = 1) : x.toNat = 1 := by subst h; decide

theorem fp_eq_one_of_toNat {x : F} (h : x.toNat = 1) : x = 1 := by
  have := Fp.cast_toNat x
  rw [h] at this
  rw [← this]; rfl

theorem seg_t22_key (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[22]'(by simp [seg_air_len]) = HostG.table := rfl

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

omit H in
theorem seg_t22_lt : 22 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
omit H in
theorem seg_t25_lt : 25 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
omit H in
theorem seg_t27_lt' : 27 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]

/-- A cell constrained by `bool` is a bit. -/
theorem key_bit {t : Nat} [SegT t] (ht : t < (wasmBaseSegAir nloc ngl).tables.length) {r : Nat}
    (hr : r < tr.height t) {c : Nat} (hc : bool (v c) ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).constraints) :
    (tr.cell t r c).toNat ≤ 1 := by
  have h := H.constr t ht r hr _ hc
  simp only [Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
    Trace.row] at h
  exact fp_bit_toNat h

theorem host_act_seg_bit {r : Nat} (hr : r < tr.height 22) : (tr.cell 22 r Host.act).toNat ≤ 1 :=
  key_bit H (t := 22) (seg_t22_lt (nloc := nloc) (ngl := ngl)) hr (c := Host.act) (by
    rw [seg_t22_key]; show Host.cAct ∈ HostG.constraints
    exact HostG.constraints_prefix.subset (HostR.constraints_prefix.subset (by simp [Host.constraints, Host.cBase])))

theorem hostb_act_seg_bit {r : Nat} (hr : r < tr.height 25) : (tr.cell 25 r HostB.act).toNat ≤ 1 :=
  key_bit H (t := 25) (seg_t25_lt (nloc := nloc) (ngl := ngl)) hr (c := HostB.act) (by
    show HostB.cAct ∈ HostBK.constraints
    exact HostBK.constraints_prefix.subset (by simp [HostB.constraints]))

theorem reg_act_seg_bit {r : Nat} (hr : r < tr.height 27) : (tr.cell 27 r Reg.act).toNat ≤ 1 :=
  key_bit H (t := 27) (seg_t27_lt' (nloc := nloc) (ngl := ngl)) hr (c := Reg.act)
    ((regAt_seg nloc ngl).cons _ (by simp [Reg.table, Reg.constraints, Reg.cAct]))

/-- An active key offer: a HOST row with `nk ≠ 0` is active. -/
theorem host_nk_act {r : Nat} (hr : r < tr.height 22) (hnk : tr.cell 22 r HostG.nk ≠ 0) :
    rowAct Host.table tr pub 22 r := by
  have h := H.constr 22 (seg_t22_lt (nloc := nloc) (ngl := ngl)) r hr HostG.cNk (by
    rw [seg_t22_key]; show HostG.cNk ∈ HostR.constraints ++ [HostG.cNk]; simp)
  simp only [HostG.cNk, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
    Trace.row] at h
  rcases mul_eq_zero' h with h | h
  · have ha : tr.cell 22 r Host.act = 1 := by grind
    show ((Host.inters.getD 0 default).count.eval (tr.row pub 22 r)).toNat = 1
    show ((v Host.act).eval (tr.row pub 22 r)).toNat = 1
    simp only [Chips.v, Expr.eval_col, Trace.row, ha]; decide
  · exact absurd h hnk

/-- The keys offered with a nonzero count are the keys of active HOST rows. -/
def KeyQ (tr : Trace) (pub : List F) (m : List F) : Prop :=
  ∃ r, r < tr.height 22 ∧ rowAct Host.table tr pub 22 r ∧ m = [tr.cell 22 r cTs, tr.cell 22 r Host.hid]

/-- **The call-key lookup**: a send on bus 214 with count 1 carries the key of an active HOST row. -/
theorem seg_key_lookup {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) {r : Nat}
    (hr : r < tr.height t) {i : Inter} (hi : i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters)
    (hb : i.bus = busHKey) (hs : i.send = true) (hc : (i.count.eval (tr.row pub t r)).toNat = 1) :
    KeyQ tr pub (i.msg.map (·.eval (tr.row pub t r))) := by
  have ho := occ_of_inter ht hr hi hc
  refine lookup_soundXS H busHKey okBus_hkey (KeyQ tr pub) ?_ ?_ ho hb hs rfl
  · intro o ho' hb' hs' hc'
    obtain ⟨t', ht', r', hr', i', hi', rfl⟩ := mem_occs.mp ho'
    simp only at hb' hs' hc' ⊢
    rcases seg_key_inters nloc ngl ht' hi' hb' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨r', hr', host_nk_act H hr' ?_, ?_⟩
      · intro h0
        apply hc'
        simp only [HostG.keyRecv, Chips.v, Expr.eval_col, Trace.row, h0]; decide
      · simp [HostG.keyRecv, Chips.v, Expr.eval_col, Trace.row]
    · simp [HostBK.keySend] at hs'
    · simp [RegCK.keySend] at hs'
  · intro o ho' hb' hs'
    obtain ⟨t', ht', r', hr', i', hi', rfl⟩ := mem_occs.mp ho'
    simp only at hb' hs' ⊢
    rcases seg_key_inters nloc ngl ht' hi' hb' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [HostG.keyRecv] at hs'
    · simpa [HostBK.keySend, Chips.v, Expr.eval_col, Trace.row] using hostb_act_seg_bit H hr'
    · simpa [RegCK.keySend, Chips.v, Expr.eval_col, Trace.row] using reg_act_seg_bit H hr'


/-- **Every `HOSTB` row with `act = 1` belongs to an active HOST row** (its `(ts, hid)` key is
offered on bus 214).  Covers the A-T1 memory-write rows, which `HostBLinked.linked` does not. -/
theorem hostb_key_linked {r' : Nat} (hr' : r' < tr.height 25) (hact : tr.cell 25 r' HostB.act = 1) :
    ∃ r, r < tr.height 22 ∧ rowAct Host.table tr pub 22 r ∧
      rowNat tr 25 r' HostB.ts = rowNat tr 22 r cTs ∧ rowNat tr 25 r' HostB.hid = rowNat tr 22 r Host.hid := by
  have hi : HostBK.keySend ∈ ((wasmBaseSegAir nloc ngl).tables[25]'(seg_t25_lt (nloc := nloc) (ngl := ngl))).inters := by
    show HostBK.keySend ∈ HostBK.wireInters ++ [HostBK.keySend] ++ HostBK.writeInters; simp
  obtain ⟨r, hr, hra, hm⟩ := seg_key_lookup H (seg_t25_lt (nloc := nloc) (ngl := ngl)) hr' hi rfl rfl (by
    simp only [HostBK.keySend, Chips.v, Expr.eval_col, Trace.row, hact]; decide)
  simp only [HostBK.keySend, Chips.v, Expr.eval_col, Trace.row, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at hm
  exact ⟨r, hr, hra, congrArg Fp.toNat hm.1, congrArg Fp.toNat hm.2⟩

end

#print axioms seg_key_lookup
#print axioms hostb_key_linked

end WasmBase
