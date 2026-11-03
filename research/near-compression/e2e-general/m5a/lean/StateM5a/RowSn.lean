import StateM5a.RowBrF

/-!
# StateM5a.RowSn — an `SN` walk row, decoded: messages, op flags, old record

* `sn_di` … `sn_uo`: the `SN` walk messages on `DOWN` / `UP` (read off the exported table);
  `sn_din` … `sn_uout`: decoded with `RowDec.cDc`;
* `sn_flags'` / `snfacts`: the op bundle on an active walk row (`mF + mU + mD = 1`): `act = 1`,
  the non-walk ops (`oLS`, `oLM`, `oEP`, `oEM`) are `0`, the mode sums, `isL` / `isE` / `gdn` /
  `gA` / `g2` as sums of ops, every flag `≤ 1`;
* `snOld`: the row's old record under its input ref `snIn` — a leaf `key ↦ (vlen, vh)` (`isL`) or
  an extension `key → (xf, x)` — with the head key `snKey` (`klen` nibbles `k_j`; continued keys,
  `cont = 1`, are not covered here).
-/

namespace StateM5a.RowSn

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Messages -/

theorem sn_di : snW.di = [Sn.c "w", Sn.c "d", Sn.c "oref"] ++ pack2 (fun b => Sn.c "ho" b) ++
    payE (fun s j => Sn.c s j) Sn.mode := by
  simp [snW, payE]; filt

theorem sn_dd : snW.dd = [Sn.c "w", Sn.c "d" + Sn.c "klen", Sn.c "xf"] ++ pack2 (fun b => Sn.c "x" b) ++
    payE (fun s j => Sn.c s j) Sn.mode := by
  simp [snW, payE]; filt

theorem sn_ui : snW.ui = [Sn.c "w", Sn.c "d" + Sn.c "klen", Sn.c "rkc",
      (Sn.c "oEU" + Sn.c "oEB") * Sn.c "nxf" + Sn.c "oES" * Sn.c "xf"] ++
    ((pack2 (fun b => Sn.c "nx" b)).zip (pack2 fun b => Sn.c "x" b)).map
      (fun (p, q) => (Sn.c "oEU" + Sn.c "oEB") * p + Sn.c "oES" * q) ++
    ((List.range 4).map fun t => (Sn.c "oEU" + Sn.c "oEB") * Sn.c "unm" t) ++
    ((List.range 4).map fun t => Sn.c "uom" t) ++
    [Sn.c "oED" * Sn.c "kid2", Sn.c "oED" * (Sn.c "d" + Sn.c "klen"), (Sn.c "oEF" + Sn.c "oED") * Sn.c "alen"] ++
    ((List.range 16).map fun i => (Sn.c "oEF" + Sn.c "oED") * Sn.c "avh" i) ++ [Sn.c "oEF" * Sn.c "fpres"] := by
  simp [snW]; filt

/-- The `UP` send's result kind. -/
def rkE : Expr :=
  Sn.c "oLR" + Sn.c "oEU" + sm RK_H Sn.gX + sm RK_LD (Sn.c "oED") + sm RK_NONE (Sn.c "oLD") +
    sm RK_HE (Sn.c "oEB") + sm RK_SAME Sn.gS
def gnu : Expr := Sn.c "oLR" + Sn.c "oEU" + Sn.c "oEB"

theorem sn_uo : snW.uo = [Sn.c "w", Sn.c "d", rkE, gnu * Sn.c "nref" + Sn.gS * Sn.c "oref" + Sn.gX * Sn.c "shf"] ++
    (((pack2 (fun b => Sn.c "hn" b)).zip (pack2 fun b => Sn.c "ho" b)).zip ((List.range 16).map fun i => Sn.c "sh" i)).map
      (fun ((p, q), s) => gnu * p + Sn.gS * q + Sn.gX * s) ++
    ((Sn.NM.zip ((List.range 4).map fun t => Sn.c "sm" t)).map fun (p, s) => gnu * p + Sn.gX * s) ++
    Sn.M.map ((Sn.c "mU" + Sn.c "mD") * ·) ++
    [Sn.c "oED" * Sn.c "kid2", Sn.c "oED" * Sn.c "d",
      Sn.c "oLF" * Sn.vlenOf (fun t => Sn.c "x" t) + (Sn.c "oEF" + Sn.c "oED") * Sn.c "alen"] ++
    ((pack2 fun b => Sn.c "x" (4 + b)).zip ((List.range 16).map fun i => Sn.c "avh" i)).map
      (fun (p, q) => Sn.c "oLF" * p + (Sn.c "oEF" + Sn.c "oED") * q) ++
    [Sn.c "oLF" + Sn.c "oEF" * Sn.c "fpres"] := by
  simp [snW, rkE, gnu]; filt

/-! ## Op flags -/

/-- The flags with a booleanity constraint (`FieldWalk.sn_bool`). -/
def snNames : List String := ["act", "mF", "mU", "mD", "isE", "gdn", "oLF", "oLR", "oLD",
    "oLS", "oLM", "oEF", "oEU", "oED", "oLA", "oEA", "oLZ", "oEZ", "oES", "oEB", "oLX", "oEX", "oEP", "oEM"]

theorem sn_mem_isL : Sn.c "isL" - (Sn.c "oLF" + Sn.c "oLR" + Sn.c "oLD" + Sn.c "oLS" + Sn.c "oLM" +
    Sn.c "oLA" + Sn.c "oLZ" + Sn.c "oLX") ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_gA : Sn.c "gA" - (Sn.c "oLA" + Sn.c "oEA" + Sn.c "oLZ" + Sn.c "oEZ" + Sn.c "oLX" +
    Sn.c "oEX") ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_g2 : Sn.c "g2" - (Sn.c "oED" + Sn.c "oLX" + Sn.c "oEX") ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

open StateM5a.FieldWalk2 in
set_option maxHeartbeats 4000000 in
/-- **The linear facts of the `SN` op bundle** on an active walk row. -/
theorem sn_flags' (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1) :
    (∀ s ∈ snNames, ev tr t r pub (Sn.c s) ≤ 1) ∧
    ev tr t r pub (Sn.c "act") = 1 ∧ ev tr t r pub (Sn.c "oLS") = 0 ∧ ev tr t r pub (Sn.c "oLM") = 0 ∧
    ev tr t r pub (Sn.c "oEP") = 0 ∧ ev tr t r pub (Sn.c "oEM") = 0 ∧
    ev tr t r pub (Sn.c "mF") + ev tr t r pub (Sn.c "mU") + ev tr t r pub (Sn.c "mD") = 1 ∧
    ev tr t r pub (Sn.c "oLF") + ev tr t r pub (Sn.c "oEF") + ev tr t r pub (Sn.c "oLA") + ev tr t r pub (Sn.c "oEA") =
      ev tr t r pub (Sn.c "mF") ∧
    ev tr t r pub (Sn.c "oLR") + ev tr t r pub (Sn.c "oEU") + ev tr t r pub (Sn.c "oLX") + ev tr t r pub (Sn.c "oEX") =
      ev tr t r pub (Sn.c "mU") ∧
    ev tr t r pub (Sn.c "oLD") + ev tr t r pub (Sn.c "oED") + ev tr t r pub (Sn.c "oLZ") + ev tr t r pub (Sn.c "oEZ") +
      ev tr t r pub (Sn.c "oES") + ev tr t r pub (Sn.c "oEB") = ev tr t r pub (Sn.c "mD") ∧
    ev tr t r pub (Sn.c "isL") = ev tr t r pub (Sn.c "oLF") + ev tr t r pub (Sn.c "oLR") + ev tr t r pub (Sn.c "oLD") +
      ev tr t r pub (Sn.c "oLA") + ev tr t r pub (Sn.c "oLZ") + ev tr t r pub (Sn.c "oLX") ∧
    ev tr t r pub (Sn.c "isE") = ev tr t r pub (Sn.c "oEF") + ev tr t r pub (Sn.c "oEU") + ev tr t r pub (Sn.c "oED") +
      ev tr t r pub (Sn.c "oEA") + ev tr t r pub (Sn.c "oEZ") + ev tr t r pub (Sn.c "oES") + ev tr t r pub (Sn.c "oEB") +
      ev tr t r pub (Sn.c "oEX") ∧
    ev tr t r pub (Sn.c "gdn") = ev tr t r pub (Sn.c "oEF") + ev tr t r pub (Sn.c "oEU") + ev tr t r pub (Sn.c "oED") +
      ev tr t r pub (Sn.c "oES") + ev tr t r pub (Sn.c "oEB") ∧
    ev tr t r pub (Sn.c "gA") = ev tr t r pub (Sn.c "oLA") + ev tr t r pub (Sn.c "oEA") + ev tr t r pub (Sn.c "oLZ") +
      ev tr t r pub (Sn.c "oEZ") + ev tr t r pub (Sn.c "oLX") + ev tr t r pub (Sn.c "oEX") ∧
    ev tr t r pub (Sn.c "g2") = ev tr t r pub (Sn.c "oED") + ev tr t r pub (Sn.c "oLX") + ev tr t r pub (Sn.c "oEX") := by
  have hb : ∀ s ∈ snNames, ev tr t r pub (Sn.c s) ≤ 1 := fun s hs => sn_flag_le hc s hs
  have sub : snNames ⊆ snNames := fun _ h => h
  have S := fun (s : String) (l : List String) (h : s :: l ⊆ snNames) (hl : l.length ≤ 63) =>
    sn_sum hc s l h hl
  have e0 := S "mF" ["mU", "mD"] (by simp [snNames]) (by simp)
  have e1 := S "mF" ["mU", "mD", "oLS", "oLM", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e2 := S "oLF" ["oEF", "oLA", "oEA"] (by simp [snNames]) (by simp)
  have e3 := S "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e4 := S "oLD" ["oED", "oLZ", "oEZ", "oES", "oEB"] (by simp [snNames]) (by simp)
  have e5 := S "oLF" ["oLR", "oLD", "oLS", "oLM", "oLA", "oLZ", "oLX"] (by simp [snNames]) (by simp)
  have e6 := S "oEF" ["oEU", "oED", "oEA", "oEZ", "oES", "oEB", "oEX", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e7 := S "oEF" ["oEU", "oED", "oES", "oEB"] (by simp [snNames]) (by simp)
  have e8 := S "oLA" ["oEA", "oLZ", "oEZ", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e9 := S "oED" ["oLX", "oEX"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  have c1 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_act)
  have c2 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mF)
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  have c4 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mD)
  have c5 := eq_of_sub (hold rfl hc sn_mem_isL)
  have c6 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_isE)
  have c7 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_gdn)
  have c8 := eq_of_sub (hold rfl hc sn_mem_gA)
  have c9 := eq_of_sub (hold rfl hc sn_mem_g2)
  rw [e0] at hg
  rw [e1] at c1; rw [e2] at c2; rw [e3] at c3; rw [e4] at c4; rw [e5] at c5; rw [e6] at c6
  rw [e7] at c7; rw [e8] at c8; rw [e9] at c9
  have b0 := hb "act" (by simp [snNames]); have b1 := hb "oLS" (by simp [snNames])
  have b2 := hb "oLM" (by simp [snNames]); have b3 := hb "oEP" (by simp [snNames])
  have b4 := hb "oEM" (by simp [snNames])
  refine ⟨hb, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega⟩

end

/-- Bring the `SN` op bundle (and every flag's bound) into the context, for `omega`. -/
macro "snfacts" hc:term:max hg:term:max : tactic => `(tactic| (
  obtain ⟨hb, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := sn_flags' $hc $hg
  have := hb "act" (by simp [snNames]); have := hb "mF" (by simp [snNames]); have := hb "mU" (by simp [snNames])
  have := hb "mD" (by simp [snNames]); have := hb "isE" (by simp [snNames]); have := hb "gdn" (by simp [snNames])
  have := hb "oLF" (by simp [snNames]); have := hb "oLR" (by simp [snNames]); have := hb "oLD" (by simp [snNames])
  have := hb "oLS" (by simp [snNames]); have := hb "oLM" (by simp [snNames]); have := hb "oEF" (by simp [snNames])
  have := hb "oEU" (by simp [snNames]); have := hb "oED" (by simp [snNames]); have := hb "oLA" (by simp [snNames])
  have := hb "oEA" (by simp [snNames]); have := hb "oLZ" (by simp [snNames]); have := hb "oEZ" (by simp [snNames])
  have := hb "oES" (by simp [snNames]); have := hb "oEB" (by simp [snNames]); have := hb "oLX" (by simp [snNames])
  have := hb "oEX" (by simp [snNames]); have := hb "oEP" (by simp [snNames]); have := hb "oEM" (by simp [snNames])
  clear hb))

end StateM5a.RowSn
