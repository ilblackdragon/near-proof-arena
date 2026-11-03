import StateM5a.RowSnM

/-!
# StateM5a.RowSnD — `LocalOK` of the `SN` delete rows `oLD` (leaf delete) and `oES`
(extension over an unchanged child)

* `localOK_oLD`: the walk key ends at this leaf (`NONE`), via `BusWalk.step_leafDel`;
* (`oES`, via `BusWalk.step_extSame`, did not elaborate in reasonable time and is left to
  `RowSnAll.SnRest`.)
-/

namespace StateM5a.RowSnD

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem sn_mem_rkS : Sn.c "oES" * (Sn.c "rkc" - K RK_SAME) ∈ Sn.constraints := by
  unfold Sn.constraints; simp

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp} {σ : Store} {keyOf : Nat → List Nat}
  (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
  (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1)
  (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
  (hnib : ∀ j < 64, (Sn.b j).eval tr 3 r pub = 1 →
    (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)))
  (hold : OldOK σ (snIn tr pub r) (snOld tr pub r))
include hc hg hcont hd hnib hold

set_option maxHeartbeats 4000000 in
/-- **`SN.oLD`**: delete at the leaf holding the key (`NONE`). -/
theorem localOK_oLD
    (hklen : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "klen"))
    (h1 : ev tr 3 r pub (Sn.c "oLD") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have eIsL : (Sn.c "isL").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_NONE := by
    have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have a3 : (Sn.c "oED").eval tr 3 r pub = 0 := s0
    have a4 : (Sn.c "oLD").eval tr 3 r pub = 1 := s1
    have a5 : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    have a8 : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
    have a9 : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
    have a10 : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    rw [ev_eq_of_eval (b := K RK_NONE) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_NONE]
  have hK := sn_key_prefix hc hcont (ev_of_eval eGA) hd hnib
  have hlen := hklen (by evsn; grind)
  rw [ev_hadd, Nat.mod_eq_of_lt (by
    have := (FieldRows2.sn_flags hc hcont).1; omega)] at hlen
  rw [List.drop_eq_nil_of_le (show (keyOf (ev tr 3 r pub (Sn.c "kid"))).length ≤
    ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") by omega), List.append_nil] at hK
  rw [snOld_leaf (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  refine step_leafDel hold hK hrk ?_
  show le4 _ = le4 _
  rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]

end

end StateM5a.RowSnD
