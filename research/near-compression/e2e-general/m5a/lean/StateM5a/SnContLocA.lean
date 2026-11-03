import StateM5a.SnContKey5
import StateM5a.RowSnD

/-!
# StateM5a.SnContLocA — `LocalOK` of the find / leaf-delete / absent ops over any node key

The `RowSnF` / `RowSnM` / `RowSnD` proofs with the head key `snKey` replaced by a key `K` given
with the facts the steps use (so they apply to a continued head, `K` its full key, `SnContKey5`):

* the old record is `gRecK K` (`OldOK σ snIn`), `|K| = klen`, `d + klen < P`;
* `gA = 0` ops (`oLF`, `oEF`, `oLD`): the walk key from `d` starts with `K` (`hKd`);
* `gA = 1` ops (`oLA`, `oEA`, `oLZ`, `oEZ`): the mismatch `kk[jm] ≠ K_kid[d + jm]` (`hmis`, with
  `jm < |K|` on an extension); **`cont_mismatch`** derives it on a continued head (the mismatch is
  in the head: `ajm = 1` puts `jm < 62 + odd`, where `K` is the head's cells; `mL·cont = 0`).
-/

namespace StateM5a.SnContLocA

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM StateM5a.RowSnD StateM5a.RowSnN StateM5a.SnContRec1 StateM5a.SnContKey4 StateM5a.SnContHead

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp} {kk : List Nat}

theorem gRecK_leaf (h : ev tr 3 r pub (Sn.c "isL") = 1) :
    gRecK tr pub r kk (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b) =
      .leaf kk (snVal tr pub r) (snMem tr pub r) := by
  unfold gRecK; rw [if_pos h]; rfl
theorem gRecK_ext (h : ev tr 3 r pub (Sn.c "isL") ≠ 1) :
    gRecK tr pub r kk (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b) =
      .ext kk (snChild tr pub r) (snMem tr pub r) := by
  unfold gRecK; rw [if_neg h]; rfl
theorem gRecK_nleaf (h : ev tr 3 r pub (Sn.c "isL") = 1) :
    gRecK tr pub r kk (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b) =
      .leaf kk (snNVal tr pub r) (snNMem tr pub r) := by
  unfold gRecK; rw [if_pos h]; rfl
theorem gRecK_next (h : ev tr 3 r pub (Sn.c "isL") ≠ 1) :
    gRecK tr pub r kk (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b) =
      .ext kk (snNChild tr pub r) (snNMem tr pub r) := by
  unfold gRecK; rw [if_neg h]; rfl

theorem ev_dkl (hdk : ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") < P) :
    ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") := by
  rw [ev_hadd, Nat.mod_eq_of_lt hdk]

end

/-! ## The mismatch of a continued head -/

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem af_one (O j : Nat) (h : af O j = 1) (hO : O ≤ 1) : j < 62 + O := by
  unfold af at h; (repeat' split at h) <;> omega

set_option maxHeartbeats 4000000 in
/-- **The mismatch of a continued head** lies in the head: `kk[jm] ≠ K_kid[d + jm]`, `jm < |K|`. -/
theorem cont_mismatch {keyOf : Nat → List Nat} {kk : List Nat}
    (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 1) (hA : ev tr 3 r pub (Sn.c "gA") = 1)
    (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hhead : ∀ j, j < 62 + ev tr 3 r pub (Sn.c "odd") → kk[j]? = some (ev tr 3 r pub (Sn.c "k" j)))
    (hKl : 62 + ev tr 3 r pub (Sn.c "odd") ≤ kk.length)
    (hmisN : (Sn.c "mN" + Sn.c "mL").eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + Sn.c "jm")]? = some (ev tr 3 r pub (Sn.c "y")))
    (hmisK : (Sn.c "mK").eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "jm")) :
    kk[ev tr 3 r pub (Sn.c "jm")]? ≠
      ((keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")))[ev tr 3 r pub (Sn.c "jm")]? ∧
    ev tr 3 r pub (Sn.c "jm") < kk.length := by
  obtain ⟨hj64, -, hkj, hajm⟩ := sn_jm hc hA
  have ho := FieldRows2.sn_bool hc "odd" (by simp)
  have bN := bool_le (FieldRows2.sn_hold hc (sn_bool' "mN" (by simp)))
  have bK := bool_le (FieldRows2.sn_hold hc (sn_bool' "mK" (by simp)))
  have bL := bool_le (FieldRows2.sn_hold hc (sn_bool' "mL" (by simp)))
  have hL0 : ev tr 3 r pub (Sn.c "mL") = 0 := by
    have h := FieldRows2.sn_hold hc (e := Sn.c "mL" * Sn.c "cont") (by unfold Sn.constraints; simp)
    rw [ev_hmul, hcont, Nat.mul_one, Nat.mod_eq_of_lt (ev_lt _)] at h
    exact h
  have m1 := eq_of_sub (FieldRows2.sn_hold hc sn_mem_m1)
  rw [ev_hadd, ev_hadd, hA, hL0, Nat.mod_eq_of_lt (by omega), Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at m1
  have hNK : ev tr 3 r pub (Sn.c "mN" + Sn.c "mK") = 1 := by rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; exact m1
  have ha := FieldWsb.wsb_gate hNK (FieldRows2.sn_hold hc sn_mem_m2)
  rw [ev_sub, ev_one] at ha
  have hajm1 : ev tr 3 r pub (Sn.c "ajm") = 1 := by
    have := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.c "ajm"); omega
  have haj := ch_a hc hcont (ev tr 3 r pub (Sn.c "jm"))
  rw [FieldRows2.sn_a_lt _ hj64, ← hajm, hajm1] at haj
  have hjlt := af_one _ _ haj.symm ho
  have hKj : kk[ev tr 3 r pub (Sn.c "jm")]? = some (ev tr 3 r pub (Sn.c "kj")) := by
    rw [hhead _ hjlt, hkj]
  have hdj : ev tr 3 r pub (Sn.c "d" + Sn.c "jm") = ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "jm") := by
    rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]
  rw [hdj] at hmisN hmisK
  have hdrop : ((keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")))[ev tr 3 r pub (Sn.c "jm")]? =
      (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "jm")]? :=
    List.getElem?_drop
  refine ⟨?_, by omega⟩
  rw [hKj, hdrop]
  rcases (by omega : ev tr 3 r pub (Sn.c "mN") = 1 ∨ ev tr 3 r pub (Sn.c "mK") = 1) with h | h
  · have hy := hmisN (ev_one_eval (by rw [ev_hadd, hL0, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; exact h))
    have hne := FieldRows.sn_mismatch_ne hc h
    rw [hy]
    intro e; exact hne (Option.some.inj e).symm
  · have hl := hmisK (ev_one_eval h)
    rw [List.getElem?_eq_none (by omega)]
    simp

end

/-! ## Find, leaf delete, absent ops over a key `K` -/

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp} {σ : Store} {keyOf : Nat → List Nat} {kk : List Nat}
  (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
  (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1)
  (hKl : kk.length = ev tr 3 r pub (Sn.c "klen"))
  (hdk : ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") < P)
  (hold : OldOK σ (snIn tr pub r) (gRecK tr pub r kk (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b)))
include hc hg hKl hdk hold

set_option maxHeartbeats 4000000 in
/-- **`SN.oLF`** over a key `K`. -/
theorem localOK_oLF_K (h1 : ev tr 3 r pub (Sn.c "oLF") = 1)
    (hKd : (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")) =
      kk ++ (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")))
    (hklen : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "klen")) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLF : (Sn.c "oLF").eval tr 3 r pub = 1 := s1
  have eEF : (Sn.c "oEF").eval tr 3 r pub = 0 := s0
  have eED : (Sn.c "oED").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have eIsL : (Sn.c "isL").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 0 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 0
    rw [show Sn.mode.eval tr 3 r pub = 0 by evsn; grind]; rfl
  have hK := hKd
  have hlen := hklen (by evsn; grind)
  rw [ev_dkl hdk] at hlen
  rw [List.drop_eq_nil_of_le (show (keyOf (ev tr 3 r pub (Sn.c "kid"))).length ≤
    ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") by omega), List.append_nil] at hK
  rw [gRecK_leaf (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  refine step_leafHit (k := kk) (m := snMem tr pub r) ?_ hK ?_
  · have e2 : snVal tr pub r = .ref (ev tr 3 r pub (Sn.c "oLF" * Sn.vlenOf (fun t => Sn.c "x" t) +
        (Sn.c "oEF" + Sn.c "oED") * Sn.c "alen"))
        (bytesOf (((pack2 fun b => Sn.c "x" (4 + b)).zip ((List.range 16).map fun i => Sn.c "avh" i)).map
          (fun (p, q) => Sn.c "oLF" * p + (Sn.c "oEF" + Sn.c "oED") * q) |>.map (E tr 3 r pub))) := by
      unfold snVal
      rw [map_zip_left (Sn.c "oLF") (Sn.c "oEF" + Sn.c "oED") (fun p => p) _ eLF (by evsn; grind) _
        (by simp [pack2])]
      congr 1
      apply ev_eq_of_eval; evsn; grind
    rw [e2] at hold
    exact hold
  · exact eval_one_ev (by evsn; grind)

set_option maxHeartbeats 4000000 in
/-- **`SN.oEF`** over a key `K`. -/
theorem localOK_oEF_K (h1 : ev tr 3 r pub (Sn.c "oEF") = 1)
    (hKd : (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")) =
      kk ++ (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen"))) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLF : (Sn.c "oLF").eval tr 3 r pub = 0 := s0
  have eEF : (Sn.c "oEF").eval tr 3 r pub = 1 := s1
  have eED : (Sn.c "oED").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 0 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 0
    rw [show Sn.mode.eval tr 3 r pub = 0 by evsn; grind]; rfl
  have hK := hKd
  have hkl : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + kk.length := by
    rw [hKl, ev_dkl hdk]
  rw [← hKl] at hK
  rw [gRecK_ext (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_pos (show snW.gdn.eval tr 3 r pub = 1 from eGdn)]
  dsimp only
  rw [sn_din, sn_dout, sn_uin, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, hkl]
  intro hch
  refine step_extFind hold hK ?_ ?_ ?_ hch
  · apply ev_eq_of_eval; evsn; grind
  · apply ev_eq_of_eval; evsn; grind
  · show bytesOf _ = bytesOf _
    rw [map_zip_right (Sn.c "oLF") (Sn.c "oEF" + Sn.c "oED") (fun p => p) _ eLF (by evsn; grind) _
      (by simp [pack2]), map_gate (Sn.c "oEF" + Sn.c "oED") (fun i => Sn.c "avh" i) (by evsn; grind),
      List.map_map]
    rfl

set_option maxHeartbeats 4000000 in
/-- **`SN.oLD`** over a key `K`. -/
theorem localOK_oLD_K (h1 : ev tr 3 r pub (Sn.c "oLD") = 1)
    (hKd : (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")) =
      kk ++ (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")))
    (hklen : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "klen")) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
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
  have hK := hKd
  have hlen := hklen (by evsn; grind)
  rw [ev_dkl hdk] at hlen
  rw [List.drop_eq_nil_of_le (show (keyOf (ev tr 3 r pub (Sn.c "kid"))).length ≤
    ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") by omega), List.append_nil] at hK
  rw [gRecK_leaf (by omega)] at hold
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

variable (hmis : kk[ev tr 3 r pub (Sn.c "jm")]? ≠
      ((keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")))[ev tr 3 r pub (Sn.c "jm")]?)
  (hjK : ev tr 3 r pub (Sn.c "jm") < kk.length)
include hmis

set_option maxHeartbeats 4000000 in
/-- **`SN.oLA`** over a key `K`. -/
theorem localOK_oLA_K (h1 : ev tr 3 r pub (Sn.c "oLA") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLF : (Sn.c "oLF").eval tr 3 r pub = 0 := s0
  have eEF : (Sn.c "oEF").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 0 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 0
    rw [show Sn.mode.eval tr 3 r pub = 0 by evsn; grind]; rfl
  rw [gRecK_leaf (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  exact step_leafMiss hold hmis (ev_of_eval (by evsn; grind))

include hjK in
set_option maxHeartbeats 4000000 in
/-- **`SN.oEA`** over a key `K`. -/
theorem localOK_oEA_K (h1 : ev tr 3 r pub (Sn.c "oEA") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLF : (Sn.c "oLF").eval tr 3 r pub = 0 := s0
  have eEF : (Sn.c "oEF").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 0 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 0
    rw [show Sn.mode.eval tr 3 r pub = 0 by evsn; grind]; rfl
  rw [gRecK_ext (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  exact step_extMiss hold hjK hmis (ev_of_eval (by evsn; grind))

set_option maxHeartbeats 4000000 in
/-- **`SN.oLZ`** over a key `K`. -/
theorem localOK_oLZ_K (h1 : ev tr 3 r pub (Sn.c "oLZ") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eS : Sn.gS.eval tr 3 r pub = 1 := by
    have : (Sn.c "oLZ").eval tr 3 r pub = 1 := s1
    have : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    evsn; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_SAME := by
    have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have a3 : (Sn.c "oED").eval tr 3 r pub = 0 := s0
    have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
    have a5 : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    have a8 : (Sn.c "oLZ").eval tr 3 r pub = 1 := s1
    have a9 : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
    have a10 : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    rw [ev_eq_of_eval (b := K RK_SAME) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_SAME]
  rw [gRecK_leaf (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  refine step_leafAbs hold hmis hrk (same_ref eNu eS eX) ?_
  show le4 _ = le4 _
  rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]

include hjK in
set_option maxHeartbeats 4000000 in
/-- **`SN.oEZ`** over a key `K`. -/
theorem localOK_oEZ_K (h1 : ev tr 3 r pub (Sn.c "oEZ") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eS : Sn.gS.eval tr 3 r pub = 1 := by
    have : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEZ").eval tr 3 r pub = 1 := s1
    have : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    evsn; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_SAME := by
    have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have a3 : (Sn.c "oED").eval tr 3 r pub = 0 := s0
    have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
    have a5 : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    have a8 : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
    have a9 : (Sn.c "oEZ").eval tr 3 r pub = 1 := s1
    have a10 : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    rw [ev_eq_of_eval (b := K RK_SAME) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_SAME]
  rw [gRecK_ext (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  refine step_extAbs hold hjK hmis hrk (same_ref eNu eS eX) ?_
  show le4 _ = le4 _
  rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]

end

end StateM5a.SnContLocA
