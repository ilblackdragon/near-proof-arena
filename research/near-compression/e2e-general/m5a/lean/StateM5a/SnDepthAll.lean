import StateM5a.RowSnAll2

/-!
# StateM5a.SnDepthAll — `RowSnAll.SnDepth` from `Holds`

Every active `SN` walk row's depth is `≤ 2^21` (so `d + 64 < P`), from one of its key lookups:

* `b₀ = 1`: its first key nibble is looked up on `NIB` at `d` (a key position, `< 2^21`);
* `b₀ = 0`, `gA = 0`: then `a₀ = 0`, so the key is empty (`klen = 0`, no continuation) and the
  row is a leaf (`isE·(1 − a₀) = 0`) whose `KLEN` lookup puts the walk key's end at `d`;
* `b₀ = 0`, `gA = 1`: the mismatch is at `jm = 0`: a `NIB` lookup (`mN`/`mL`) or the `KLEN` lookup
  (`mK`) at `d`.
-/

namespace StateM5a.SnDepthAll

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM StateM5a.KeyDecode StateM5a.KeyLookups StateM5a.RowSnAll StateM5a.RowSnN

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem sn_mem_ea0 : Sn.c "isE" * (1 - Sn.a 0) ∈ Sn.constraints := by unfold Sn.constraints; simp
theorem sn_mem_ca61 : Sn.c "cont" * (1 - Sn.a 61) ∈ Sn.constraints := by unfold Sn.constraints; simp

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem ev_x_one_sub {x y : Expr} (h : ev tr 3 r pub (x * (1 - y)) = 0) (hy : ev tr 3 r pub y = 0) :
    ev tr 3 r pub x = 0 := by
  rw [ev_hmul, FieldRows2.ev_one_sub0 hy, Nat.mul_one, Nat.mod_eq_of_lt (ev_lt _)] at h; exact h

theorem ev_d0 {e : Expr} (h0 : ev tr 3 r pub e = 0) : ev tr 3 r pub (Sn.c "d" + e) = ev tr 3 r pub (Sn.c "d") := by
  rw [ev_hadd, h0, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]

end

set_option maxHeartbeats 4000000 in
/-- **`SnDepth` from `Holds`.** -/
theorem sn_depth_all {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) : SnDepth tr pub := by
  intro r hr hg
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := eval_one_ev hg
  suffices h : ev tr 3 r pub (Sn.c "d") ≤ 2 ^ 21 by omega
  have hb0 := sn_b_bool hc 0 (by decide)
  have hkey := RowFacts.keyOf_bounds hH
  rcases (by omega : ev tr 3 r pub (Sn.c "b" 0) = 1 ∨ ev tr 3 r pub (Sn.c "b" 0) = 0) with h1 | h0
  · have := (sn_nib hH hN 0 (by decide) hr (fp_of_ev1 (by rw [sn_b_lt 0 (by decide)]; exact h1))).2
    rw [ev_d0 (e := K 0) (ev_const 0)] at this
    omega
  · obtain ⟨hb, -, -, -, -, -, hs, hF, hU, hD, hisL, hisE, -, hgA, -⟩ := sn_flags' hc hg'
    have bgA : ev tr 3 r pub (Sn.c "gA") ≤ 1 := by clear hb; omega
    rcases (by omega : ev tr 3 r pub (Sn.c "gA") = 0 ∨ ev tr 3 r pub (Sn.c "gA") = 1) with hA0 | hA1
    · have ha0 : ev tr 3 r pub (Sn.c "a" 0) = 0 := by
        rw [← FieldRows2.sn_a_lt 0 (by decide), ← sn_b_eq_a hc hA0 0 (by decide), sn_b_lt 0 (by decide)]
        exact h0
      obtain ⟨-, hf⟩ := FieldRows2.prefix_flags (fun j => ev tr 3 r pub (Sn.c "a" j)) 64
        (fun j hj => FieldRows2.sn_a_bool hc j hj) (fun j hj h1 => FieldRows2.sn_a_mono hc j hj h1)
      have hf0 := hf 0 (by decide)
      have hf61 := hf 61 (by decide)
      have ha61 : ev tr 3 r pub (Sn.c "a" 61) = 0 := by
        rw [hf61]; rw [ha0] at hf0; split at hf0 <;> split <;> omega
      have hcont : ev tr 3 r pub (Sn.c "cont") = 0 :=
        ev_x_one_sub (FieldRows2.sn_hold hc sn_mem_ca61) (by rw [FieldRows2.sn_a_lt 61 (by decide)]; exact ha61)
      have hkl := FieldRows2.sn_flags hc hcont
      have hk0 : ev tr 3 r pub (Sn.c "klen") = 0 := by
        have := hkl.2 0 (by decide); rw [ha0] at this; split at this <;> omega
      have hisE0 : ev tr 3 r pub (Sn.c "isE") = 0 :=
        ev_x_one_sub (FieldRows2.sn_hold hc sn_mem_ea0) (by rw [FieldRows2.sn_a_lt 0 (by decide)]; exact ha0)
      have hisL1 : ev tr 3 r pub (Sn.c "isL") = 1 := by clear hb; omega
      have hk := sn_klen_leaf hH hL hr (fp_of_ev1 (by rw [ev_hmul, hisL1, FieldRows2.ev_one_sub0 hA0]))
      have hk' : (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d") := by
        rw [← ev_d0 hk0]; exact hk
      have := (hkey (ev tr 3 r pub (Sn.c "kid"))).2
      omega
    · obtain ⟨-, hbf, -, -⟩ := sn_jm hc hA1
      have hjm0 : ev tr 3 r pub (Sn.c "jm") = 0 := by
        have := hbf 0 (by decide); rw [h0] at this; split at this <;> omega
      have hm := eq_of_sub (FieldRows2.sn_hold hc sn_mem_m1)
      have bN := bool_le (FieldRows2.sn_hold hc (sn_bool' "mN" (by simp)))
      have bK := bool_le (FieldRows2.sn_hold hc (sn_bool' "mK" (by simp)))
      have bL := bool_le (FieldRows2.sn_hold hc (sn_bool' "mL" (by simp)))
      rw [ev_hadd, ev_hadd, hA1] at hm
      rcases (by omega : ev tr 3 r pub (Sn.c "mN") + ev tr 3 r pub (Sn.c "mL") = 1 ∨
          ev tr 3 r pub (Sn.c "mK") = 1) with h | h
      · have := (sn_nib_mis hH hN hr (fp_of_ev1 (by rw [ev_hadd]; omega))).2
        rw [ev_d0 hjm0] at this
        omega
      · have hk : (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d") := by
          rw [← ev_d0 hjm0]; exact sn_klen_mK hH hL hr (fp_of_ev1 h)
        have := (hkey (ev tr 3 r pub (Sn.c "kid"))).2
        omega

end StateM5a.SnDepthAll
