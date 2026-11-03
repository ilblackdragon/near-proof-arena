import StateM5a.SnContLocX
import StateM5a.SnAssembly

/-!
# StateM5a.SnContRestAll — **`SnContRest` from `Holds`**: every continued-key walk row is `LocalOK`

For an active `SN` walk row with `cont = 1`: its old node is `gRecK kk` over the full key `kk`
(`SnContKey5.cont_old`, `ContKey`), the new node (if any) over the same key (`cont_new`,
`contKey_eq`), the depth `d ≤ 2^21` (`cont_depth`, from a key lookup at `d`), so `d + klen < P`;
then each op is the key-generic step of `SnContLocA` / `SnContLocB` / `SnContLocX`:

* `gA = 0`: `oLF`, `oEF`, `oLD` (walk key = `kk ++ …`, `contKey_drop`; leaves end at `KLEN`),
  `oLR` (new leaf memory `cont_leaf_nmem`), `oEU`, `oES`, `oEB` (`sn_mem_ebK`), `oED` (`kid2`);
* `gA = 1`: `oLA`, `oEA`, `oLZ`, `oEZ` (`cont_mismatch`), `oLX`, `oEX` (`split_keysC`).

Premises: those of `SnFinal5`'s responders (`SnMatOK`, the `oSL` rows' `NewOK` / limbs, every
`FreshRel`), `SnUpLimbs`, `Sha256CR` and the static `extra` facts.
-/

namespace StateM5a.SnContRestAll

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.RowSnM StateM5a.SnContRec1 StateM5a.SnContHead
open StateM5a.SnContKey4 StateM5a.SnContKey5 StateM5a.SnContLocA StateM5a.SnContLocB StateM5a.SnContLocX
open StateM5a.RowBrN StateM5a.SnSer

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- The op bundle of a walk row, on naturals. -/
theorem walk_arith (a b c d e f g h i j k l m n mF mU mD gA : Nat) (ba : a ≤ 1) (bb : b ≤ 1) (bc : c ≤ 1)
    (bd : d ≤ 1) (be : e ≤ 1) (bf : f ≤ 1) (bg : g ≤ 1) (bh : h ≤ 1) (bi : i ≤ 1) (bj : j ≤ 1) (bk : k ≤ 1)
    (bl : l ≤ 1) (bm : m ≤ 1) (bn : n ≤ 1) (hs : mF + mU + mD = 1) (hF : a + b + c + d = mF)
    (hU : e + f + g + h = mU) (hD : i + j + k + l + m + n = mD) (hgA : gA = c + d + k + l + g + h) :
    ((a = 1 ∨ b = 1 ∨ e = 1 ∨ f = 1 ∨ i = 1 ∨ j = 1 ∨ m = 1 ∨ n = 1) → gA = 0) ∧
    ((c = 1 ∨ d = 1 ∨ k = 1 ∨ l = 1) → gA = 1) ∧ (n = 1 → f = 0) ∧
    (a = 1 ∨ b = 1 ∨ c = 1 ∨ d = 1 ∨ e = 1 ∨ f = 1 ∨ g = 1 ∨ h = 1 ∨ i = 1 ∨ j = 1 ∨ k = 1 ∨ l = 1 ∨
      m = 1 ∨ n = 1) := by
  omega

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 8000000 in
/-- **The depth of a continued walk row** is a key position (or a key's end): `d ≤ 2^21`. -/
theorem cont_depth (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) {r : Nat} (hr : r < tr.height 3)
    (hg : snW.g.eval tr 3 r pub = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 1) :
    ev tr 3 r pub (Sn.c "d") ≤ 2 ^ 21 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := eval_one_ev hg
  have hd := SnDepthAll.sn_depth_all hH hN hL r hr hg
  have hkey := RowFacts.keyOf_bounds hH
  obtain ⟨hb, -, -, -, -, -, hs, hF, hU, hD, -, -, -, hgA, -⟩ := sn_flags' hc hg'
  obtain ⟨-, h2, -, -⟩ := walk_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hb "oLF" (by simp [snNames]))
    (hb "oEF" (by simp [snNames])) (hb "oLA" (by simp [snNames])) (hb "oEA" (by simp [snNames]))
    (hb "oLR" (by simp [snNames])) (hb "oEU" (by simp [snNames])) (hb "oLX" (by simp [snNames]))
    (hb "oEX" (by simp [snNames])) (hb "oLD" (by simp [snNames])) (hb "oED" (by simp [snNames]))
    (hb "oLZ" (by simp [snNames])) (hb "oEZ" (by simp [snNames])) (hb "oES" (by simp [snNames]))
    (hb "oEB" (by simp [snNames])) hs hF hU hD hgA
  have bgA : ev tr 3 r pub (Sn.c "gA") ≤ 1 := by
    have := hb "oLA" (by simp [snNames]); have := hb "oEA" (by simp [snNames])
    have := hb "oLZ" (by simp [snNames]); have := hb "oEZ" (by simp [snNames])
    have := hb "oLX" (by simp [snNames]); have := hb "oEX" (by simp [snNames])
    clear hb h2
    generalize ev tr 3 r pub (Sn.c "mF") = x1 at *
    generalize ev tr 3 r pub (Sn.c "mU") = x2 at *
    generalize ev tr 3 r pub (Sn.c "mD") = x3 at *
    omega
  clear h2
  rcases (by omega : ev tr 3 r pub (Sn.c "gA") = 0 ∨ ev tr 3 r pub (Sn.c "gA") = 1) with hA0 | hA1
  · have hb0 : ev tr 3 r pub (Sn.b 0) = 1 := by
      rw [sn_b_eq_a hc hA0 0 (by decide), ch_a hc hcont 0]; rfl
    have := (sn_nib hH hN 0 (by decide) hr (ev_one_eval hb0)).2
    rw [SnDepthAll.ev_d0 (e := K 0) (ev_const 0)] at this
    omega
  · obtain ⟨hj64, -⟩ := sn_jm hc hA1
    have bN := bool_le (FieldRows2.sn_hold hc (sn_bool' "mN" (by simp)))
    have bK := bool_le (FieldRows2.sn_hold hc (sn_bool' "mK" (by simp)))
    have hL0 : ev tr 3 r pub (Sn.c "mL") = 0 := by
      have h := FieldRows2.sn_hold hc (e := Sn.c "mL" * Sn.c "cont") (by unfold Sn.constraints; simp)
      rw [ev_hmul, hcont, Nat.mul_one, Nat.mod_eq_of_lt (ev_lt _)] at h
      exact h
    have m1 := eq_of_sub (FieldRows2.sn_hold hc sn_mem_m1)
    rw [ev_hadd, ev_hadd, hA1, hL0, Nat.mod_eq_of_lt (by omega), Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at m1
    have hdj : ev tr 3 r pub (Sn.c "d" + Sn.c "jm") = ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "jm") := by
      rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]
    rcases (by omega : ev tr 3 r pub (Sn.c "mN") = 1 ∨ ev tr 3 r pub (Sn.c "mK") = 1) with h | h
    · have := (sn_nib_mis hH hN hr (ev_one_eval (by rw [ev_hadd, hL0, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; exact h))).2
      rw [hdj] at this; omega
    · have := sn_klen_mK hH hL hr (ev_one_eval h)
      unfold KlenAt at this
      rw [hdj] at this
      have := (hkey (ev tr 3 r pub (Sn.c "kid"))).2
      omega

end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
  (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SPQ = false)
  (hxMQ : ∀ T ∈ extra, sendsOn T.interactions B_MATQ = false)
  (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false)
  (hxP : ∀ T ∈ extra, sendsOn T.interactions B_SPR = false)
  (hxE : ∀ T ∈ extra, sendsOn T.interactions B_EPQ = false)
  (hxSQ : ∀ T ∈ extra, sendsOn T.interactions B_SXQ = false)
  (hxSR : ∀ T ∈ extra, sendsOn T.interactions B_SXR = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
  (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)
  (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)
  (hxU : ∀ T ∈ extra, sendsOn T.interactions B_UP = false)
  (hCR : Walk.Sha256CR) (hSU : SnUpLimbs tr pub)
  {σ : Store} (hS : SnMatOK σ (keyOf tr) tr pub)
  (hBnew : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → NewOK σ (brOut tr pub r) (brNew tr pub r))
  (hBlim : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → ∀ k, k < 4 →
    ev tr 2 r pub (Br.NM.getD k 0) < 65536 ∧ ev tr 2 r pub (Br.c "nm" k) < 65536 ∧
    ev tr 2 r pub (Br.c "nm2" k) < 65536)
  (hF : ∀ p, p < tr.height 3 → (ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) →
    FreshRel σ (keyOf tr) tr pub p)
include hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hxSQ hxSR hxr hxB hxD hxRr hxV hxU hCR hSU hS hBnew
  hBlim hF

set_option maxHeartbeats 16000000 in
/-- **`SnContRest` from `Holds`.** -/
theorem snContRest_of : SnFinal5.SnContRest σ (keyOf tr) tr pub := by
  intro r hr hg hcont
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := eval_one_ev hg
  obtain ⟨hb, hA, -, hLM, hEP, hEM, hs, hF', hU, hD', -, -, -, hgA, -⟩ := sn_flags' hc hg'
  obtain ⟨hz, ho1, hEBU, hcov⟩ := walk_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hb "oLF" (by simp [snNames]))
    (hb "oEF" (by simp [snNames])) (hb "oLA" (by simp [snNames])) (hb "oEA" (by simp [snNames]))
    (hb "oLR" (by simp [snNames])) (hb "oEU" (by simp [snNames])) (hb "oLX" (by simp [snNames]))
    (hb "oEX" (by simp [snNames])) (hb "oLD" (by simp [snNames])) (hb "oED" (by simp [snNames]))
    (hb "oLZ" (by simp [snNames])) (hb "oEZ" (by simp [snNames])) (hb "oES" (by simp [snNames]))
    (hb "oEB" (by simp [snNames])) hs hF' hU hD' hgA
  clear hb hs hF' hU hD' hgA
  -- the old node over the full key, the depth
  obtain ⟨kk, hK, hold, -, hmb⟩ := cont_old hH hxB hxD hxK hxR hxRr hxN hxr hCR σ hr hcont
    (SnFinal4.gold_of hc hA hLM hEP hEM)
  obtain ⟨hkl, hev, hrl, hpl, hod⟩ := cont_klen hH hxK hxR hr hA hcont
  have hdep := cont_depth hH hxN hxL hr hg hcont
  have hdk : ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") < P := by rw [hkl]; omega
  have hKl := hK.len
  have hklen : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1 →
      (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "klen") :=
    fun h => sn_klen_leaf hH hxL hr h
  have hM : ∀ k, k < 4 → ev tr 3 r pub (Sn.M.getD k 0) < 65536 := fun k hk => by
    rw [SnRange.M_get k hk]; exact SnRange.limbs_of_bytes hmb k hk
  -- the mismatch (`gA = 1`)
  have hmis := fun (hA1 : ev tr 3 r pub (Sn.c "gA") = 1) =>
    cont_mismatch (keyOf := keyOf tr) hc hcont hA1 (SnDepthAll.sn_depth_all hH hxN hxL r hr hg) hK.head
      (by rw [hKl, hkl]; omega) (fun h => (sn_nib_mis hH hxN hr h).1) (fun h => sn_klen_mK hH hxL hr h)
  -- the new node, over the same key (`gA = 0`)
  have hnew : ev tr 3 r pub (Sn.c "gA") = 0 → ev tr 3 r pub (Sn.c "gnew") = 1 →
      NewOK σ (snOut tr pub r) (gRecK tr pub r kk (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b)) ∧
      (∀ t, t < payLen tr pub r → ev tr 3 r pub (Sn.c "nx" t) < 256) ∧
      (∀ b, b < 8 → ev tr 3 r pub (Sn.c "nmem" b) < 256) := by
    intro hA0 hgn
    obtain ⟨kk', hK', hn, hp, hm⟩ := cont_new hH hxB hxD hxK hxR hxRr hxN hxr hCR σ hr hcont hgn
    rw [contKey_eq hK hK' hA0]
    exact ⟨hn, hp, hm⟩
  have hNM : (∀ b, b < 8 → ev tr 3 r pub (Sn.c "nmem" b) < 256) →
      ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536 := fun h k hk => by
    rw [SnRange.NM_get k hk]; exact SnRange.limbs_of_bytes h k hk
  rcases hcov with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- oLF
    have hA0 := hz (Or.inl h)
    exact localOK_oLF_K hc hg' hKl hdk hold h (contKey_drop hK hA0) hklen
  · -- oEF
    have hA0 := hz (Or.inr (Or.inl h))
    exact localOK_oEF_K hc hg' hKl hdk hold h (contKey_drop hK hA0)
  · -- oLA
    obtain ⟨m1, m2⟩ := hmis (ho1 (Or.inl h))
    exact localOK_oLA_K hc hg' hKl hdk hold m1 h
  · -- oEA
    obtain ⟨m1, m2⟩ := hmis (ho1 (Or.inr (Or.inl h)))
    exact localOK_oEA_K hc hg' hKl hdk hold m1 m2 h
  · -- oLR
    have hA0 := hz (Or.inr (Or.inr (Or.inl h)))
    have hgn := SnLimbsAll.gnew_of hc (Or.inl rfl) h
    obtain ⟨hn, hp, hm⟩ := hnew hA0 hgn
    have hLM' : ev tr 3 r pub (Sn.c "oLR" + Sn.c "oLM") = 1 := by rw [ev_hadd, h, hLM]
    have hisL : ev tr 3 r pub (Sn.c "isL") = 1 := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, h5, -⟩ := sn_flags' hc hg'
      rw [h5]; snfacts hc hg'; omega
    have hpay : payLen tr pub r = 36 := by rw [SnContSer2.payLen_eq, hisL]
    have hnx : ∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256 := fun t ht => hp t (by omega)
    obtain ⟨hmem, hlt⟩ := cont_leaf_nmem hc hLM' hm hnx (by omega)
    have hlm : snNMem tr pub r = leafMem kk (ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t)) := by
      rw [hmem]; unfold leafMem; rw [contKey_hp hK true hkl hev hpl hod]; omega
    exact localOK_oLR_K hc hg' h hKl hdk hold (contKey_drop hK hA0) hklen hn hlm (hNM hm) hlt hnx
  · -- oEU
    have hA0 := hz (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have hgn := SnLimbsAll.gnew_of hc (Or.inr (Or.inr (Or.inl rfl))) h
    obtain ⟨hn, -, hm⟩ := hnew hA0 hgn
    obtain ⟨hgd, he⟩ := SnAssembly.gdn_of hc hg' (Or.inl h)
    have hun := SnAssembly.sn_unom_lt hH hxB hxD hxK hxr hxV hxU hSU hr hgd
    exact localOK_oEU_K hc hg' h hKl hdk hold (contKey_drop hK hA0) hn hM (hNM hm)
      (fun k hk => by have := (hun k hk).1; rwa [ev_gm he] at this) (fun k hk => (hun k hk).2)
  · -- oLX
    exact localOK_oLX_K hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hS hBnew hBlim hF hr
      (SnFinal5.gX_of_split hc hg' (Or.inl h)) h hcont hK hold
  · -- oEX
    exact localOK_oEX_K hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hxSQ hxSR hxr hS hBnew hBlim hF hr
      (SnFinal5.gX_of_split hc hg' (Or.inr h)) h hcont hK hold hM
  · -- oLD
    have hA0 := hz (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    exact localOK_oLD_K hc hg' hKl hdk hold h (contKey_drop hK hA0) hklen
  · -- oED
    exact localOK_oED_K hc hg' hKl hdk hold (contKey_drop hK (hz (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      h (fun hg2 => contKey_drop2 hK hg2) (RowFacts.keyOf_bounds hH)
  · -- oLZ
    obtain ⟨m1, m2⟩ := hmis (ho1 (Or.inr (Or.inr (Or.inl h))))
    exact localOK_oLZ_K hc hg' hKl hdk hold m1 h
  · -- oEZ
    obtain ⟨m1, m2⟩ := hmis (ho1 (Or.inr (Or.inr (Or.inr h))))
    exact localOK_oEZ_K hc hg' hKl hdk hold m1 m2 h
  · -- oES
    have hA0 := hz (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    exact localOK_oES_K hc hg' hKl hdk hold (contKey_drop hK hA0) h
  · -- oEB
    have hA0 := hz (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    have hgn := SnLimbsAll.gnew_of hc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
    obtain ⟨hn, -, hm⟩ := hnew hA0 hgn
    obtain ⟨hgd, he⟩ := SnAssembly.gdn_of hc hg' (Or.inr h)
    have hun := SnAssembly.sn_unom_lt hH hxB hxD hxK hxr hxV hxU hSU hr hgd
    have hu : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "unm" k) < 65536 :=
      fun k hk => by have := (hun k hk).1; rwa [ev_gm he] at this
    have hF1 : ev tr 3 r pub (Sn.c "gfr") = 1 := by
      rw [eq_of_sub (FieldRows2.sn_hold hc sn_mem_gfr), ev_hadd, ev_hadd, h, hEP, hEM]
    have eG : ev tr 3 r pub (Sn.c "oEU" + Sn.c "gfr") = 1 := by rw [ev_hadd, hF1, hEBU h]
    obtain ⟨hown, hown'⟩ := SnContResp.ev_ownK (contKey_hp hK false hkl hev hpl hod) (by omega)
    have hmem := SnContResp.sn_mem_ebK hc hown hown' eG hF1 (hNM hm) hu
    exact localOK_oEB_K hc hg' hKl hdk hold (contKey_drop hK hA0) h hn hmem (hNM hm) hu

end

end StateM5a.SnContRestAll
