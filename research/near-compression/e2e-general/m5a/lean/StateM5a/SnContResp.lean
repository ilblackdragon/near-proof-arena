import StateM5a.SnContKey5
import StateM5a.SnFreshLimbs
import StateM5a.SnFinal5

/-!
# StateM5a.SnContResp — the continued-key responders from `Holds`: `hlongS`, `hlongM`, `SnFreshLong`

A responder row (`oLS`, `oLM`, `oEP`, `oEM`) with `cont = 1` reads / builds a node whose full key
`K` (`SnContKey5.cont_old` / `cont_new`) is the walk key's segment `K_kid[d .. d + klen)`
(`gA = 0` on responders), and for a leaf the walk key ends there (`KLEN`):

* **`hlongS_of`**: `SibRel` of a continued `oLS` row (its old leaf under the requested ref);
* **`hlongM_of`**: `MatRel` of a continued `oLM` row (`cont_leaf_nmem`: the new leaf's memory is
  `leafMem K vlen`, `|hexPrefix K| = hplen`);
* **`snFreshLong_of`**: `FreshRel` of a continued `oEP` / `oEM` row (memory `extOwnMem K + unm`,
  `sn_mem_ebK`: `SN`'s memory chain with `own = 50 + 2·hplen = extOwnMem K`).

Premises beyond `SnFinal5`'s: `Sha256CR` (already there) and `hxRr` (no extra table touches `KCR`).
-/

namespace StateM5a.SnContResp

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnResp StateM5a.SnContKey4 StateM5a.SnContKey5 StateM5a.SnContRec1
open StateM5a.SnSer StateM5a.SnRec StateM5a.SnContHead StateM5a.SnSplit

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## `memChain` with a wide `plus` limb -/

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

/-- `FieldRows.limb_eq` with the added limb `x < 2^28` (a long key's own memory `50 + 2·hplen`):
the field equation is still the integer one (`|·| < P`). -/
theorem limb_eqW {g a b x y cc cp : Expr} (hg : ev tr t r pub g = 1)
    (h : ev tr t r pub (g * (a + sm 65536 cc - b - x + y - cp)) = 0)
    (ha : ev tr t r pub a < 2 ^ 17) (hb : ev tr t r pub b < 2 ^ 17) (hx : ev tr t r pub x < 2 ^ 28)
    (hy : ev tr t r pub y < 2 ^ 17)
    (hc : ev tr t r pub cc = 0 ∨ ev tr t r pub cc = 1 ∨ ev tr t r pub cc = P - 1)
    (hp : ev tr t r pub cp = 0 ∨ ev tr t r pub cp = 1 ∨ ev tr t r pub cp = P - 1) :
    (ev tr t r pub a : Int) + 65536 * cI (ev tr t r pub cc) =
      ev tr t r pub b + ev tr t r pub x - ev tr t r pub y + cI (ev tr t r pub cp) := by
  change ev tr t r pub (Expr.mul g _) = 0 at h
  rw [ev_mul_gate _ hg] at h
  have h' := eq_of_sub h
  simp only [ev_sub, ev_hadd, ev_add, sm, ev_mul, ev_const, Nat.reduceMod] at h'
  generalize ev tr t r pub a = A at ha h' ⊢
  generalize ev tr t r pub b = B at hb h' ⊢
  generalize ev tr t r pub x = X at hx h' ⊢
  generalize ev tr t r pub y = Y at hy h' ⊢
  unfold cI
  rcases hc with hc | hc | hc <;> rcases hp with hp | hp | hp <;> simp only [hc, hp] at h' ⊢ <;>
    simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceMod, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
      Nat.mul_one, ite_true, ite_false, Int.natCast_zero, Int.natCast_one, Int.reduceNeg] at h' ⊢ <;> omega

/-- `FieldRows.memChain_sound` with `plus` limbs `< 2^28`. -/
theorem memChain_soundW (g : Expr) (nw m plus minus : List Expr) (cy : Nat → Expr)
    (hc : ∀ e ∈ memChain g nw m plus minus cy, ev tr t r pub e = 0) (hg : ev tr t r pub g = 1)
    (hb : ∀ k, k < 4 → ev tr t r pub (nw.getD k 0) < 2 ^ 17 ∧ ev tr t r pub (m.getD k 0) < 2 ^ 17 ∧
      ev tr t r pub (plus.getD k 0) < 2 ^ 28 ∧ ev tr t r pub (minus.getD k 0) < 2 ^ 17) :
    V4 tr t r pub nw + V4 tr t r pub minus = V4 tr t r pub m + V4 tr t r pub plus := by
  have lim : ∀ k, k < 4 → ev tr t r pub (g * (nw.getD k 0 + sm 65536 (cy k) - m.getD k 0 -
      plus.getD k 0 + minus.getD k 0 - cprev cy k)) = 0 := fun k hk =>
    hc _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)))))
  have car : ∀ k, k < 4 → ev tr t r pub (cy k) = 0 ∨ ev tr t r pub (cy k) = 1 ∨
      ev tr t r pub (cy k) = P - 1 := fun k hk =>
    carry_cases (hc _ (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))))
  have h3 : ev tr t r pub (g * cy 3) = 0 :=
    hc _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))))
  have h3' : ev tr t r pub (Expr.mul g (cy 3)) = 0 := h3
  rw [ev_mul_gate _ hg] at h3'
  have z0 : ev tr t r pub (cprev cy 0) = 0 := ev_const 0
  have e0 := limb_eqW hg (lim 0 (by decide)) (hb 0 (by decide)).1 (hb 0 (by decide)).2.1
    (hb 0 (by decide)).2.2.1 (hb 0 (by decide)).2.2.2 (car 0 (by decide)) (Or.inl z0)
  have e1 := limb_eqW hg (lim 1 (by decide)) (hb 1 (by decide)).1 (hb 1 (by decide)).2.1
    (hb 1 (by decide)).2.2.1 (hb 1 (by decide)).2.2.2 (car 1 (by decide)) (car 0 (by decide))
  have e2 := limb_eqW hg (lim 2 (by decide)) (hb 2 (by decide)).1 (hb 2 (by decide)).2.1
    (hb 2 (by decide)).2.2.1 (hb 2 (by decide)).2.2.2 (car 2 (by decide)) (car 1 (by decide))
  have e3 := limb_eqW hg (lim 3 (by decide)) (hb 3 (by decide)).1 (hb 3 (by decide)).2.1
    (hb 3 (by decide)).2.2.1 (hb 3 (by decide)).2.2.2 (car 3 (by decide)) (car 2 (by decide))
  have c3 : cI (ev tr t r pub (cy 3)) = 0 := by rw [h3']; rfl
  have c0 : cI (ev tr t r pub (cprev cy 0)) = 0 := by rw [z0]; rfl
  rw [c0] at e0
  rw [c3] at e3
  simp only [cprev] at e1 e2 e3
  unfold V4
  generalize cI (ev tr t r pub (cy 0)) = C0 at e0 e1
  generalize cI (ev tr t r pub (cy 1)) = C1 at e1 e2
  generalize cI (ev tr t r pub (cy 2)) = C2 at e2 e3
  omega

end

/-! ## The memory of a fresh extension over any key -/

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

/-- `own = 50 + 2·hplen = extOwnMem K` for a key whose hex-prefix has `hplen` bytes. -/
theorem ev_ownK {Kk : List Nat} (hp : (hexPrefix Kk false).length = ev tr 3 r pub (Sn.c "hplen"))
    (hH : ev tr 3 r pub (Sn.c "hplen") < 2 ^ 25 + 64) :
    ev tr 3 r pub Sn.own = extOwnMem Kk ∧ ev tr 3 r pub Sn.own < 2 ^ 27 := by
  unfold Sn.own extOwnMem
  rw [ev_hadd, ev_sm3, ev_lit3, hp]
  simp only [Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show 2 * ev tr 3 r pub (Sn.c "hplen") < P by omega), Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxHeartbeats 8000000 in
/-- **A fresh extension's memory** `nmem = unm + extOwnMem K` (16-bit limbs), any key `K` with
`own = extOwnMem K` (`RowSnE.sn_mem_eb` with the key abstracted). -/
theorem sn_mem_ebK (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0) {Kk : List Nat}
    (hown : ev tr 3 r pub Sn.own = extOwnMem Kk) (hown' : ev tr 3 r pub Sn.own < 2 ^ 27)
    (eG : ev tr 3 r pub (Sn.c "oEU" + Sn.c "gfr") = 1) (eF : ev tr 3 r pub (Sn.c "gfr") = 1)
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536)
    (hu : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "unm" k) < 65536) :
    snNMem tr pub r = extOwnMem Kk + le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 r pub)) := by
  have e1 := FieldWsb.ev_one_sub1 (tr := tr) (t := 3) (r := r) (pub := pub) eF
  have em : ∀ k, k < 4 → ev tr 3 r pub (((List.range 4).map fun t => (1 - Sn.c "gfr") * Sn.M.getD t 0).getD k 0) = 0 :=
    fun k hk => by rw [getD_r4 _ hk, ev_gm0 e1]
  have eo : ∀ k, k < 4 → ev tr 3 r pub (((List.range 4).map fun t => (1 - Sn.c "gfr") * Sn.c "uom" t).getD k 0) = 0 :=
    fun k hk => by rw [getD_r4 _ hk, ev_gm0 e1]
  have ep0 : ev tr 3 r pub (((List.range 4).map fun t =>
      Sn.c "unm" t + (if t = 0 then Sn.c "gfr" * Sn.own else 0)).getD 0 0) =
      ev tr 3 r pub (Sn.c "unm" 0) + ev tr 3 r pub Sn.own := by
    rw [getD_r4 _ (by decide), ev_hadd, if_pos rfl, ev_gm eF]
    have := hu 0 (by decide); omega
  have ep : ∀ k, 0 < k → k < 4 → ev tr 3 r pub (((List.range 4).map fun t =>
      Sn.c "unm" t + (if t = 0 then Sn.c "gfr" * Sn.own else 0)).getD k 0) = ev tr 3 r pub (Sn.c "unm" k) := by
    intro k hk0 hk
    rw [getD_r4 _ hk, ev_hadd, if_neg (by omega), ev_lit3, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
  have q := memChain_soundW _ _ _ _ _ _ (fun e he => FieldRows2.sn_hold hc (sn_mem_chainU he)) eG (by
    intro k hk
    rw [em k hk, eo k hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [ep0]; exact ⟨by have := hN 0 hk; omega, by omega, by have := hu 0 hk; omega, by omega⟩
    · rw [ep k hk0 hk]; exact ⟨by have := hN k hk; omega, by omega, by have := hu k hk; omega, by omega⟩)
  unfold V4 at q
  rw [em 0 (by decide), em 1 (by decide), em 2 (by decide), em 3 (by decide),
    ep0, ep 1 (by decide) (by decide), ep 2 (by decide) (by decide), ep 3 (by decide) (by decide),
    eo 0 (by decide), eo 1 (by decide), eo 2 (by decide), eo 3 (by decide)] at q
  rw [← hown]
  unfold snNMem le4
  simp only [Sn.NM, memLimbs, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, E, sE] at q ⊢
  unfold ev at q hown'
  unfold ev
  omega

end

/-! ## The responders -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
  (hCR : Walk.Sha256CR)

include hH hxK hxR hL in
/-- A continued leaf responder's key is the walk key's rest from `d`. -/
theorem resp_keyC {s : Nat} {K : List Nat} (hs : s < tr.height 3) (hK : ContKey tr pub s K)
    (hA : ev tr 3 s pub (Sn.c "act") = 1) (hcont : ev tr 3 s pub (Sn.c "cont") = 1)
    (hA0 : ev tr 3 s pub (Sn.c "gA") = 0) (hisL : ev tr 3 s pub (Sn.c "isL") = 1) :
    (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d")) = K := by
  obtain ⟨hkl, -, -, -, -⟩ := cont_klen hH hxK hxR hs hA hcont
  have hdl := contKey_dlen hK hA0 (by omega)
  have hlen := sn_klen_leaf hH hL hs (ev_one_eval (by rw [ev_hmul, hisL, FieldRows2.ev_one_sub0 hA0]))
  change (keyOf tr _).length = _ at hlen
  have hb := (RowFacts.keyOf_bounds hH (ev tr 3 s pub (Sn.c "kid"))).2
  rw [ev_hadd, Nat.mod_eq_of_lt (by omega)] at hlen
  have hK2 := contKey_drop hK hA0
  rw [List.drop_eq_nil_of_le (show (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).length ≤
    ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "klen") by omega), List.append_nil] at hK2
  exact hK2

include hH hxB hxD hxK hxR hxRr hN hL hxr hCR in
set_option maxHeartbeats 4000000 in
/-- **`hlongS` from `Holds`**: a continued `oLS` row's `SibRel`. -/
theorem hlongS_of (σ : Store) : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLS") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      SibRel σ (keyOf tr) (ev tr 3 s pub (Sn.c "d"))
        (refOf (E tr 3 s pub (Sn.c "oref")) ((pack2 fun b => Sn.c "ho" b).map (E tr 3 s pub)))
        (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t))
        (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub))) := by
  intro s hs h1 hcont
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hA0, hisL, -, -, -, hA, hEP, hEM, hsum⟩ := resp_flags hc (Or.inl h1)
  have hLM : ev tr 3 s pub (Sn.c "oLM") = 0 := by omega
  obtain ⟨K, hK, hold, -, -⟩ := cont_old hH hxB hxD hxK hxR hxRr hN hxr hCR σ hs hcont
    (SnFinal4.gold_of hc hA hLM hEP hEM)
  have hd := resp_keyC hH hxK hxR hL hs hK hA hcont hA0 hisL
  unfold gRecK at hold
  rw [if_pos hisL] at hold
  unfold SibRel
  rw [hd]
  exact ⟨_, hold⟩

include hH hxB hxD hxK hxR hxRr hN hL hxr hCR in
set_option maxHeartbeats 8000000 in
/-- **`hlongM` from `Holds`**: a continued `oLM` row's `MatRel`. -/
theorem hlongM_of (σ : Store) : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLM") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      MatRel σ (keyOf tr) (ev tr 3 s pub (Sn.c "kid"))
        (ev tr 3 s pub (Sn.c "d")) (ev tr 3 s pub (Sn.c "dvlen"))
        (bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub)))
        (refOf (E tr 3 s pub (Sn.c "nref")) ((pack2 fun b => Sn.c "hn" b).map (E tr 3 s pub)))
        (le4 (Sn.NM.map (E tr 3 s pub))) := by
  intro s hs h1 hcont
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hA0, hisL, hLR, -, -, hA, -⟩ := resp_flags hc (Or.inr h1)
  have g : ev tr 3 s pub (Sn.c "oLR" + Sn.c "oLM") = 1 := by rw [ev_hadd, hLR, h1]
  have hgn : ev tr 3 s pub (Sn.c "gnew") = 1 := SnLimbsAll.gnew_of hc (Or.inr (Or.inl rfl)) h1
  obtain ⟨K, hK, hnew, hnx, hnm⟩ := cont_new hH hxB hxD hxK hxR hxRr hN hxr hCR σ hs hcont hgn
  obtain ⟨hkl, hev, hrl, hpl, ho⟩ := cont_klen hH hxK hxR hs hA hcont
  have hd := resp_keyC hH hxK hxR hL hs hK hA hcont hA0 hisL
  have hpay : payLen tr pub s = 36 := by rw [SnContSer2.payLen_eq, hisL]
  obtain ⟨hmem, -⟩ := SnContKey5.cont_leaf_nmem hc g hnm (fun t ht => hnx t (by omega)) (by omega)
  have hvl : ev tr 3 s pub (Sn.c "dvlen") = ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "nx" t) :=
    FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_vl) g
  have hvh : ((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub) =
      (pack2 fun b => Sn.c "nx" (4 + b)).map (E tr 3 s pub) := by
    simp only [pack2, List.map_map]
    apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.1 hi
    have := FieldVer.eq_of_gate (FieldRows2.sn_hold hc (sn_mem_dvh i hi')) g
    simp only [Function.comp, E]
    rw [show 4 + (2 * i + 1) = 5 + 2 * i by omega]
    exact Fp.ext this
  have hlm : snNMem tr pub s = leafMem K (ev tr 3 s pub (Sn.c "dvlen")) := by
    rw [hmem, hvl]; unfold leafMem; rw [contKey_hp hK true hkl hev hpl ho]; omega
  unfold gRecK at hnew
  rw [if_pos hisL] at hnew
  unfold MatRel
  rw [hd]
  refine ⟨hlm, ?_⟩
  rw [hvh, ← hlm, hvl]
  exact hnew

include hH hxB hxD hxK hxR hxRr hN hxr hCR in
set_option maxHeartbeats 8000000 in
/-- **`SnFreshLong` from `Holds`**: a continued `oEP` / `oEM` row's `FreshRel`. -/
theorem snFreshLong_of (σ : Store) (hxP : ∀ T ∈ extra, sendsOn T.interactions B_SPR = false)
    (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SXQ = false) (hCM : SnLimbsAll.SnContMem tr pub) :
    SnFinal5.SnFreshLong σ (keyOf tr) tr pub := by
  intro p hp h hcont
  have hc := tbl_sn D extra nb np hH p (List.mem_range.2 hp)
  obtain ⟨hA0, hL0, hE1, hA, hEU, hF⟩ := fresh_flags hc h
  have hgn : ev tr 3 p pub (Sn.c "gnew") = 1 := by
    rcases h with h | h
    · exact SnLimbsAll.gnew_of hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h
    · exact SnLimbsAll.gnew_of hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h
  obtain ⟨K, hK, hnew, -, hnm⟩ := cont_new hH hxB hxD hxK hxR hxRr hN hxr hCR σ hp hcont hgn
  obtain ⟨hkl, hev, hrl, hpl, ho⟩ := cont_klen hH hxK hxR hp hA hcont
  have hN4 : ∀ k, k < 4 → ev tr 3 p pub (Sn.NM.getD k 0) < 65536 := fun k hk => by
    rw [SnRange.NM_get k hk]; exact SnRange.limbs_of_bytes hnm k hk
  have hu : ∀ k, k < 4 → ev tr 3 p pub (Sn.c "unm" k) < 65536 := by
    rcases h with h | h
    · exact SnFreshLimbs.oep_unm_lt hH hxB hxD hxK hN hxr hxP hCM hp h
    · exact SnFreshLimbs.oem_unm_lt hH hxr hxQ hp h
  have hdl := contKey_dlen hK hA0 (by omega)
  have hb := (RowFacts.keyOf_bounds hH (ev tr 3 p pub (Sn.c "kid"))).2
  have hkl' : ev tr 3 p pub (Sn.c "d" + Sn.c "klen") = ev tr 3 p pub (Sn.c "d") + K.length := by
    rw [hK.len, ev_hadd, Nat.mod_eq_of_lt (by omega)]
  have hK2 := contKey_drop hK hA0
  rw [← hK.len] at hK2
  have eG : ev tr 3 p pub (Sn.c "oEU" + Sn.c "gfr") = 1 := by rw [ev_hadd, hF, hEU]
  obtain ⟨hown, hown'⟩ := ev_ownK (contKey_hp hK false hkl hev hpl ho) (by omega)
  have hmem := sn_mem_ebK hc hown hown' eG hF hN4 hu
  unfold FreshRel
  rw [hkl', epKey_eq hK2]
  unfold gRecK at hnew
  rw [if_neg (by omega)] at hnew
  refine extOver_of_new hnew hmem ⟨hK.nib, snNMem_lt hN4, ?_⟩
  rw [contKey_hp hK false hkl hev hpl ho]; omega

end

end StateM5a.SnContResp
