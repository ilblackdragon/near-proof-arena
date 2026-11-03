import StateM5a.SnContLocB
import StateM5a.SnContResp
import StateM5a.SnSplitLX
import StateM5a.SnSplitEX

/-!
# StateM5a.SnContLocX — `LocalOK` of the split rows `oLX` / `oEX` with a continued key

`SnSplitLX.localOK_oLX` / `SnSplitEX.localOK_oEX` with the head key replaced by the continued
head's full key `kk` (`ContKey`, `SnContKey4`):

* **`split_keysC`**: the keys of a continued split row — the mismatch `jm` is in the head
  (`ajm = 1`: `jm < 62 + odd`), so `kk[jm] = kj`, the walk key from `d` is `kk[..jm] ++ y :: …`
  (the head's `NIB` lookups before `jm`, `y` at `jm`), and `K_kid2[d..] = kk ++ …` (`g2 = 1`:
  head and chunks looked up against `kid2`);
* `ex_memK`: the extension split's memory `mem = cm + extOwnMem kk` (`own = 50 + 2·hplen < 2^27`;
  `SnContResp.memChain_soundW`);
* **`localOK_oLX_K`** / **`localOK_oEX_K`**.
-/

namespace StateM5a.SnContLocX

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.RowBrN StateM5a.SnSplitLoc StateM5a.SnContRec1
open StateM5a.SnContHead

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp}

set_option maxHeartbeats 4000000 in
theorem g2_of_split {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (hX : ev tr 3 s pub Sn.gX = 1) : ev tr 3 s pub (Sn.c "g2") = 1 := by
  obtain ⟨hg, -, -, hX'⟩ := split_flags hc hX
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := sn_flags' hc hg
  rw [h]; snfacts hc hg; omega

end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 8000000 in
/-- **The keys of a continued split row.** -/
theorem split_keysC (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) {s : Nat} (hs : s < tr.height 3)
    (hX : ev tr 3 s pub Sn.gX = 1) (hcont : ev tr 3 s pub (Sn.c "cont") = 1)
    {kk : List Nat} (hCK : SnContKey4.ContKey tr pub s kk) :
    ev tr 3 s pub (Sn.c "jm") < ev tr 3 s pub (Sn.c "klen") ∧
    kk[ev tr 3 s pub (Sn.c "jm")]? = some (ev tr 3 s pub (Sn.c "kj")) ∧
    (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d")) =
      kk.take (ev tr 3 s pub (Sn.c "jm")) ++ ev tr 3 s pub (Sn.c "y") ::
        (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") + 1) ∧
    (keyOf tr (ev tr 3 s pub (Sn.c "kid2"))).drop (ev tr 3 s pub (Sn.c "d")) =
      kk ++ (keyOf tr (ev tr 3 s pub (Sn.c "kid2"))).drop
        (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "klen")) ∧
    ev tr 3 s pub (Sn.c "y") ≠ ev tr 3 s pub (Sn.c "kj") ∧
    ev tr 3 s pub (Sn.c "d") + 64 < P := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hg, -, hA, -⟩ := split_flags hc hX
  obtain ⟨-, hajm⟩ := split_mN hc hX
  have hdep : ev tr 3 s pub (Sn.c "d") + 64 < P := SnDepthAll.sn_depth_all hH hxN hxL s hs (ev_one_eval hg)
  obtain ⟨hj64, hb, hkj, haj⟩ := RowSnM.sn_jm hc hA
  have ho := FieldRows2.sn_bool hc "odd" (by simp)
  have ha := ch_a hc hcont (ev tr 3 s pub (Sn.c "jm"))
  rw [FieldRows2.sn_a_lt _ hj64, ← haj, hajm] at ha
  have hjlt := SnContLocA.af_one _ _ ha.symm ho
  have hkx := hCK.head _ hjlt
  have hlt : ev tr 3 s pub (Sn.c "jm") < ev tr 3 s pub (Sn.c "klen") := by
    rw [← hCK.len]
    exact (List.getElem?_eq_some_iff.1 hkx).1
  obtain ⟨hy, -, hne⟩ := split_nibs hH hxN hxL hs hX
  refine ⟨hlt, by rw [hkx, hkj], ?_, SnContKey5.contKey_drop2 hCK (g2_of_split hc hX), hne, hdep⟩
  refine SnSplitLoc.drop_split (by rw [List.length_take, hCK.len]; omega) (fun j hj => ?_) hy
  rw [List.getElem?_take, if_pos hj, hCK.head j (by omega)]
  have hbj : ev tr 3 s pub (Sn.b j) = 1 := by
    rw [sn_b_lt j (by omega), hb j (by omega), if_pos hj]
  have := (sn_nib hH hxN j (by omega) hs (ev_one_eval hbj)).1
  rw [ev_dK j (by omega), FieldRows2.sn_k_lt j (by omega)] at this
  exact this

set_option maxHeartbeats 8000000 in
/-- **The extension split's memory**: `mem = cm + extOwnMem k` (16-bit limbs, `cmb` bytes in `RNG`). -/
theorem ex_memK (hH : Holds (fullAir D extra nb np) pub tr) (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    {s : Nat} (hs : s < tr.height 3) (h1 : ev tr 3 s pub (Sn.c "oEX") = 1)
    {kk : List Nat} (hown : ev tr 3 s pub Sn.own = extOwnMem kk) (hown' : ev tr 3 s pub Sn.own < 2 ^ 27)
    (hM : ∀ k, k < 4 → ev tr 3 s pub (Sn.M.getD k 0) < 65536) :
    snMem tr pub s = le4 (Sn.CM.map (E tr 3 s pub)) + extOwnMem (kk) := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have rb : ∀ t, t < 8 → ev tr 3 s pub (Sn.c "cmb" t) < 256 := fun t ht =>
    WsDecode3.rng_rcv hH hxr (t := 3) (by simp [fullAir, m5aAir])
      (by rw [WsDecode.full_get 3 (by decide)]; exact memD_mem (sn_rng_cmb t ht)) hs (ev_one_eval h1)
  have hCM : ∀ k, k < 4 → ev tr 3 s pub (Sn.CM.getD k 0) < 65536 := by
    intro k hk
    have : Sn.CM.getD k 0 = limb16 (fun b => Sn.c "cmb" b) k := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [this]; exact ev_limb16_byte3 (rb _ (by omega)) (rb _ (by omega))
  have hM' : ∀ k, k < 4 → ev tr 3 s pub (Sn.M.getD k 0) < 2 ^ 17 := fun k hk => by
    have := hM k hk; omega
  have hCM' : ∀ k, k < 4 → ev tr 3 s pub (Sn.CM.getD k 0) < 2 ^ 17 := fun k hk => by
    have := hCM k hk; omega
  have q := SnContResp.memChain_soundW _ _ _ _ _ _ (fun e he => FieldRows2.sn_hold hc (sn_mem_chainX he)) h1 (by
    intro k hk
    refine ⟨hM' k hk, hCM' k hk, ?_, ?_⟩ <;>
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, show (0 : Expr) = Expr.const 0 from rfl,
        ev_const] <;> omega)
  unfold V4 at q
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (0 : Expr) = Expr.const 0 from rfl, ev_const,
    Nat.zero_mod] at q
  rw [← hown]
  unfold snMem le4
  simp only [Sn.M, Sn.CM, memLimbs, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, E, sE] at q ⊢
  unfold ev at q hown'
  unfold ev
  omega


end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

section
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
  {σ : Store} (hS : SnMatOK σ (keyOf tr) tr pub)
  (hBnew : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → NewOK σ (brOut tr pub r) (brNew tr pub r))
  (hBlim : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → ∀ k, k < 4 →
    ev tr 2 r pub (Br.NM.getD k 0) < 65536 ∧ ev tr 2 r pub (Br.c "nm" k) < 65536 ∧
    ev tr 2 r pub (Br.c "nm2" k) < 65536)
  (hF : ∀ p, p < tr.height 3 → (ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) →
    FreshRel σ (keyOf tr) tr pub p)
include hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hS hBnew hBlim hF

set_option maxHeartbeats 16000000 in
/-- **`SN.oLX` is `LocalOK`** (short key). -/
theorem localOK_oLX_K {s : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1)
    (h1 : ev tr 3 s pub (Sn.c "oLX") = 1)
    (hcont : ev tr 3 s pub (Sn.c "cont") = 1) {kk : List Nat} (hCK : SnContKey4.ContKey tr pub s kk)
    (hold : OldOK σ (snIn tr pub s) (gRecK tr pub s kk (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b))) :
    LocalOK (Sem σ (keyOf tr)) (snRow tr pub s) := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hlt, hkx, hK, hK2, hne, hdep⟩ := split_keysC hH hxN hxL hs hX hcont hCK
  obtain ⟨hdo, hmode, hin, hd, hkid, hvl, hvh, href, hnm, hom⟩ := split_row hc hX
  have hans := split_ans hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hS hBnew hBlim
    (fun p hp h => hF p hp (Or.inl h)) hs hX
  obtain ⟨hg, -⟩ := split_flags hc hX
  have hisL : ev tr 3 s pub (Sn.c "isL") = 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := sn_flags' hc hg
    rw [h]; snfacts hc hg; omega
  rw [SnContLocA.gRecK_leaf hisL] at hold
  have hsplit := list_split hkx
  have hkl2 := (sn_klen_lx hH hxL hs (fp_of_ev1 h1))
  unfold KlenAt at hkl2
  have hkl0 := SnContKey5.contKey_dlen2 hCK (g2_of_split hc hX) (by omega)
  have hkb := (RowFacts.keyOf_bounds hH (ev tr 3 s pub (Sn.c "kid2"))).2
  rw [ev_hadd, Nat.mod_eq_of_lt (by omega)] at hkl2
  have hk2 : (keyOf tr (ev tr 3 s pub (Sn.c "kid2"))).drop (ev tr 3 s pub (Sn.c "d")) =
      (kk).take (ev tr 3 s pub (Sn.c "jm")) ++ ev tr 3 s pub (Sn.c "kj") ::
        (kk).drop (ev tr 3 s pub (Sn.c "jm") + 1) := by
    rw [hK2, List.drop_eq_nil_of_le (by rw [hkl2]; exact Nat.le_refl _), List.append_nil]; exact hsplit
  have hsq : snQ tr pub s = ⟨ev tr 3 s pub (Sn.c "kid"), ev tr 3 s pub (Sn.c "kid2"),
      .leaf (ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t)) (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub))),
      ev tr 3 s pub (Sn.c "dvlen"), bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub))⟩ := by
    unfold snQ snOs; rw [if_pos h1]
  rw [hsq] at hans
  have hpl : ((kk).take (ev tr 3 s pub (Sn.c "jm"))).length = ev tr 3 s pub (Sn.c "jm") := by
    simp [hCK.len]; omega
  refine localOK_leafSplit (snRow tr pub s) hmode hdo (kid2 := ev tr 3 s pub (Sn.c "kid2"))
    (L := ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t))
    (A := bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub))) (m := snMem tr pub s)
    (p := (kk).take (ev tr 3 s pub (Sn.c "jm"))) (x0 := ev tr 3 s pub (Sn.c "kj"))
    (xs := (kk).drop (ev tr 3 s pub (Sn.c "jm") + 1))
    (ys := (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") + 1))
    (y := ev tr 3 s pub (Sn.c "y")) ?_ ?_ (fun h => hne h.symm) ?_ ?_ ?_
  · rw [hin, ← hsplit]; exact hold
  · rw [hkid, hd]; exact hK
  · rw [hd]; exact hk2
  · rw [hd, hkid, hvl, hvh, href, hnm, hpl]; exact hans
  · exact hom

end

end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

section
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
  {σ : Store} (hS : SnMatOK σ (keyOf tr) tr pub)
  (hBnew : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → NewOK σ (brOut tr pub r) (brNew tr pub r))
  (hBlim : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → ∀ k, k < 4 →
    ev tr 2 r pub (Br.NM.getD k 0) < 65536 ∧ ev tr 2 r pub (Br.c "nm" k) < 65536 ∧
    ev tr 2 r pub (Br.c "nm2" k) < 65536)
  (hF : ∀ p, p < tr.height 3 → (ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) →
    FreshRel σ (keyOf tr) tr pub p)
include hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hxSQ hxSR hxr hS hBnew hBlim hF

set_option maxHeartbeats 16000000 in
/-- **`SN.oEX` is `LocalOK`** (short key). -/
theorem localOK_oEX_K {s : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1)
    (h1 : ev tr 3 s pub (Sn.c "oEX") = 1)
    (hcont : ev tr 3 s pub (Sn.c "cont") = 1) {kk : List Nat} (hCK : SnContKey4.ContKey tr pub s kk)
    (hold : OldOK σ (snIn tr pub s) (gRecK tr pub s kk (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b)))
    (hM : ∀ k, k < 4 → ev tr 3 s pub (Sn.M.getD k 0) < 65536) :
    LocalOK (Sem σ (keyOf tr)) (snRow tr pub s) := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hlt, hkx, hK, hK2, hne, hdep⟩ := split_keysC hH hxN hxL hs hX hcont hCK
  obtain ⟨hdo, hmode, hin, hd, hkid, hvl, hvh, href, hnm, hom⟩ := split_row hc hX
  have hans := split_ans hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hS hBnew hBlim
    (fun p hp h => hF p hp (Or.inl h)) hs hX
  obtain ⟨hg, -, -, hXs⟩ := split_flags hc hX
  have hL0 : ev tr 3 s pub (Sn.c "oLX") = 0 := by omega
  have hisL : ev tr 3 s pub (Sn.c "isL") = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := sn_flags' hc hg
    rw [h]; snfacts hc hg; omega
  have hA : ev tr 3 s pub (Sn.c "act") = 1 := (sn_flags' hc hg).2.1
  rw [SnContLocA.gRecK_ext (by omega)] at hold
  have hsplit := list_split hkx
  have hkl0 := SnContKey5.contKey_dlen2 hCK (g2_of_split hc hX) (by omega)
  have hkb := (RowFacts.keyOf_bounds hH (ev tr 3 s pub (Sn.c "kid2"))).2
  have hlen : ((kk).take (ev tr 3 s pub (Sn.c "jm")) ++ ev tr 3 s pub (Sn.c "kj") ::
      (kk).drop (ev tr 3 s pub (Sn.c "jm") + 1)).length = ev tr 3 s pub (Sn.c "klen") := by
    rw [← hsplit, hCK.len]
  have hpl : ((kk).take (ev tr 3 s pub (Sn.c "jm"))).length = ev tr 3 s pub (Sn.c "jm") := by
    simp [hCK.len]; omega
  obtain ⟨hkl', hev, hrl, hpl', ho⟩ := SnContKey5.cont_klen hH hxK hxR hs hA hcont
  obtain ⟨hown, hown'⟩ := SnContResp.ev_ownK (SnContKey5.contKey_hp hCK false hkl' hev hpl' ho) (by omega)
  have hmem := ex_memK hH hxr hs h1 hown hown' hM
  have hsq : snQ tr pub s = ⟨ev tr 3 s pub (Sn.c "kid"), ev tr 3 s pub (Sn.c "kid2"), snOs tr pub s,
      ev tr 3 s pub (Sn.c "dvlen"), bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub))⟩ := rfl
  rw [hsq] at hans
  have e1 := ev_one_eval h1
  -- the old side
  have hos : OldSideX σ (keyOf tr) (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") + 1)
      (ev tr 3 s pub (Sn.c "kid2")) (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "klen")) (snChild tr pub s)
      (le4 (Sn.CM.map (E tr 3 s pub))) ((kk).drop (ev tr 3 s pub (Sn.c "jm") + 1)) (snOs tr pub s) := by
    have bz := bool_le (FieldRows2.sn_hold hc (e := bool (Sn.c "z")) (by unfold Sn.constraints; simp [Sn.ops]))
    have z1c := FieldRows2.sn_hold hc sn_mem_z1
    have z0c := FieldRows2.sn_hold hc sn_mem_z0
    have hxhf := eq_of_sub (FieldRows2.sn_hold hc sn_mem_xhf)
    unfold snOs
    rw [if_neg (by omega)]
    rcases Nat.lt_or_ge (ev tr 3 s pub (Sn.c "jm") + 1) (ev tr 3 s pub (Sn.c "klen")) with hgt | hle
    · -- `xs ≠ []`: `z = 0`, the re-keyed extension from `SXR`
      have hz : ev tr 3 s pub (Sn.c "z") = 0 := by
        rw [ev_hmul, ev_hmul, h1, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _), ← ev_hmul] at z1c
        rcases (by omega : ev tr 3 s pub (Sn.c "z") = 0 ∨ ev tr 3 s pub (Sn.c "z") = 1) with h | h
        · exact h
        · exfalso
          rw [ev_hmul, h, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _), ev_sub, ev_sub, ev_one] at z1c
          have := ev_lt (tr := tr) (t := 3) (r := s) (pub := pub) (Sn.c "jm")
          have := ev_lt (tr := tr) (t := 3) (r := s) (pub := pub) (Sn.c "klen")
          omega
      obtain ⟨a, xs', hxs⟩ : ∃ a xs', (kk).drop (ev tr 3 s pub (Sn.c "jm") + 1) = a :: xs' := by
        cases h : (kk).drop (ev tr 3 s pub (Sn.c "jm") + 1) with
        | nil => exfalso; have := congrArg List.length h; simp [hCK.len] at this; omega
        | cons a xs' => exact ⟨a, xs', rfl⟩
      rw [hxs]
      have hg0 : ev tr 3 s pub (Sn.c "oEX" * (1 - Sn.c "z")) = 1 := by
        rw [RowSnN.ev_gm h1, FieldRows2.ev_one_sub0 hz]
      obtain ⟨p, hp, hpM, hr⟩ := sxr_src hH hxSR hs hg0
      obtain ⟨s', hs', hg', hq⟩ := sxq_src hH hxSQ hp hpM
      have hc' := tbl_sn D extra nb np hH s' (List.mem_range.2 hs')
      have hX' := (gX_of_oEX hc' hg').1
      obtain ⟨hgs', h0', -⟩ := split_flags hc' hX'
      obtain ⟨rw0, rd, rk, rf, rh, rm⟩ := hdr4_dec hr (by simp [pack2])
      obtain ⟨qw, qd, qk, qe, qf, qh, qm⟩ := hdr5_dec hq (by simp [pack2])
      obtain rfl := sn_term_unique hH hD hx hxN hxK hxR hs hs' (ev_one_eval hg) (ev_one_eval hgs') (by
        have := split_flags hc hX; exact this.2.1) h0' (toNat_eq (rw0.symm.trans qw.symm))
      have hrel := hF p hp (Or.inr hpM)
      unfold FreshRel at hrel
      have ed1 : ev tr 3 p pub (Sn.c "d") = ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") + 1 := by
        rw [← toNat_eq qd]
        rw [ev_hadd, ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have ed2 : ev tr 3 p pub (Sn.c "d" + Sn.c "klen") = ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "klen") := by
        rw [← toNat_eq qe, ev_hadd, Nat.mod_eq_of_lt (by omega)]
      have ek : ev tr 3 p pub (Sn.c "kid") = ev tr 3 s pub (Sn.c "kid2") := (toNat_eq qk).symm
      have hch : snNChild tr pub p = snChild tr pub s := by
        unfold snNChild snChild
        show refOf (E tr 3 p pub (Sn.c "nxf")) ((pack2 fun b => Sn.c "nx" b).map (E tr 3 p pub)) =
          refOf (E tr 3 s pub (Sn.c "xf")) ((pack2 fun b => Sn.c "x" b).map (E tr 3 s pub))
        rw [← qf, ← qh]
      have hcm : le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 p pub)) = le4 (Sn.CM.map (E tr 3 s pub)) := by
        rw [← qm]
      rw [ed1, ed2, ek, hch, hcm] at hrel
      refine ⟨snOut tr pub p, snNMem tr pub p, ?_, hrel⟩
      have g0 := ev_one_eval (FieldRows2.ev_one_sub0 hz)
      have zz := fp_of_ev0 hz
      have hxh : ((List.range 16).map fun i => Sn.c "xh" i).map (E tr 3 s pub) =
          ((List.range 16).map fun i => Sn.c "sxh" i).map (E tr 3 s pub) := by
        simp only [List.map_map]
        apply List.map_congr_left; intro i hi
        have := eq_of_sub (FieldRows2.sn_hold hc (SnSplitBus.sn_mem_xh i (List.mem_range.1 hi)))
        apply Fp.ext
        simp only [Function.comp]
        show ev tr 3 s pub (Sn.c "xh" i) = _
        rw [this, RowSnN.ev_gm h1]
        apply toNat_eq
        simp only [eval_add, eval_mul, zz]; grind
      have hxm : le4 (((List.range 4).map fun t => Sn.c "xm" t).map (E tr 3 s pub)) =
          le4 (((List.range 4).map fun t => Sn.c "sxm" t).map (E tr 3 s pub)) := by
        simp only [le4_map4]
        have a : ∀ t, t < 4 → ev tr 3 s pub (Sn.c "xm" t) = ev tr 3 s pub (Sn.c "sxm" t) := by
          intro t ht
          rw [eq_of_sub (FieldRows2.sn_hold hc (sn_mem_xm t ht)), RowSnN.ev_gm h1]
          apply toNat_eq
          simp only [eval_add, eval_mul, zz]; grind
        change ev tr 3 s pub (Sn.c "xm" 0) + 65536 * ev tr 3 s pub (Sn.c "xm" 1) + 4294967296 * ev tr 3 s pub (Sn.c "xm" 2) +
          281474976710656 * ev tr 3 s pub (Sn.c "xm" 3) = ev tr 3 s pub (Sn.c "sxm" 0) + 65536 * ev tr 3 s pub (Sn.c "sxm" 1) +
          4294967296 * ev tr 3 s pub (Sn.c "sxm" 2) + 281474976710656 * ev tr 3 s pub (Sn.c "sxm" 3)
        rw [a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide)]
      have hxf : E tr 3 s pub (Sn.c "xhf") = E tr 3 s pub (Sn.c "sxhf") := by
        apply Fp.ext
        show ev tr 3 s pub (Sn.c "xhf") = _
        rw [hxhf, RowSnN.ev_gm h1]
        apply toNat_eq
        simp only [eval_add, eval_mul, zz]; grind
      have r1 : refOf (E tr 3 s pub (Sn.c "xhf")) (((List.range 16).map fun i => Sn.c "xh" i).map (E tr 3 s pub)) =
          snOut tr pub p := by
        rw [hxf, hxh]; unfold snOut
        show _ = refOf (E tr 3 p pub (Sn.c "nref")) ((pack2 fun b => Sn.c "hn" b).map (E tr 3 p pub))
        rw [rf, rh]
      have r2 : le4 (((List.range 4).map fun t => Sn.c "xm" t).map (E tr 3 s pub)) = snNMem tr pub p := by
        rw [hxm]; unfold snNMem
        show _ = le4 (Sn.NM.map (E tr 3 p pub))
        rw [rm]
      show OldSide.node _ _ = _
      rw [r1, r2]
    · -- `xs = []`: `z = 1`, the extension's own child
      have hkl : ev tr 3 s pub (Sn.c "klen") = ev tr 3 s pub (Sn.c "jm") + 1 := by omega
      have hxs : (kk).drop (ev tr 3 s pub (Sn.c "jm") + 1) = [] :=
        List.drop_eq_nil_of_le (by rw [hCK.len]; omega)
      rw [hxs]
      have ekl : (Sn.c "klen").eval tr 3 s pub = (Sn.c "jm").eval tr 3 s pub + 1 := by
        apply Fp.ext
        show ev tr 3 s pub (Sn.c "klen") = ev tr 3 s pub (Sn.c "jm" + 1)
        rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)]; exact hkl
      have hz : (Sn.c "z").eval tr 3 s pub = 1 := by
        have := fp_of_ev0 z0c
        simp only [eval_mul, eval_sub, eval_add, eval_lit, e1, ekl] at this
        grind

      have hxh : ((List.range 16).map fun i => Sn.c "xh" i).map (E tr 3 s pub) =
          (pack2 fun b => Sn.c "x" b).map (E tr 3 s pub) := by
        simp only [List.map_map, pack2]
        apply List.map_congr_left; intro i hi
        have := eq_of_sub (FieldRows2.sn_hold hc (SnSplitBus.sn_mem_xh i (List.mem_range.1 hi)))
        apply Fp.ext
        simp only [Function.comp]
        show ev tr 3 s pub (Sn.c "xh" i) = _
        rw [this, RowSnN.ev_gm h1]
        apply toNat_eq
        simp only [eval_add, eval_mul, eval_sub, eval_lit, eval_sm, eval_K, hz]; grind
      have hxf : E tr 3 s pub (Sn.c "xhf") = E tr 3 s pub (Sn.c "xf") := by
        apply Fp.ext
        show ev tr 3 s pub (Sn.c "xhf") = _
        rw [hxhf, RowSnN.ev_gm h1]
        apply toNat_eq
        simp only [eval_add, eval_mul, eval_sub, eval_lit, hz]; grind
      have hxm : le4 (((List.range 4).map fun t => Sn.c "xm" t).map (E tr 3 s pub)) = le4 (Sn.CM.map (E tr 3 s pub)) := by
        have a : ∀ t, t < 4 → ev tr 3 s pub (Sn.c "xm" t) = ev tr 3 s pub (Sn.CM.getD t 0) := by
          intro t ht
          rw [eq_of_sub (FieldRows2.sn_hold hc (sn_mem_xm t ht)), RowSnN.ev_gm h1]
          apply toNat_eq
          simp only [eval_add, eval_mul, eval_sub, eval_lit, hz]; grind
        simp only [le4_map4]
        have hcm : le4 (Sn.CM.map (E tr 3 s pub)) = ev tr 3 s pub (Sn.CM.getD 0 0) +
            65536 * ev tr 3 s pub (Sn.CM.getD 1 0) + 4294967296 * ev tr 3 s pub (Sn.CM.getD 2 0) +
            281474976710656 * ev tr 3 s pub (Sn.CM.getD 3 0) := by
          simp [le4, Sn.CM, memLimbs, List.range, List.range.loop, ev]
        rw [hcm]
        change ev tr 3 s pub (Sn.c "xm" 0) + 65536 * ev tr 3 s pub (Sn.c "xm" 1) + 4294967296 * ev tr 3 s pub (Sn.c "xm" 2) +
          281474976710656 * ev tr 3 s pub (Sn.c "xm" 3) = _
        rw [a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide)]
      show _ = OldSide.node (refOf (E tr 3 s pub (Sn.c "xf")) ((pack2 fun b => Sn.c "x" b).map (E tr 3 s pub))) _
      rw [hxf, hxh, hxm]
  refine localOK_extSplit (snRow tr pub s) hmode hdo (c := snChild tr pub s) (kid2 := ev tr 3 s pub (Sn.c "kid2"))
    (m := snMem tr pub s) (cm := le4 (Sn.CM.map (E tr 3 s pub)))
    (p := (kk).take (ev tr 3 s pub (Sn.c "jm"))) (x0 := ev tr 3 s pub (Sn.c "kj"))
    (xs := (kk).drop (ev tr 3 s pub (Sn.c "jm") + 1))
    (ys := (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") + 1))
    (y := ev tr 3 s pub (Sn.c "y")) (os := snOs tr pub s) ?_ ?_ (fun h => hne h.symm) ?_ ?_ ?_ ?_ ?_
  · rw [hin, ← hsplit]; exact hold
  · rw [hkid, hd]; exact hK
  · rw [hd, hlen, ← hsplit]; exact hK2
  · rw [← hsplit, hmem]; omega
  · rw [hd, hpl, hlen]; exact hos
  · rw [hd, hkid, hvl, hvh, href, hnm, hpl]; exact hans
  · exact hom

end

end

end StateM5a.SnContLocX
