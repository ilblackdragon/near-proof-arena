import StateM5a.SnSplitKeys

/-! # StateM5a.SnSplitLX — `LocalOK` of `SN.oLX` (short key; split out of `SnSplitLoc`, M5a-7). -/

namespace StateM5a.SnSplitLoc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.RowBrN

local notation "P" => 2013265921

set_option maxRecDepth 100000

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
theorem localOK_oLX {s : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1)
    (h1 : ev tr 3 s pub (Sn.c "oLX") = 1)
    (hcont : ev tr 3 s pub (Sn.c "cont") = 0) (hold : OldOK σ (snIn tr pub s) (snOld tr pub s)) :
    LocalOK (Sem σ (keyOf tr)) (snRow tr pub s) := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hlt, hkx, hK, hK2, hne, hdep⟩ := split_keys hH hxN hxL hs hX hcont
  obtain ⟨hdo, hmode, hin, hd, hkid, hvl, hvh, href, hnm, hom⟩ := split_row hc hX
  have hans := split_ans hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hS hBnew hBlim
    (fun p hp h => hF p hp (Or.inl h)) hs hX
  obtain ⟨hg, -⟩ := split_flags hc hX
  have hisL : ev tr 3 s pub (Sn.c "isL") = 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := sn_flags' hc hg
    rw [h]; snfacts hc hg; omega
  rw [RowSnM.snOld_leaf hisL] at hold
  have hsplit := list_split hkx
  have hkl2 := (sn_klen_lx hH hxL hs (fp_of_ev1 h1))
  unfold KlenAt at hkl2
  have hkl0 := (FieldRows2.sn_flags hc hcont).1
  rw [ev_hadd, Nat.mod_eq_of_lt (by omega)] at hkl2
  have hk2 : (keyOf tr (ev tr 3 s pub (Sn.c "kid2"))).drop (ev tr 3 s pub (Sn.c "d")) =
      (snKey tr pub s).take (ev tr 3 s pub (Sn.c "jm")) ++ ev tr 3 s pub (Sn.c "kj") ::
        (snKey tr pub s).drop (ev tr 3 s pub (Sn.c "jm") + 1) := by
    rw [hK2, List.drop_eq_nil_of_le (by rw [hkl2]; exact Nat.le_refl _), List.append_nil]; exact hsplit
  have hsq : snQ tr pub s = ⟨ev tr 3 s pub (Sn.c "kid"), ev tr 3 s pub (Sn.c "kid2"),
      .leaf (ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t)) (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub))),
      ev tr 3 s pub (Sn.c "dvlen"), bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub))⟩ := by
    unfold snQ snOs; rw [if_pos h1]
  rw [hsq] at hans
  have hpl : ((snKey tr pub s).take (ev tr 3 s pub (Sn.c "jm"))).length = ev tr 3 s pub (Sn.c "jm") := by
    simp [snKey_length]; omega
  refine localOK_leafSplit (snRow tr pub s) hmode hdo (kid2 := ev tr 3 s pub (Sn.c "kid2"))
    (L := ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t))
    (A := bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub))) (m := snMem tr pub s)
    (p := (snKey tr pub s).take (ev tr 3 s pub (Sn.c "jm"))) (x0 := ev tr 3 s pub (Sn.c "kj"))
    (xs := (snKey tr pub s).drop (ev tr 3 s pub (Sn.c "jm") + 1))
    (ys := (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") + 1))
    (y := ev tr 3 s pub (Sn.c "y")) ?_ ?_ (fun h => hne h.symm) ?_ ?_ ?_
  · rw [hin, ← hsplit]; exact hold
  · rw [hkid, hd]; exact hK
  · rw [hd]; exact hk2
  · rw [hd, hkid, hvl, hvh, href, hnm, hpl]; exact hans
  · exact hom

end

end

end StateM5a.SnSplitLoc
