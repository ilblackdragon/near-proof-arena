import StateM5a.SnSplit

/-!
# StateM5a.SnSplitLoc — `LocalOK` of the `SN` split rows (`oLX`, `oEX`) with a short key

A split row at `(w, d)` with `cont = 0`: its key `snKey = p ++ x₀ :: xs` (`p` the `jm` nibbles
looked up against the walk key, `x₀ = k_jm`), the walk key `K[d..] = p ++ y :: ys` (`y ≠ x₀`,
`split_keys`), the old key `K_kid2[d..]` starts with `snKey` (`g2` lookups).  Its result is the
`SPR` answer (`SnSplit.split_ans`), so `BusSplit.localOK_leafSplit` (`oLX`, `localOK_oLX`) and
`BusSplit2.localOK_extSplit` (`oEX`, `localOK_oEX`: the old side the extension's child or the
re-keyed extension answered on `SXR` by `oEM`, `FreshRel`) apply.
-/

namespace StateM5a.SnSplitLoc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem drop_split {K p : List Nat} {d L y : Nat} (hp : p.length = L) (h : ∀ j < L, K[d + j]? = p[j]?)
    (hy : K[d + L]? = some y) : K.drop d = p ++ y :: K.drop (d + L + 1) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  rcases Nat.lt_trichotomy i L with hi | rfl | hi
  · rw [List.getElem?_append_left (by omega)]; exact h i hi
  · rw [List.getElem?_append_right (by omega), hp, Nat.sub_self]; simpa using hy
  · rw [List.getElem?_append_right (by omega), hp]
    obtain ⟨k, rfl⟩ : ∃ k, i = L + 1 + k := ⟨i - L - 1, by omega⟩
    rw [show L + 1 + k - L = k + 1 by omega, List.getElem?_cons_succ, List.getElem?_drop]
    congr 1; omega

theorem list_split {l : List Nat} {j x : Nat} (h : l[j]? = some x) : l = l.take j ++ x :: l.drop (j + 1) := by
  have hj : j < l.length := by
    rcases Nat.lt_or_ge j l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have := drop_split (K := l) (d := 0) (p := l.take j) (L := j) (y := x) (by simp; omega)
    (fun i hi => by rw [Nat.zero_add, List.getElem?_take]; simp [hi]) (by simpa using h)
  simpa using this

theorem map_zip3_thd {tr : Trace Fp} {r : Nat} {pub : List Fp} (g h k : Expr) (hg : g.eval tr 3 r pub = 0)
    (hh : h.eval tr 3 r pub = 0) (hk : k.eval tr 3 r pub = 1) :
    ∀ (A B C : List Expr), A.length = B.length → B.length = C.length →
      (((A.zip B).zip C).map (fun ((p, q), s) => g * p + h * q + k * s)).map (E tr 3 r pub) = C.map (E tr 3 r pub)
  | [], [], [], _, _ => rfl
  | a :: A, b :: B, c :: C, h1, h2 => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    refine ⟨?_, map_zip3_thd g h k hg hh hk A B C (by simpa using h1) (by simpa using h2)⟩
    simp only [E, eval_add, eval_mul, hg, hh, hk]; grind
  | [], _ :: _, _, h1, _ => by simp at h1
  | _ :: _, [], _, h1, _ => by simp at h1
  | _, [], _ :: _, _, h2 => by simp at h2
  | _, _ :: _, [], _, h2 => by simp at h2

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 8000000 in
/-- **The keys of a short-key split row.** -/
theorem split_keys (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hxL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false) {s : Nat} (hs : s < tr.height 3)
    (hX : ev tr 3 s pub Sn.gX = 1) (hcont : ev tr 3 s pub (Sn.c "cont") = 0) :
    ev tr 3 s pub (Sn.c "jm") < ev tr 3 s pub (Sn.c "klen") ∧
    (snKey tr pub s)[ev tr 3 s pub (Sn.c "jm")]? = some (ev tr 3 s pub (Sn.c "kj")) ∧
    (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d")) =
      (snKey tr pub s).take (ev tr 3 s pub (Sn.c "jm")) ++ ev tr 3 s pub (Sn.c "y") ::
        (keyOf tr (ev tr 3 s pub (Sn.c "kid"))).drop (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") + 1) ∧
    (keyOf tr (ev tr 3 s pub (Sn.c "kid2"))).drop (ev tr 3 s pub (Sn.c "d")) =
      snKey tr pub s ++ (keyOf tr (ev tr 3 s pub (Sn.c "kid2"))).drop
        (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "klen")) ∧
    ev tr 3 s pub (Sn.c "y") ≠ ev tr 3 s pub (Sn.c "kj") ∧
    ev tr 3 s pub (Sn.c "d") + 64 < P := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hg, -, hA, -⟩ := split_flags hc hX
  obtain ⟨-, hajm⟩ := split_mN hc hX
  have hdep : ev tr 3 s pub (Sn.c "d") + 64 < P := SnDepthAll.sn_depth_all hH hxN hxL s hs (ev_one_eval hg)
  obtain ⟨hj64, hb, hkj, haj⟩ := RowSnM.sn_jm hc hA
  obtain ⟨hkl, hf⟩ := FieldRows2.sn_flags hc hcont
  obtain ⟨hy, -, hne⟩ := split_nibs hH hxN hxL hs hX
  have hlt : ev tr 3 s pub (Sn.c "jm") < ev tr 3 s pub (Sn.c "klen") := by
    have := hf _ hj64; rw [← haj, hajm] at this; split at this <;> omega
  have hget : ∀ j, j < ev tr 3 s pub (Sn.c "klen") → (snKey tr pub s)[j]? = some (ev tr 3 s pub (Sn.c "k" j)) := by
    intro j hj
    unfold snKey FieldRows2.keyOf
    rw [List.getElem?_map, List.getElem?_range hj]; rfl
  have hg2 : ev tr 3 s pub (Sn.c "g2") = 1 := by
    obtain ⟨-, -, -, hX'⟩ := split_flags hc hX
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := sn_flags' hc hg
    rw [h]; snfacts hc hg; omega
  refine ⟨hlt, by rw [hget _ hlt, hkj], ?_, ?_, hne, hdep⟩
  · refine drop_split (by simp; omega) (fun j hj => ?_) hy
    rw [List.getElem?_take, if_pos hj, hget j (by omega)]
    have hbj : ev tr 3 s pub (Sn.b j) = 1 := by
      rw [sn_b_lt j (by omega), hb j (by omega), if_pos hj]
    have := (sn_nib hH hxN j (by omega) hs (fp_of_ev1 hbj)).1
    rw [ev_dK j (by omega), FieldRows2.sn_k_lt j (by omega)] at this
    exact this
  · exact RowSnE.sn_key2_prefix hc hcont hg2 hdep (fun j hj hgj => (sn_nib2 hH hxN j hj hs hgj).1)

/-- The decoded walk row of a split row: no child, upsert, result the `SPR` answer. -/
theorem split_row {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (hX : ev tr 3 s pub Sn.gX = 1) :
    (snRow tr pub s).dout = none ∧ (snRow tr pub s).din.pay.mode = 1 ∧
    (snRow tr pub s).din.ref = snIn tr pub s ∧ (snRow tr pub s).din.d = ev tr 3 s pub (Sn.c "d") ∧
    (snRow tr pub s).din.pay.kid = ev tr 3 s pub (Sn.c "kid") ∧
    (snRow tr pub s).din.pay.vlen = ev tr 3 s pub (Sn.c "dvlen") ∧
    (snRow tr pub s).din.pay.vh = bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub)) ∧
    (snRow tr pub s).uout.ref = refOf (E tr 3 s pub (Sn.c "shf")) (((List.range 16).map fun i => Sn.c "sh" i).map (E tr 3 s pub)) ∧
    (snRow tr pub s).uout.nm = le4 (((List.range 4).map fun t => Sn.c "sm" t).map (E tr 3 s pub)) ∧
    (snRow tr pub s).uout.om = snMem tr pub s := by
  obtain ⟨hg, h0, -, hX'⟩ := split_flags hc hX
  snfacts hc hg
  have a1 : (Sn.c "oLR").eval tr 3 s pub = 0 := s0
  have a2 : (Sn.c "oEU").eval tr 3 s pub = 0 := s0
  have a5 : (Sn.c "oEB").eval tr 3 s pub = 0 := s0
  have a8 : (Sn.c "oLZ").eval tr 3 s pub = 0 := s0
  have a9 : (Sn.c "oEZ").eval tr 3 s pub = 0 := s0
  have a10 : (Sn.c "oES").eval tr 3 s pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 s pub = 1 := s1
  have eD : (Sn.c "mD").eval tr 3 s pub = 0 := s0
  have eNu : gnu.eval tr 3 s pub = 0 := by simp only [gnu, eval_add, a1, a2, a5]; grind
  have eS : Sn.gS.eval tr 3 s pub = 0 := by simp only [Sn.gS, eval_add, a8, a9, a10]; grind
  have eX : Sn.gX.eval tr 3 s pub = 1 := ev_one_eval hX
  have hdin : (snRow tr pub s).din = _ := by simp only [snRow]; exact sn_din
  have huout : (snRow tr pub s).uout = _ := by simp only [snRow]; exact sn_uout
  refine ⟨WalkEnd.snRow_dout h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdin, snpay_mode]; show (Sn.mode.eval tr 3 s pub).toNat = 1
    rw [show Sn.mode.eval tr 3 s pub = 1 by evsn; grind]; rfl
  · rw [hdin]
  · rw [hdin]
  · rw [hdin, snpay_kid]; rfl
  · rw [hdin, snpay_vlen]; rfl
  · rw [hdin, snpay_vh]
  · rw [huout]; dsimp only
    rw [map_zip3_thd gnu Sn.gS Sn.gX eNu eS eX _ _ _ (by simp [pack2]) (by simp [pack2])]
    congr 1
    simp only [E, eval_add, eval_mul, eNu, eS, eX]; grind
  · rw [huout]; dsimp only
    rw [map_zip_right gnu Sn.gX (fun p => p) _ eNu eX _ (by simp [Sn.NM, memLimbs])]
  · rw [huout]; dsimp only
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]; rfl

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
    rw [hK2, List.drop_eq_nil_of_le (by rw [hkl2]), List.append_nil]; exact hsplit
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

/-! ## The extension split (`oEX`) -/

theorem ev_limb16_byte3 {tr : Trace Fp} {r : Nat} {pub : List Fp} {v : Nat → Expr} {k : Nat}
    (ha : ev tr 3 r pub (v (2 * k)) < 256)
    (hb : ev tr 3 r pub (v (2 * k + 1)) < 256) : ev tr 3 r pub (limb16 v k) < 65536 := by
  unfold limb16
  rw [ev_hadd, ev_hmul, show K 256 = Expr.const 256 from rfl, ev_const]
  simp only [Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show 256 * ev tr 3 r pub (v (2 * k + 1)) < P by omega),
    Nat.mod_eq_of_lt (show ev tr 3 r pub (v (2 * k)) + 256 * ev tr 3 r pub (v (2 * k + 1)) < P by omega)]
  omega

theorem sn_mem_chainX {e : Expr} (he : e ∈ memChain (Sn.c "oEX") Sn.M Sn.CM [Sn.own, 0, 0, 0] [0, 0, 0, 0]
    (fun t => Sn.c "cy2" t)) : e ∈ Sn.constraints := by
  unfold Sn.constraints; exact List.mem_append_right _ he

theorem sn_rng_cmb : ∀ t, t < 8 → memD (rcv B_RNG (Sn.c "oEX") [Sn.c "cmb" t]) Sn.interactions = true := by
  decide

theorem sn_mem_z1 : Sn.c "oEX" * Sn.c "z" * (Sn.c "klen" - Sn.c "jm" - 1) ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_z0 : Sn.c "oEX" * (1 - Sn.c "z") * ((Sn.c "klen" - Sn.c "jm" - 1) * Sn.c "iz" - 1) ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_xhf : Sn.c "xhf" - Sn.c "oEX" * (Sn.c "z" * Sn.c "xf" + (1 - Sn.c "z") * Sn.c "sxhf") ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_xm (t : Nat) (ht : t < 4) :
    Sn.c "xm" t - Sn.c "oEX" * (Sn.c "z" * Sn.CM.getD t 0 + (1 - Sn.c "z") * Sn.c "sxm" t) ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_map, List.mem_range]; memfind

theorem hdr5_dec {a b c d e a' b' c' d' e' : Expr} {A B A' B' : List Expr} {f g : Expr → Fp}
    (h : ([a, b, c, d, e] ++ A ++ B).map f = ([a', b', c', d', e'] ++ A' ++ B').map g) (hA : A.length = A'.length) :
    f a = g a' ∧ f b = g b' ∧ f c = g c' ∧ f d = g d' ∧ f e = g e' ∧ A.map f = A'.map g ∧ B.map f = B'.map g := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨h7, h8⟩ := List.append_inj h6 (by simp [hA])
  exact ⟨h1, h2, h3, h4, h5, h7, h8⟩

theorem hdr4_dec {a b c d a' b' c' d' : Expr} {A B A' B' : List Expr} {f g : Expr → Fp}
    (h : ([a, b, c, d] ++ A ++ B).map f = ([a', b', c', d'] ++ A' ++ B').map g) (hA : A.length = A'.length) :
    f a = g a' ∧ f b = g b' ∧ f c = g c' ∧ f d = g d' ∧ A.map f = A'.map g ∧ B.map f = B'.map g := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨h7, h8⟩ := List.append_inj h5 (by simp [hA])
  exact ⟨h1, h2, h3, h4, h7, h8⟩

open StateM5a.FieldWalk2 in
set_option maxHeartbeats 4000000 in
theorem gX_of_oEX {tr : Trace Fp} {pub : List Fp} {s : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (h1 : ev tr 3 s pub (Sn.c "oEX" * (1 - Sn.c "z")) = 1) : ev tr 3 s pub Sn.gX = 1 ∧ ev tr 3 s pub (Sn.c "oEX") = 1 := by
  have hb : ∀ s' ∈ snNames, ev tr 3 s pub (Sn.c s') ≤ 1 := fun s' hs => sn_flag_le hc s' hs
  have bE := hb "oEX" (by simp [snNames]); have bL := hb "oLX" (by simp [snNames])
  have bU := hb "mU" (by simp [snNames]); have bR := hb "oLR" (by simp [snNames])
  have bEU := hb "oEU" (by simp [snNames])
  have hE : ev tr 3 s pub (Sn.c "oEX") = 1 := by
    rw [ev_hmul] at h1
    rcases (by omega : ev tr 3 s pub (Sn.c "oEX") = 0 ∨ ev tr 3 s pub (Sn.c "oEX") = 1) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  have e3 := sn_sum hc "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc] at e3
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  rw [e3] at c3
  refine ⟨?_, hE⟩
  unfold Sn.gX; rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; omega

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 8000000 in
/-- **The extension split's memory**: `mem = cm + extOwnMem k` (16-bit limbs, `cmb` bytes in `RNG`). -/
theorem ex_mem (hH : Holds (fullAir D extra nb np) pub tr) (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    {s : Nat} (hs : s < tr.height 3) (h1 : ev tr 3 s pub (Sn.c "oEX") = 1)
    (hA : ev tr 3 s pub (Sn.c "act") = 1) (hcont : ev tr 3 s pub (Sn.c "cont") = 0)
    (hM : ∀ k, k < 4 → ev tr 3 s pub (Sn.M.getD k 0) < 65536) :
    snMem tr pub s = le4 (Sn.CM.map (E tr 3 s pub)) + extOwnMem (snKey tr pub s) := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hown, hown'⟩ := RowSnE.ev_own hc hA hcont
  have rb : ∀ t, t < 8 → ev tr 3 s pub (Sn.c "cmb" t) < 256 := fun t ht =>
    WsDecode3.rng_rcv hH hxr (t := 3) (by simp [fullAir, m5aAir])
      (by rw [WsDecode.full_get 3 (by decide)]; exact memD_mem (sn_rng_cmb t ht)) hs (ev_one_eval h1)
  have hCM : ∀ k, k < 4 → ev tr 3 s pub (Sn.CM.getD k 0) < 65536 := by
    intro k hk
    have : Sn.CM.getD k 0 = limb16 (fun b => Sn.c "cmb" b) k := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [this]; exact ev_limb16_byte3 (rb _ (by omega)) (rb _ (by omega))
  have q := memChain_sound _ _ _ _ _ _ (fun e he => FieldRows2.sn_hold hc (sn_mem_chainX he)) h1 (by
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
      refine ⟨by have := hM _ (by decide); omega, by have := hCM _ (by decide); omega, ?_, ?_⟩ <;>
      simp only [show (0 : Expr) = Expr.const 0 from rfl, ev_const] <;> omega)
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
theorem localOK_oEX {s : Nat} (hs : s < tr.height 3) (hX : ev tr 3 s pub Sn.gX = 1)
    (h1 : ev tr 3 s pub (Sn.c "oEX") = 1)
    (hcont : ev tr 3 s pub (Sn.c "cont") = 0) (hold : OldOK σ (snIn tr pub s) (snOld tr pub s))
    (hM : ∀ k, k < 4 → ev tr 3 s pub (Sn.M.getD k 0) < 65536) :
    LocalOK (Sem σ (keyOf tr)) (snRow tr pub s) := by
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  obtain ⟨hlt, hkx, hK, hK2, hne, hdep⟩ := split_keys hH hxN hxL hs hX hcont
  obtain ⟨hdo, hmode, hin, hd, hkid, hvl, hvh, href, hnm, hom⟩ := split_row hc hX
  have hans := split_ans hH hD hx hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hS hBnew hBlim
    (fun p hp h => hF p hp (Or.inl h)) hs hX
  obtain ⟨hg, -, -, hXs⟩ := split_flags hc hX
  have hL0 : ev tr 3 s pub (Sn.c "oLX") = 0 := by omega
  have hisL : ev tr 3 s pub (Sn.c "isL") = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := sn_flags' hc hg
    rw [h]; snfacts hc hg; omega
  have hA : ev tr 3 s pub (Sn.c "act") = 1 := (sn_flags' hc hg).2.1
  rw [RowSnM.snOld_ext (by omega)] at hold
  have hsplit := list_split hkx
  have hkl0 := (FieldRows2.sn_flags hc hcont).1
  have hlen : ((snKey tr pub s).take (ev tr 3 s pub (Sn.c "jm")) ++ ev tr 3 s pub (Sn.c "kj") ::
      (snKey tr pub s).drop (ev tr 3 s pub (Sn.c "jm") + 1)).length = ev tr 3 s pub (Sn.c "klen") := by
    rw [← hsplit, snKey_length]
  have hpl : ((snKey tr pub s).take (ev tr 3 s pub (Sn.c "jm"))).length = ev tr 3 s pub (Sn.c "jm") := by
    simp [snKey_length]; omega
  have hmem := ex_mem hH hxr hs h1 hA hcont hM
  have hsq : snQ tr pub s = ⟨ev tr 3 s pub (Sn.c "kid"), ev tr 3 s pub (Sn.c "kid2"), snOs tr pub s,
      ev tr 3 s pub (Sn.c "dvlen"), bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub))⟩ := rfl
  rw [hsq] at hans
  have e1 := ev_one_eval h1
  -- the old side
  have hos : OldSideX σ (keyOf tr) (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "jm") + 1)
      (ev tr 3 s pub (Sn.c "kid2")) (ev tr 3 s pub (Sn.c "d") + ev tr 3 s pub (Sn.c "klen")) (snChild tr pub s)
      (le4 (Sn.CM.map (E tr 3 s pub))) ((snKey tr pub s).drop (ev tr 3 s pub (Sn.c "jm") + 1)) (snOs tr pub s) := by
    have bz := bool_le (FieldRows2.sn_hold hc (e := bool (Sn.c "z")) (by unfold Sn.constraints; simp [Sn.ops]))
    have z1c := FieldRows2.sn_hold hc sn_mem_z1
    have z0c := FieldRows2.sn_hold hc sn_mem_z0
    have hxhf := eq_of_sub (FieldRows2.sn_hold hc sn_mem_xhf)
    unfold snOs
    rw [if_neg (by omega)]
    rcases Nat.lt_or_ge (ev tr 3 s pub (Sn.c "jm") + 1) (ev tr 3 s pub (Sn.c "klen")) with hgt | hle
    · -- `xs ≠ []`: `z = 0`, the re-keyed extension from `SXR`
      have hz : ev tr 3 s pub (Sn.c "z") = 0 := by
        rw [RowSnN.ev_gm h1] at z1c
        rcases (by omega : ev tr 3 s pub (Sn.c "z") = 0 ∨ ev tr 3 s pub (Sn.c "z") = 1) with h | h
        · exact h
        · exfalso
          rw [ev_hmul, h, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _), ev_sub, ev_sub, ev_one] at z1c
          have := ev_lt (tr := tr) (t := 3) (r := s) (pub := pub) (Sn.c "jm")
          have := ev_lt (tr := tr) (t := 3) (r := s) (pub := pub) (Sn.c "klen")
          omega
      obtain ⟨a, xs', hxs⟩ : ∃ a xs', (snKey tr pub s).drop (ev tr 3 s pub (Sn.c "jm") + 1) = a :: xs' := by
        cases h : (snKey tr pub s).drop (ev tr 3 s pub (Sn.c "jm") + 1) with
        | nil => exfalso; have := congrArg List.length h; simp [snKey_length] at this; omega
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
      have hxs : (snKey tr pub s).drop (ev tr 3 s pub (Sn.c "jm") + 1) = [] :=
        List.drop_eq_nil_of_le (by rw [snKey_length]; omega)
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
  rw [RowSnM.snOld_ext (by omega)] at hold
  refine localOK_extSplit (snRow tr pub s) hmode hdo (c := snChild tr pub s) (kid2 := ev tr 3 s pub (Sn.c "kid2"))
    (m := snMem tr pub s) (cm := le4 (Sn.CM.map (E tr 3 s pub)))
    (p := (snKey tr pub s).take (ev tr 3 s pub (Sn.c "jm"))) (x0 := ev tr 3 s pub (Sn.c "kj"))
    (xs := (snKey tr pub s).drop (ev tr 3 s pub (Sn.c "jm") + 1))
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

end

end StateM5a.SnSplitLoc
