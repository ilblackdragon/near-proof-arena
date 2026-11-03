import StateM5a.SnContKey4
import StateM5a.RowSnN
import StateM5a.SnRange

/-!
# StateM5a.SnContKey5 — the old / new node of a continued head over its full key

* **`cont_old`** (`gold`) / **`cont_new`** (`gnew`): a key `K` with `ContKey` whose record is the
  row's `OldOK σ snIn` / `NewOK σ snOut` (any store: a continued node is hashed), plus the byte
  facts of the payload and memory columns;
* `contKey_eq`: two `ContKey`s of a row with `gA = 0` agree (both are the walk key's segment);
* `contKey_drop` / `contKey_drop2`: `K_kid[d..] = K ++ K_kid[d + klen ..]` (`gA = 0`), resp. against
  `kid2` (`g2 = 1`); `contKey_dlen`: `d + klen ≤ |K_kid| ≤ 2^21`;
* `contKey_hp`: `|hexPrefix K b| = hplen`; `cont_klen`: `klen = 62 + odd + rl`, `rl` even, small;
* **`cont_leaf_nmem`**: the new leaf's memory on a continued `oLR` / `oLM` row is `< P` and is
  `leafMem K vlen` (the AIR's equation `limb₀ + 65536·limb₁ = 100 + 2·hplen + vlen`, top byte `≤ 1`).
-/

namespace StateM5a.SnContKey5

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.BrDigest StateM5a.BrSer StateM5a.SnSer
open StateM5a.KeyDecode StateM5a.SnDigest StateM5a.SnContHead StateM5a.SnContMem StateM5a.SnRec
open StateM5a.SnContRec1 StateM5a.SnContRec2 StateM5a.SnContRec3 StateM5a.RowSnMsg StateM5a.RowSnN
open StateM5a.SnHashed StateM5a.SnStore2 StateM5a.SnContKey4 StateM5a.SnContKey3

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Pure -/

theorem drop_of_get {kk K : List Nat} {d L : Nat} (hl : K.length = L) (h : ∀ j, j < L → kk[d + j]? = K[j]?) :
    kk.drop d = K ++ kk.drop (d + L) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  by_cases hi : i < L
  · rw [List.getElem?_append_left (by omega), h i hi]
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop, hl]
    congr 1; omega

theorem eq_of_get {kk K K' : List Nat} {d L : Nat} (hl : K.length = L) (hl' : K'.length = L)
    (h : ∀ j, j < L → kk[d + j]? = K[j]?) (h' : ∀ j, j < L → kk[d + j]? = K'[j]?) : K = K' := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < L
  · rw [← h j hj, h' j hj]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ## Instances -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
  (hCR : Walk.Sha256CR)

include hH hxB hxD hxK hxR hxRr hN hxr hCR in
/-- **A continued head's old node over its full key** (`gold`). -/
theorem cont_old (σ : Store) {r : Nat} (hr : r < tr.height 3) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hg : ev tr 3 r pub (Sn.c "gold") = 1) :
    ∃ K, ContKey tr pub r K ∧
      OldOK σ (snIn tr pub r) (gRecK tr pub r K (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b)) ∧
      (∀ t, t < payLen tr pub r → ev tr 3 r pub (Sn.c "x" t) < 256) ∧
      (∀ b, b < 8 → ev tr 3 r pub (Sn.c "mem" b) < 256) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hs := ch_gsha hc hcont hg
  have hA := SnRec.sn_act_of hH hr (Or.inl hs)
  obtain ⟨K, hK, hR, hp, hm⟩ := cont_key hH hxB hxD hxK hxR hxRr hN hxr hCR hr (par := 0)
    (Nat.zero_le _) (SnRec.ev_idS hH hr).1 rfl sn_sd_old
    (fun i hi hb hs hh => mem_of_filter sn_sb_old hi (pred_true hb hs hh)) hs hA hcont
    (fun h1 => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_x3) h1)
    (fun _ => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gxf) hs) (xf := Sn.c "xf")
  refine ⟨K, hK, ?_, hp, hm⟩
  have ho : ev tr 3 r pub (Sn.c "oref") = 0 := FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gor) hs
  unfold snIn
  rw [VerStore.refOf_dig _ _ (VerStore.pack2_len fun b => Sn.c "ho" b) ho]
  exact VerStore.oldOK_dig hR

include hH hxB hxD hxK hxR hxRr hN hxr hCR in
/-- **A continued head's new node over its full key** (`gnew`). -/
theorem cont_new (σ : Store) {r : Nat} (hr : r < tr.height 3) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hg : ev tr 3 r pub (Sn.c "gnew") = 1) :
    ∃ K, ContKey tr pub r K ∧
      NewOK σ (snOut tr pub r) (gRecK tr pub r K (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b)) ∧
      (∀ t, t < payLen tr pub r → ev tr 3 r pub (Sn.c "nx" t) < 256) ∧
      (∀ b, b < 8 → ev tr 3 r pub (Sn.c "nmem" b) < 256) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hf := ch_gfin hc hcont hg
  have hA := SnRec.sn_act_of hH hr (Or.inr hg)
  obtain ⟨hfl, h1, h2, h3, h4, h5, h6, -, h9⟩ := sn_ops hc
  have := hfl "oLR" (by simp [RowSn.snNames]); have := hfl "oLM" (by simp [RowSn.snNames])
  have := hfl "act" (by simp [RowSn.snNames])
  obtain ⟨K, hK, hR, hp, hm⟩ := cont_key hH hxB hxD hxK hxR hxRr hN hxr hCR hr (par := 1)
    (Nat.le_refl _) (SnRec.ev_idS hH hr).2 rfl sn_sd_new
    (fun i hi hb hs hh => mem_of_filter sn_sb_new hi (pred_true hb hs hh)) hf hA hcont
    (fun hl => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_nx3) (by rw [ev_hadd]; omega))
    (fun _ => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gnxf) hf) (xf := Sn.c "nxf")
  refine ⟨K, hK, ?_, hp, hm⟩
  right
  refine ⟨_, ?_, hR.1, hR.2.2.2⟩
  unfold snOut; exact VerStore.refOf_dig _ _ (VerStore.pack2_len fun b => Sn.c "hn" b) (ch_nref hc hcont)

include hH hxK hxR in
/-- `klen = 62 + odd + rl`, `rl` even and small, `hplen = 32 + rl/2` (a continued head). -/
theorem cont_klen {r : Nat} (hr : r < tr.height 3) (hA : ev tr 3 r pub (Sn.c "act") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 1) :
    ev tr 3 r pub (Sn.c "klen") = 62 + ev tr 3 r pub (Sn.c "odd") + ev tr 3 r pub (Sn.c "rl") ∧
    ev tr 3 r pub (Sn.c "rl") % 2 = 0 ∧ ev tr 3 r pub (Sn.c "rl") ≤ 64 * 2 ^ 20 ∧
    ev tr 3 r pub (Sn.c "hplen") = 32 + ev tr 3 r pub (Sn.c "rl") / 2 ∧ ev tr 3 r pub (Sn.c "odd") ≤ 1 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨h1, h2⟩ := cont_rl hH hxK hxR hr hcont
  exact ⟨ch_klen hc hcont (by omega), h1, h2, cont_hplen hH hxK hxR hr hA hcont,
    FieldRows2.sn_bool hc "odd" (by simp)⟩

end

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat} {K : List Nat}

theorem contKey_eq {K' : List Nat} (hK : ContKey tr pub r K) (hK' : ContKey tr pub r K')
    (hA0 : ev tr 3 r pub (Sn.c "gA") = 0) : K = K' :=
  eq_of_get hK.len hK'.len (fun j hj => hK.walk hA0 j hj) (fun j hj => hK'.walk hA0 j hj)

theorem contKey_drop (hK : ContKey tr pub r K) (hA0 : ev tr 3 r pub (Sn.c "gA") = 0) :
    (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")) =
      K ++ (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")) :=
  drop_of_get hK.len (hK.walk hA0)

theorem contKey_drop2 (hK : ContKey tr pub r K) (hg2 : ev tr 3 r pub (Sn.c "g2") = 1) :
    (keyOf tr (ev tr 3 r pub (Sn.c "kid2"))).drop (ev tr 3 r pub (Sn.c "d")) =
      K ++ (keyOf tr (ev tr 3 r pub (Sn.c "kid2"))).drop (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")) :=
  drop_of_get hK.len (hK.walk2 hg2)

/-- The walk key reaches past a continued key (`klen ≥ 1`): `d + klen ≤ |K_kid|`. -/
theorem contKey_dlen (hK : ContKey tr pub r K) (hA0 : ev tr 3 r pub (Sn.c "gA") = 0)
    (hk1 : 1 ≤ ev tr 3 r pub (Sn.c "klen")) :
    ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") ≤ (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).length := by
  have h := hK.walk hA0 (ev tr 3 r pub (Sn.c "klen") - 1) (by omega)
  rw [List.getElem?_eq_getElem (l := K) (by rw [hK.len]; omega)] at h
  have := (List.getElem?_eq_some_iff.1 h).1
  omega

theorem contKey_dlen2 (hK : ContKey tr pub r K) (hg2 : ev tr 3 r pub (Sn.c "g2") = 1)
    (hk1 : 1 ≤ ev tr 3 r pub (Sn.c "klen")) :
    ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") ≤ (keyOf tr (ev tr 3 r pub (Sn.c "kid2"))).length := by
  have h := hK.walk2 hg2 (ev tr 3 r pub (Sn.c "klen") - 1) (by omega)
  rw [List.getElem?_eq_getElem (l := K) (by rw [hK.len]; omega)] at h
  have := (List.getElem?_eq_some_iff.1 h).1
  omega

theorem contKey_hp (hK : ContKey tr pub r K) (b : Bool)
    (hkl : ev tr 3 r pub (Sn.c "klen") = 62 + ev tr 3 r pub (Sn.c "odd") + ev tr 3 r pub (Sn.c "rl"))
    (hev : ev tr 3 r pub (Sn.c "rl") % 2 = 0) (hpl : ev tr 3 r pub (Sn.c "hplen") = 32 + ev tr 3 r pub (Sn.c "rl") / 2)
    (ho : ev tr 3 r pub (Sn.c "odd") ≤ 1) :
    (hexPrefix K b).length = ev tr 3 r pub (Sn.c "hplen") := by
  rw [hp_length, hK.len, hkl, hpl]
  omega

end

/-! ## The new leaf's memory on a continued row -/

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

set_option maxHeartbeats 8000000 in
/-- **The new leaf's memory** on an `oLR` / `oLM` row whose memory bytes are bytes: `< P` and
`100 + 2·hplen + vlen` (any `cont`; `hplen < 2^26`). -/
theorem cont_leaf_nmem (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (g : ev tr 3 r pub (Sn.c "oLR" + Sn.c "oLM") = 1)
    (hb : ∀ b, b < 8 → ev tr 3 r pub (Sn.c "nmem" b) < 256)
    (hnx : ∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256) (hHp : ev tr 3 r pub (Sn.c "hplen") < 2 ^ 26) :
    snNMem tr pub r = 100 + 2 * ev tr 3 r pub (Sn.c "hplen") + ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t) ∧
      snNMem tr pub r < P := by
  have z : ∀ t, t < 4 → ev tr 3 r pub (Sn.c "nmem" (4 + t)) = 0 := fun t ht =>
    FieldVer.gate_zero (FieldRows2.sn_hold hc (sn_mem_nm0 t ht)) g
  have h3' : ev tr 3 r pub (Sn.c "nmem" 3) ≤ 1 := by
    have e := FieldRows.hold rfl hc SnRange.sn_mem_nm3
    have e1 : ev tr 3 r pub ((Sn.c "oLR" + Sn.c "oLM") * Sn.c "nmem" 3) = ev tr 3 r pub (Sn.c "nmem" 3) := by
      rw [ev_hmul, g, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)]
    apply bool_le
    show ev tr 3 r pub (Sn.c "nmem" 3 * (Sn.c "nmem" 3 - 1)) = 0
    rw [ev_hmul] at e ⊢
    rw [e1] at e
    exact e
  have l0 := ev3_limb16 (fun b => Sn.c "nmem" b) 0 (hb 0 (by omega)) (hb 1 (by omega))
  have l1 := ev3_limb16 (fun b => Sn.c "nmem" b) 1 (hb 2 (by omega)) (hb 3 (by omega))
  have l2 := ev3_limb16 (fun b => Sn.c "nmem" b) 2 (hb 4 (by omega)) (hb 5 (by omega))
  have l3 := ev3_limb16 (fun b => Sn.c "nmem" b) 3 (hb 6 (by omega)) (hb 7 (by omega))
  have z0 := z 0 (by omega); have z1 := z 1 (by omega); have z2 := z 2 (by omega); have z3 := z 3 (by omega)
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at z0 z1 z2 z3 l0 l1 l2 l3
  rw [z0, z1] at l2; rw [z2, z3] at l3
  simp only [Nat.mul_zero, Nat.add_zero] at l2 l3
  have hm := eq_of_sub (FieldVer.gate_zero (FieldRows2.sn_hold hc sn_mem_lm) g)
  have hv := ev_vlenOf_lt hnx
  have q1 := sub_ev hm (by omega)
  rw [ev_sm3] at q1; simp only [Nat.reduceMod] at q1
  rw [Nat.mod_eq_of_lt (show 2 * ev tr 3 r pub (Sn.c "hplen") < P by omega),
    Nat.mod_eq_of_lt (show 2 * ev tr 3 r pub (Sn.c "hplen") + ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t) < P by omega)] at q1
  have q2 := sub_ev q1 (by omega)
  rw [ev_lit3] at q2; simp only [Nat.reduceMod] at q2
  rw [Nat.mod_eq_of_lt (by omega)] at q2
  rw [ev_hadd, ev_sm3] at q2; simp only [Nat.reduceMod] at q2
  rw [l0, l1] at q2
  rw [snNMem_eq, l0, l1, l2, l3]
  generalize ev tr 3 r pub (Sn.c "nmem" 0) = a0 at *
  generalize ev tr 3 r pub (Sn.c "nmem" 1) = a1 at *
  generalize ev tr 3 r pub (Sn.c "nmem" 2) = a2 at *
  generalize ev tr 3 r pub (Sn.c "nmem" 3) = a3 at *
  generalize ev tr 3 r pub (Sn.c "hplen") = H at *
  generalize ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t) = V at *
  have hb1 := hb 1 (by omega)
  omega

end

end StateM5a.SnContKey5
