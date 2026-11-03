import StateM5a.SnStore

/-!
# StateM5a.SnStore2 — the `SN` part of the version store; `sn_oldOK`, `sn_newOK`

See `SnStore` for the argument.  `snVers` is the `SN` part of the store (`VerStore.brVers` the
`BR` part); `vers_nodup` replaces the premise `hnd` of the assemblies.
-/

namespace StateM5a.SnStore2

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KeyDecode StateM5a.KeyDigest StateM5a.SnSer StateM5a.SnHashed StateM5a.SnRec
open StateM5a.SnVer StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnN StateM5a.SnStore

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Version ids of `SN` rows -/

section
variable {tr : Trace Fp} {pub : List Fp} {t r : Nat}

theorem sn_vid_c (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
    (hn : ev tr t r pub (Sn.c "nref") = 1) :
    ev tr t r pub (Sn.c "hn" 0) = ev tr t r pub Sn.nidN ∧
      ∀ b, b < 31 → ev tr t r pub (Sn.c "hn" (b + 1)) = 0 := by
  refine ⟨FieldVer.eq_of_gate (hold (L := Sn.constraints) rfl hc ?_) hn,
    fun b hb => FieldVer.gate_zero (hold (L := Sn.constraints) rfl hc ?_) hn⟩
  · unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind
  · unfold Sn.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind

end

/-- The version id of `SN` row `r`'s new node: limb 0 of its ref `hn`. -/
def snVid (tr : Trace Fp) (pub : List Fp) (r : Nat) : Nat :=
  (((pack2 fun b => Sn.c "hn" b).map (E tr 3 r pub)).getD 0 0).toNat

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

theorem snVid_val (hH : Holds (fullAir D extra nb np) pub tr) {r : Nat} (hr : r < tr.height 3)
    (hn : ev tr 3 r pub (Sn.c "nref") = 1) :
    snVid tr pub r = (256 * (3 * 2 ^ 24 + 2 * r + 1)) % P := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨h0, h1⟩ := sn_vid_c hc hn
  have hrid := sn_rid hH r hr
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by simp [fullAir, m5aAir])).2
  have hN : ev tr 3 r pub Sn.nidN = 3 * 2 ^ 24 + 2 * r + 1 := by
    unfold Sn.nidN
    rw [ev_id2' _ _ (by omega) (by decide), hrid]; rfl
  have hb1 := h1 0 (by decide)
  unfold snVid
  simp only [pack2, List.map_map, List.range, List.range.loop, List.map_cons, List.getD_cons_zero, Function.comp]
  show ev tr 3 r pub (K 256 * Sn.c "hn" (2 * 0) + Sn.c "hn" (2 * 0 + 1)) = _
  rw [ev_hadd, ev_hmul, ev3_K]
  simp only [Nat.mul_zero, Nat.zero_add] at hb1 ⊢
  rw [h0, hb1, hN]
  simp only [Nat.reduceMod]; omega

/-- The `SN` rows' version-id publications `(id, new record)`. -/
def snVers (tr : Trace Fp) (pub : List Fp) : List (Nat × Rec) :=
  ((List.range (tr.height 3)).filter fun r =>
      decide (ev tr 3 r pub (Sn.c "nref") = 1 ∧ ev tr 3 r pub (Sn.c "gnew") = 1)).map
    fun r => (snVid tr pub r, snNew tr pub r)

/-- **The `BR` and `SN` version ids are distinct.** -/
theorem vers_nodup (hH : Holds (fullAir D extra nb np) pub tr) :
    ((VerStore.brVers tr pub ++ snVers tr pub).map (·.1)).Nodup := by
  have hH2 : tr.height 2 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 2 (by simp [fullAir, m5aAir])).2
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by simp [fullAir, m5aAir])).2
  rw [List.map_append, List.nodup_append]
  refine ⟨VerStore.brVers_nodup hH, ?_, ?_⟩
  · unfold snVers
    rw [List.map_map]
    refine VerStore.nodup_map_on _ _ (fun a ha b hb e => ?_) (List.nodup_range.filter _)
    obtain ⟨ha1, ha2⟩ := List.mem_filter.1 ha
    obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
    simp only [decide_eq_true_eq] at ha2 hb2
    have ha0 := List.mem_range.1 ha1; have hb0 := List.mem_range.1 hb1
    simp only [Function.comp] at e
    rw [snVid_val hH ha0 ha2.1, snVid_val hH hb0 hb2.1] at e
    omega
  · intro x hx y hy hxy
    subst hxy
    simp only [VerStore.brVers, snVers, List.map_map, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq, Function.comp] at hx hy
    obtain ⟨a, ⟨ha0, ha1, -⟩, rfl⟩ := hx
    obtain ⟨b, ⟨hb0, hb1, -⟩, e⟩ := hy
    rw [VerStore.brVid_val hH ha0 ha1, snVid_val hH hb0 hb1] at e
    omega

theorem snVers_hv (hH : Holds (fullAir D extra nb np) pub tr) :
    ∀ r, r < tr.height 3 → ev tr 3 r pub (Sn.c "nref") = 1 → ev tr 3 r pub (Sn.c "gnew") = 1 →
      storeOf (VerStore.brVers tr pub ++ snVers tr pub) (snVid tr pub r) = some (snNew tr pub r) := by
  intro r hr hn hg
  apply storeOf_mem (vers_nodup hH)
  apply List.mem_append_right
  exact List.mem_map.2 ⟨r, List.mem_filter.2 ⟨List.mem_range.2 hr, by simp [hn, hg]⟩, rfl⟩

end

/-! ## `NewOK` and `OldOK` -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : XSbHi D extra nb np tr pub)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
  (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)

theorem sn_flag_le' {r : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0) (s : String)
    (hs : s = "nref" ∨ s = "oref" ∨ s = "gsha" ∨ s = "cont") : ev tr 3 r pub (Sn.c s) ≤ 1 := by
  apply bool_le
  apply FieldRows.hold (L := Sn.constraints) rfl hc
  unfold Sn.constraints
  simp only [List.mem_append, List.mem_map]
  repeat apply Or.inl
  refine ⟨s, ?_, rfl⟩
  rcases hs with rfl | rfl | rfl | rfl <;> simp [Sn.ops]

include hH hxB hxD hxK hN hxr in
/-- **A row with a new node publishes it** (`cont = 0`). -/
theorem sn_newOK {r : Nat} (hr : r < tr.height 3) (hg : ev tr 3 r pub (Sn.c "gnew") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) :
    NewOK (storeOf (VerStore.brVers tr pub ++ snVers tr pub)) (snOut tr pub r) (snNew tr pub r) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hnb := sn_flag_le' hc "nref" (Or.inl rfl)
  rcases (by omega : ev tr 3 r pub (Sn.c "nref") = 0 ∨ ev tr 3 r pub (Sn.c "nref") = 1) with hn | hn
  · have hR := (sn_new_node hH hxB hxD hxK hN hxr hr hg hn hcont).2
    right
    refine ⟨_, ?_, hR.1, hR.2.2.2⟩
    unfold snOut; exact VerStore.refOf_dig _ _ (VerStore.pack2_len fun b => Sn.c "hn" b) hn
  · left
    refine ⟨snVid tr pub r, ?_, snVers_hv hH r hr hn hg⟩
    unfold snOut; exact VerStore.refOf_vid _ _ (by show ev tr 3 r pub (Sn.c "nref") ≠ 0; omega)

theorem sn_mem_gor : Sn.c "gsha" * Sn.c "oref" ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp

include hH hxB hxD hxK hN hxr hxV in
set_option maxHeartbeats 8000000 in
/-- **The old record of an `SN` row reading its node** (`gold`, `cont = 0`) is `OldOK`. -/
theorem sn_oldOK (hCR : Walk.Sha256CR) {r : Nat} (hr : r < tr.height 3)
    (hg : ev tr 3 r pub (Sn.c "gold") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 0) :
    OldOK (storeOf (VerStore.brVers tr pub ++ snVers tr pub)) (snIn tr pub r) (snOld tr pub r) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by simp [fullAir, m5aAir])).2
  have hsb := sn_flag_le' hc "gsha" (by simp)
  have hob := sn_flag_le' hc "oref" (by simp)
  by_cases hs : ev tr 3 r pub (Sn.c "gsha") = 1
  · have ho : ev tr 3 r pub (Sn.c "oref") = 0 := FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gor) hs
    unfold snIn
    rw [VerStore.refOf_dig _ _ (VerStore.pack2_len fun b => Sn.c "ho" b) ho]
    exact VerStore.oldOK_dig (sn_old_node hH hxB hxD hxK hN hxr hr hs hcont).2
  have hs0 : ev tr 3 r pub (Sn.c "gsha") = 0 := by omega
  have hrd : (Sn.c "gold" - Sn.c "gsha").eval tr 3 r pub = 1 := ev_one_eval (by rw [ev_sub, hg, hs0])
  have hpub : ∀ p, p < 3 → ∃ r' nw, r' < tr.height 3 ∧ ev tr 3 r' pub (Sn.c "cont") = 0 ∧
      (nw = false → ev tr 3 r' pub (Sn.c "gsha") = 1) ∧ (nw = true → ev tr 3 r' pub (Sn.c "gnew") = 1) ∧
      (sRdE p).map (E tr 3 r pub) = (pE nw p).map (E tr 3 r' pub) := by
    intro p hp
    obtain ⟨r', hr', hco, (⟨hgs, hm⟩ | ⟨hgn, hm⟩)⟩ := sn_rd_part hH hxV hr hrd p hp
    · exact ⟨r', false, hr', hco, fun _ => hgs, fun h => absurd h (by decide), hm⟩
    · exact ⟨r', true, hr', hco, fun h => absurd h (by decide), fun _ => hgn, hm⟩
  rcases (by omega : ev tr 3 r pub (Sn.c "oref") = 0 ∨ ev tr 3 r pub (Sn.c "oref") = 1) with ho | ho
  · -- under a digest: every part from a record hashed to it
    have hdig : snIn tr pub r = .dig (bytesOf ((pack2 fun b => Sn.c "ho" b).map (E tr 3 r pub))) := by
      unfold snIn; exact VerStore.refOf_dig _ _ (VerStore.pack2_len fun b => Sn.c "ho" b) ho
    have hrec : ∀ p, p < 3 → ∃ r' nw, r' < tr.height 3 ∧ ev tr 3 r' pub (Sn.c "cont") = 0 ∧
        (sRdE p).map (E tr 3 r pub) = (pE nw p).map (E tr 3 r' pub) ∧
        Hashed (gRecS tr pub r' (pX nw) (pXF nw) (pMB nw))
          (bytesOf ((pack2 fun b => Sn.c "ho" b).map (E tr 3 r pub))) := by
      intro p hp
      obtain ⟨r', nw, hr', hco, h0, h1, hm⟩ := hpub p hp
      obtain ⟨efl, eref⟩ := fl_ref hp hm
      cases nw
      · refine ⟨r', false, hr', hco, hm, ?_⟩
        rw [pRec_false]
        have e : (pack2 fun b => Sn.c "ho" b).map (E tr 3 r pub) =
            (pack2 fun b => Sn.c "ho" b).map (E tr 3 r' pub) := eref
        rw [e]; exact (sn_old_node hH hxB hxD hxK hN hxr hr' (h0 rfl) hco).2
      · have e := congrArg Fp.toNat efl
        change ev tr 3 r pub (Sn.c "oref") = ev tr 3 r' pub (Sn.c "nref") at e
        refine ⟨r', true, hr', hco, hm, ?_⟩
        rw [pRec_true]
        have e2 : (pack2 fun b => Sn.c "ho" b).map (E tr 3 r pub) =
            (pack2 fun b => Sn.c "hn" b).map (E tr 3 r' pub) := eref
        rw [e2]; exact (sn_new_node hH hxB hxD hxK hN hxr hr' (h1 rfl) (by omega) hco).2
    obtain ⟨a, na, ha, hca, hma, hHa⟩ := hrec 0 (by decide)
    obtain ⟨b, nb', hb, hcb, hmb, hHb⟩ := hrec 1 (by decide)
    obtain ⟨c, nc, hc3, hcc, hmc, hHc⟩ := hrec 2 (by decide)
    have eb := hashed_agree hCR hHb hHa
    have ec := hashed_agree hCR hHc hHa
    have kb : snKey tr pub b = snKey tr pub a := by
      have := congrArg Rec.key eb; rwa [gRecS_key, gRecS_key] at this
    have kc : snKey tr pub c = snKey tr pub a := by
      have := congrArg Rec.key ec; rwa [gRecS_key, gRecS_key] at this
    have hF := fields0 hma
    have hla := (FieldRows2.sn_flags (tbl_sn D extra nb np hH a (List.mem_range.2 ha)) hca).1
    have hk := key_of_parts hF.klen hla (fields1 hmb) (fields2 hmc) kb kc
    have hrecEq : snOld tr pub r = gRecS tr pub a (pX na) (pXF na) (pMB na) := by
      rw [snOld_eq]; exact grec_of_fields hF hk
    rw [hdig, hrecEq]
    exact VerStore.oldOK_dig hHa
  · -- under a version id: every part from the one row with that id
    have hvid : snIn tr pub r = .vid (((pack2 fun b => Sn.c "ho" b).map (E tr 3 r pub)).getD 0 0).toNat := by
      unfold snIn; exact VerStore.refOf_vid _ _ (by show ev tr 3 r pub (Sn.c "oref") ≠ 0; omega)
    have hv : ∀ p, p < 3 → ∃ r', r' < tr.height 3 ∧ ev tr 3 r' pub (Sn.c "cont") = 0 ∧
        ev tr 3 r' pub (Sn.c "nref") = 1 ∧ ev tr 3 r' pub (Sn.c "gnew") = 1 ∧
        (pack2 fun b => Sn.c "ho" b).map (E tr 3 r pub) = (pack2 fun b => Sn.c "hn" b).map (E tr 3 r' pub) ∧
        (sRdE p).map (E tr 3 r pub) = (pE true p).map (E tr 3 r' pub) := by
      intro p hp
      obtain ⟨r', nw, hr', hco, h0, h1, hm⟩ := hpub p hp
      obtain ⟨efl, eref⟩ := fl_ref hp hm
      cases nw
      · exfalso
        have e := congrArg Fp.toNat efl
        change ev tr 3 r pub (Sn.c "oref") = ev tr 3 r' pub (0 : Expr) at e
        rw [show ev tr 3 r' pub (0 : Expr) = 0 from ev_const 0] at e
        omega
      · have e := congrArg Fp.toNat efl
        change ev tr 3 r pub (Sn.c "oref") = ev tr 3 r' pub (Sn.c "nref") at e
        exact ⟨r', hr', hco, by omega, h1 rfl, eref, hm⟩
    obtain ⟨s, hs3, hcs, hns, hgs, hls, -⟩ := hv 0 (by decide)
    have hsame : ∀ p, p < 3 → (sRdE p).map (E tr 3 r pub) = (pE true p).map (E tr 3 s pub) := by
      intro p hp
      obtain ⟨r', hr', -, hn', -, hl', hm'⟩ := hv p hp
      have e : snVid tr pub r' = snVid tr pub s := by unfold snVid; rw [← hl', ← hls]
      rw [snVid_val hH hr' hn', snVid_val hH hs3 hns] at e
      have : r' = s := by omega
      rw [hm', this]
    have hF := fields0 (hsame 0 (by decide))
    have hla := (FieldRows2.sn_flags (tbl_sn D extra nb np hH s (List.mem_range.2 hs3)) hcs).1
    have hk := key_of_parts hF.klen hla (fields1 (hsame 1 (by decide))) (fields2 (hsame 2 (by decide))) rfl rfl
    have hrecEq : snOld tr pub r = snNew tr pub s := by
      rw [snOld_eq, ← pRec_true]; exact grec_of_fields hF hk
    left
    refine ⟨snVid tr pub s, ?_, ?_⟩
    · rw [hvid]; unfold snVid; rw [hls]
    · rw [hrecEq]; exact snVers_hv hH s hs3 hns hgs

end

end StateM5a.SnStore2
