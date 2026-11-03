import StateM5a.SnSplitLoc

/-!
# StateM5a.SnFinal3 — `air_final_sorted_sn2` with `OslApart` and the short-key splits from `Holds`

**`air_final_sorted_sn3`**: `SnResp.air_final_sorted_sn2` with

* `hOsl` (`BrMat.OslApart`) discharged (`WalkEnd.oslApart`);
* `hrest` (`SnRest2`) discharged for the splits `oLX` / `oEX` with a short key (`cont = 0`,
  `SnSplitLoc.localOK_oLX` / `localOK_oEX`); the rows with a continued key remain the premise
  `SnContRest` (they are all of `SnRest2` but the splits);
* the split protocol's responder facts reduced to: `SnFreshNew` (short-key `oEP`/`oEM`: new record
  `NewOK`, 16-bit limbs of `nmem` and of the received `unm`), `SnFreshLong` (`FreshRel` of the
  continued-key `oEP`/`oEM` rows), `OslNodeLimbs` (the `oSL` row's `nm2` limbs when the old side is a
  node, i.e. the split row's `xm`); the `oSL` rows' `NewOK` (`VerStore.br_newOK`), `nmem` limbs
  (`BrRange.br_NM_lt`), and the `MATR` answer limbs (`BrRange.matr_sent_lt`) are from `Holds`.
* `hlongS` / `hlongM` (continued-key responders) unchanged.
-/

namespace StateM5a.SnFinal3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.SnSplitLoc StateM5a.RowSnAll StateM5a.RowSnAll2
open StateM5a.SnAssembly StateM5a.SnResp

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- **Premise**: a short-key fresh-extension row (`oEP`/`oEM`) publishes its new record, and its
memory limbs (its `nmem`, the received `unm`) are 16-bit. -/
def SnFreshNew (σ : Store) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ p, p < tr.height 3 → (ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) →
    ev tr 3 p pub (Sn.c "cont") = 0 →
    NewOK σ (snOut tr pub p) (snNew tr pub p) ∧ (∀ k, k < 4 → ev tr 3 p pub (Sn.NM.getD k 0) < 65536) ∧
      (∀ k, k < 4 → ev tr 3 p pub (Sn.c "unm" k) < 65536)

/-- **Premise**: a continued-key fresh-extension row establishes `FreshRel`. -/
def SnFreshLong (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ p, p < tr.height 3 → (ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) →
    ev tr 3 p pub (Sn.c "cont") = 1 → FreshRel σ keyOf tr pub p

/-- **Premise**: the old-side memory limbs `nm2` of a split's new branch over a node (`xl = 0`). -/
def OslNodeLimbs (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → ev tr 2 r pub (Br.c "xl") = 0 →
    ∀ k, k < 4 → ev tr 2 r pub (Br.c "nm2" k) < 65536

/-- **Premise**: the active `SN` rows with a continued key (`cont = 1`). -/
def SnContRest (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 → ev tr 3 r pub (Sn.c "cont") = 1 →
    LocalOK (Sem σ keyOf) (snRow tr pub r)

theorem brMatR2_nm : ∀ k : Nat, k < 4 → brMatR2[20 + k]? = some (Br.c "nm2" k) := by decide

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 8000000 in
/-- The limbs of an `oSL` row: `nmem` (new node), `nm` (`MATR`), `nm2` (`MATR` when re-keyed). -/
theorem osl_limbs (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false) (hSM : SnMatLimbs tr pub)
    (hON : OslNodeLimbs tr pub) {r : Nat} (hr : r < tr.height 2) (h1 : ev tr 2 r pub (Br.c "oSL") = 1) :
    ∀ k, k < 4 → ev tr 2 r pub (Br.NM.getD k 0) < 65536 ∧ ev tr 2 r pub (Br.c "nm" k) < 65536 ∧
      ev tr 2 r pub (Br.c "nm2" k) < 65536 := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨hA, hgn, -, -, -, -, -, -, -, -, hUN, -, -, hDL, -⟩ := osl_flags hc h1
  have h2 : 2 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hgm : ev tr 2 r pub (Br.c "oDL" + Br.c "oUN" + Br.c "oSL") = 1 := by
    rw [RowBr.ev_add_lt (by rw [RowBr.ev_add_lt (by omega)]; omega), RowBr.ev_add_lt (by omega)]; omega
  intro k hk
  refine ⟨br_NM_lt hH hxB hxD hxK hxr hr hgn k hk, ?_, ?_⟩
  · have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_matr_r) hr rfl (ev_one_eval hgm)
    have a := matr_sent_lt hxM hSM (recv_sent hH hm) (20 + k) (by omega) (by omega)
    simp only [Interaction.msgVal] at a
    rw [getD_map_some (brMatR_nm k hk)] at a
    exact a
  · have bx := bool_le (FieldRows2.br_hold hc br_mem_xl)
    rcases (by omega : ev tr 2 r pub (Br.c "xl") = 0 ∨ ev tr 2 r pub (Br.c "xl") = 1) with h0 | hx1
    · exact hON r hr h1 h0 k hk
    · have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
        (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_matr2_r) hr rfl
        (by rw [eval_mul, ev_one_eval h1, ev_one_eval hx1]; grind)
      have a := matr_sent_lt hxM hSM (recv_sent hH hm) (20 + k) (by omega) (by omega)
      simp only [Interaction.msgVal] at a
      rw [getD_map_some (brMatR2_nm k hk)] at a
      exact a

end

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 StateM5a.VerStore StateM5a.VerAssembly in
set_option maxHeartbeats 8000000 in
/-- **Batched FINAL in the spec's order** (`SnResp.air_final_sorted_sn2`) with `OslApart` and the
short-key split rows discharged from `Holds`. -/
theorem air_final_sorted_sn3 {tr : Trace Fp} {pub : List Fp} (D : Nat)
    (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table) (nb np : Nat)
    {compress : List Nat → List Nat → List Nat}
    (hP : Prem tr pub D (tapeTable (m5aTape writes prev post n) :: rest) nb np compress)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH)
    (hrN : ∀ T ∈ rest, sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KC = false ∧
      sendsOn T.interactions B_KCR = false)
    (hrS : ∀ T ∈ rest, sendsOn T.interactions B_MATQ = false ∧ sendsOn T.interactions B_MATR = false ∧
      sendsOn T.interactions B_SIBQ = false ∧ sendsOn T.interactions B_SIBA = false)
    (hrX : ∀ T ∈ rest, sendsOn T.interactions B_SPQ = false ∧ sendsOn T.interactions B_SPR = false ∧
      sendsOn T.interactions B_EPQ = false ∧ sendsOn T.interactions B_SXQ = false ∧
      sendsOn T.interactions B_SXR = false)
    (hxV : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions B_VER = false)
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (snVers : List (Nat × Rec))
    (hnd : ((brVers tr pub ++ snVers).map (·.1)).Nodup)
    (hSU : BrRange.SnUpLimbs tr pub) (hSM : BrRange.SnMatLimbs tr pub)
    (hVl : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ev tr 2 r pub (Br.c "gsha") = 0 →
      ∀ k, k < 2 → ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) k) < 65536)
    (hVP : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → brVlen tr pub r < 2013265921)
    (hold : SnOldAll (storeOf (brVers tr pub ++ snVers)) tr pub)
    (hnew : SnNewAll (storeOf (brVers tr pub ++ snVers)) tr pub)
    (holdS : SnOldAny (storeOf (brVers tr pub ++ snVers)) tr pub)
    (hnewM : SnNewAny (storeOf (brVers tr pub ++ snVers)) tr pub)
    (hlim : SnLimbs3 tr pub) (hlm : SnLeafMemLt tr pub) (hleaf : SnMatLeaf tr pub)
    (hFN : SnFreshNew (storeOf (brVers tr pub ++ snVers)) tr pub)
    (hFL : SnFreshLong (storeOf (brVers tr pub ++ snVers)) (keyOf tr) tr pub)
    (hON : OslNodeLimbs tr pub)
    (hcr : SnContRest (storeOf (brVers tr pub ++ snVers)) (keyOf tr) tr pub)
    (hlongS : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLS") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      SibRel (storeOf (brVers tr pub ++ snVers)) (keyOf tr) (ev tr 3 s pub (Sn.c "d"))
        (refOf (E tr 3 s pub (Sn.c "oref")) ((pack2 fun b => Sn.c "ho" b).map (E tr 3 s pub)))
        (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t))
        (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub))))
    (hlongM : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLM") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      MatRel (storeOf (brVers tr pub ++ snVers)) (keyOf tr) (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.c "d"))
        (ev tr 3 s pub (Sn.c "dvlen"))
        (bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub)))
        (refOf (E tr 3 s pub (Sn.c "nref")) ((pack2 fun b => Sn.c "hn" b).map (E tr 3 s pub)))
        (le4 (Sn.NM.map (E tr 3 s pub))))
    (cs : List (Bytes × Option Bytes)) (hlen : cs.length = n) (hcs : FinalChanges tr pub cs)
    (committed : List (Bytes × Option Bytes)) (hcomm : committed.Perm cs)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) (sortKV committed) = some (some T') ∧ rootHash (some T') = post := by
  have tp : ∀ b, b ≠ B_WRITE → b ≠ B_TCH → (∀ T ∈ rest, sendsOn T.interactions b = false) →
      ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions b = false :=
    fun b h1 h2 h T hT => by
      rcases List.mem_cons.1 hT with rfl | hT
      · exact tape_not writes prev post n b h1 h2
      · exact h T hT
  have hH := hP.hH
  have hD30 : D ≤ 30 := by have := hP.hD; omega
  have hxN := fun T hT => (hP.hsil T hT).1
  have hxL := fun T hT => (hP.hsil T hT).2.1
  have hxB := fun T hT => (hP.hsil T hT).2.2.2.1
  have hxD := fun T hT => (hP.hsil T hT).2.2.2.2.1
  have hxK := fun T hT => (hP.hsil T hT).2.2.2.2.2.1
  have hxr : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, ∀ i ∈ T.interactions, i.bus ≠ B_RNG :=
    fun T hT i hi => (hP.hx T hT i hi).2.2.2.1
  have hxR := tp B_KCR (by decide) (by decide) (fun T hT => (hrN T hT).2.2)
  have hxDU : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, ∀ i ∈ T.interactions,
      i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP := fun T hT i hi => by
    rcases List.mem_cons.1 hT with rfl | hT
    · rcases tape_bus writes prev post n i hi with e | e <;> rw [e] <;> decide
    · exact ⟨(hr T hT i hi).1, (hr T hT i hi).2.1⟩
  have hxMQ := tp B_MATQ (by decide) (by decide) (fun T hT => (hrS T hT).1)
  have hxM := tp B_MATR (by decide) (by decide) (fun T hT => (hrS T hT).2.1)
  have hxQ := tp B_SPQ (by decide) (by decide) (fun T hT => (hrX T hT).1)
  have hxP := tp B_SPR (by decide) (by decide) (fun T hT => (hrX T hT).2.1)
  have hxE := tp B_EPQ (by decide) (by decide) (fun T hT => (hrX T hT).2.2.1)
  have hxSQ := tp B_SXQ (by decide) (by decide) (fun T hT => (hrX T hT).2.2.2.1)
  have hxSR := tp B_SXR (by decide) (by decide) (fun T hT => (hrX T hT).2.2.2.2)
  -- the responders
  have hMat := snMatOK_of hH hxN hxL hnewM hSM hleaf hlongM
  have hBnew : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 →
      NewOK (storeOf (brVers tr pub ++ snVers)) (brOut tr pub r) (brNew tr pub r) := fun r hr' h1 => by
    have hc := tbl_br D _ nb np hH r (List.mem_range.2 hr')
    exact br_newOK hH (BrDigest.brHashed hH hxB hxD hxK) _ (brVers_hv hH snVers hnd) hr' (osl_flags hc h1).2.1
  have hBlim := fun r hr' h1 => osl_limbs hH hxB hxD hxK hxr hxM hSM hON (r := r) hr' h1
  have hFr : ∀ p, p < tr.height 3 → (ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) →
      FreshRel (storeOf (brVers tr pub ++ snVers)) (keyOf tr) tr pub p := by
    intro p hp h
    have hc := tbl_sn D _ nb np hH p (List.mem_range.2 hp)
    have hcb := FieldRows2.sn_bool hc "cont" (by simp)
    rcases (by omega : ev tr 3 p pub (Sn.c "cont") = 0 ∨ ev tr 3 p pub (Sn.c "cont") = 1) with h0 | h1
    · obtain ⟨a, b, c⟩ := hFN p hp h h0
      exact fresh_short hH hxN hp h h0 a b c
    · exact hFL p hp h h1
  -- `SnRest2`
  have hrest : SnRest2 (storeOf (brVers tr pub ++ snVers)) (keyOf tr) tr pub := by
    intro r hr' hg hops
    have hc := tbl_sn D _ nb np hH r (List.mem_range.2 hr')
    have hcb := FieldRows2.sn_bool hc "cont" (by simp)
    rcases (by omega : ev tr 3 r pub (Sn.c "cont") = 0 ∨ ev tr 3 r pub (Sn.c "cont") = 1) with h0 | h1
    · have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := eval_one_ev hg
      have hX : ev tr 3 r pub Sn.gX = 1 := by
        unfold Sn.gX
        snfacts hc hg'
        rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]
        omega
      rcases hops with h | h | h
      · omega
      · exact localOK_oLX hH hD30 hxDU hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hMat hBnew hBlim hFr hr' hX h h0
          (hold r hr' hg h0)
      · exact localOK_oEX hH hD30 hxDU hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hxSQ hxSR hxr hMat hBnew hBlim hFr
          hr' hX h h0 (hold r hr' hg h0) (hlim r hr' hg h0).mem
    · exact hcr r hr' hg h1
  exact air_final_sorted_sn2 D writes prev post n rest nb np hP hr hrN hrS hxV hn hprev hpost snVers hnd hSU hSM
    hVl hVP (oslApart hH hD30 hxDU hxN hxL hxK hxR hxQ) hold hnew holdS hnewM hlim hlm hleaf hrest hlongS hlongM
    cs hlen hcs committed hcomm T hT0 hF

end StateM5a.SnFinal3
