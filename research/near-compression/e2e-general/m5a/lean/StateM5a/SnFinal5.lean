import StateM5a.SnSplitLX
import StateM5a.SnSplitEX
import StateM5a.SnFreshLimbs

/-!
# StateM5a.SnFinal5 — batched FINAL with the short-key split rows and all memory limbs from `Holds`

**`air_final_sorted_sn5`** (M5a-7): `SnFinal4.air_final_sorted_sn4` with, newly from `Holds`:

* the short-key split rows `oLX` / `oEX` (`cont = 0`) `LocalOK` (`SnSplitLX.localOK_oLX`,
  `SnSplitEX.localOK_oEX`, through the split answer `SnSplit.split_ans`); their responders' facts:
  `FreshRel` of short-key `oEP` rows (`SnSplit.fresh_short` with `SnFreshLimbs.snFreshNew_of`), the
  `oSL` rows' `NewOK` (`VerStore.br_newOK`) and limbs (`osl_limbs`, `SnFreshLimbs.oslNodeLimbs_of`);
* `SnUpLimbs` / `SnMatLimbs` (`SnLimbsAll.snUpLimbs_of` / `snMatLimbs_of`).

Remaining premises — all about the rows with a **continued key** (`cont = 1`), named:
`SnContMem` (their memory limbs), `SnFreshLong` (`FreshRel` of continued-key `oEP`/`oEM`),
`SnContRest` (`LocalOK` of continued-key walk rows), `hlongS` / `hlongM` (continued-key `SIBA` /
`MATR` responders); plus `Sha256CR` and the chip contract (in `Prem`). Each is satisfiable on
honest traces (an honest continued-key row is a correct row of the spec's walk: its node is the
spec's node, memory `< 2^25`), and each is vacuous on traces without keys longer than the head
(T1, T2 and the synthetic cases have none).
-/

namespace StateM5a.SnFinal5

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.SnSplitLoc StateM5a.RowSnAll StateM5a.RowSnAll2
open StateM5a.SnAssembly StateM5a.SnResp StateM5a.SnLimbsAll StateM5a.SnFreshLimbs StateM5a.SnStore2 StateM5a.RowBrN

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- **Premise (continued keys)**: a continued-key fresh-extension row establishes `FreshRel`. -/
def SnFreshLong (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ p, p < tr.height 3 → (ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) →
    ev tr 3 p pub (Sn.c "cont") = 1 → FreshRel σ keyOf tr pub p

/-- **Premise (continued keys)**: the active `SN` walk rows with a continued key are `LocalOK`. -/
def SnContRest (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 → ev tr 3 r pub (Sn.c "cont") = 1 →
    LocalOK (Sem σ keyOf) (snRow tr pub r)

theorem brMatR2_nm : ∀ k : Nat, k < 4 → brMatR2[20 + k]? = some (Br.c "nm2" k) := by decide

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

set_option maxHeartbeats 8000000 in
/-- The limbs of an `oSL` row: `nmem` (new node), `nm` (`MATR`), `nm2` (`MATR` when re-keyed, the
split row's `xm` over a node). -/
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
    simp only [Interaction.msgVal, rcv] at a
    rw [getD_map_some (brMatR_nm k hk)] at a
    exact a
  · have bx := bool_le (FieldRows2.br_hold hc br_mem_xl)
    rcases (by omega : ev tr 2 r pub (Br.c "xl") = 0 ∨ ev tr 2 r pub (Br.c "xl") = 1) with h0 | hx1
    · exact hON r hr h1 h0 k hk
    · have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
        (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_matr2_r) hr rfl
        (by rw [eval_mul, ev_one_eval h1, ev_one_eval hx1]; grind)
      have a := matr_sent_lt hxM hSM (recv_sent hH hm) (20 + k) (by omega) (by omega)
      simp only [Interaction.msgVal, rcv] at a
      rw [getD_map_some (brMatR2_nm k hk)] at a
      exact a

set_option maxHeartbeats 4000000 in
/-- A split op on an active walk row: `gX = oLX + oEX = 1`. -/
theorem gX_of_split {r : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1)
    (h : ev tr 3 r pub (Sn.c "oLX") = 1 ∨ ev tr 3 r pub (Sn.c "oEX") = 1) : ev tr 3 r pub Sn.gX = 1 := by
  obtain ⟨hb, -, -, -, -, -, hs, -, hU, -⟩ := sn_flags' hc hg
  have b1 := hb "mU" (by simp [snNames])
  have hle : ev tr 3 r pub (Sn.c "oLX") + ev tr 3 r pub (Sn.c "oEX") ≤ 1 := by omega
  clear hb hs
  unfold Sn.gX; rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; omega

end

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 StateM5a.VerStore StateM5a.VerAssembly in
set_option maxHeartbeats 8000000 in
/-- **Batched FINAL in the spec's order from `Holds`**: every premise on a short-key row discharged
(M5a-7); the continued-key rows remain (`SnContMem`, `SnFreshLong`, `SnContRest`, `hlongS`,
`hlongM`). -/
theorem air_final_sorted_sn5 {tr : Trace Fp} {pub : List Fp} (D : Nat)
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
    (hCR : Walk.Sha256CR)
    (hCM : SnContMem tr pub)
    (hFL : SnFreshLong (storeOf (brVers tr pub ++ snVers tr pub)) (keyOf tr) tr pub)
    (hcr : SnContRest (storeOf (brVers tr pub ++ snVers tr pub)) (keyOf tr) tr pub)
    (hlongS : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLS") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      SibRel (storeOf (brVers tr pub ++ snVers tr pub)) (keyOf tr) (ev tr 3 s pub (Sn.c "d"))
        (refOf (E tr 3 s pub (Sn.c "oref")) ((pack2 fun b => Sn.c "ho" b).map (E tr 3 s pub)))
        (ev tr 3 s pub (Sn.c "kid")) (ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t))
        (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub))))
    (hlongM : ∀ s, s < tr.height 3 → ev tr 3 s pub (Sn.c "oLM") = 1 → ev tr 3 s pub (Sn.c "cont") = 1 →
      MatRel (storeOf (brVers tr pub ++ snVers tr pub)) (keyOf tr) (ev tr 3 s pub (Sn.c "kid"))
        (ev tr 3 s pub (Sn.c "d")) (ev tr 3 s pub (Sn.c "dvlen"))
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
  -- the limb premises (`SnLimbsAll`, `SnFreshLimbs`)
  have hSU := snUpLimbs_of hH hxB hxD hxK hxN hxr hxV hxP hCM
  have hSM := snMatLimbs_of hH hxB hxD hxK hxN hxr hCM
  have hON := oslNodeLimbs_of hH hxB hxD hxK hxN hxr hxQ hxSR hCM
  have hFN := snFreshNew_of hH hxB hxD hxK hxN hxr hxP hxSQ hCM
  -- the responders
  have hMat := snMatOK_of hH hxN hxL (SnFinal4.snNewAny_of hH hxB hxD hxK hxN hxr) hSM
    (SnFinal4.snMatLeaf_of hH hxB hxD hxK hxN hxr) hlongM
  have hBnew : ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 →
      NewOK (storeOf (brVers tr pub ++ snVers tr pub)) (brOut tr pub r) (brNew tr pub r) := fun r hr' h1 => by
    have hc := tbl_br D _ nb np hH r (List.mem_range.2 hr')
    exact br_newOK hH (BrDigest.brHashed hH hxB hxD hxK) _ (brVers_hv hH (snVers tr pub) (vers_nodup hH)) hr'
      (osl_flags hc h1).2.1
  have hBlim := fun r hr' h1 => osl_limbs hH hxB hxD hxK hxr hxM hSM hON (r := r) hr' h1
  have hFr : ∀ p, p < tr.height 3 → (ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) →
      FreshRel (storeOf (brVers tr pub ++ snVers tr pub)) (keyOf tr) tr pub p := by
    intro p hp h
    have hc := tbl_sn D _ nb np hH p (List.mem_range.2 hp)
    have hcb := FieldRows2.sn_bool hc "cont" (by simp)
    rcases (by omega : ev tr 3 p pub (Sn.c "cont") = 0 ∨ ev tr 3 p pub (Sn.c "cont") = 1) with h0 | h1
    · obtain ⟨a, b, c⟩ := hFN p hp h h0
      exact fresh_short hH hxN hp h h0 a b c
    · exact hFL p hp h h1
  have hold := SnFinal4.snOldAll_of hH hxB hxD hxK hxN hxr hxV hCR
  have hlim := SnFinal4.snLimbs3_of hH hxB hxD hxK hxN hxr hxV
  -- `SnRest2`
  have hrest : SnRest2 (storeOf (brVers tr pub ++ snVers tr pub)) (keyOf tr) tr pub := by
    intro r hr' hg hops
    have hc := tbl_sn D _ nb np hH r (List.mem_range.2 hr')
    have hcb := FieldRows2.sn_bool hc "cont" (by simp)
    rcases (by omega : ev tr 3 r pub (Sn.c "cont") = 0 ∨ ev tr 3 r pub (Sn.c "cont") = 1) with h0 | h1
    · have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := eval_one_ev hg
      rcases hops with h | h | h
      · rw [h0] at h; exact absurd h (by decide)
      · exact localOK_oLX hH hD30 hxDU hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hMat hBnew hBlim hFr hr'
          (gX_of_split hc hg' (Or.inl h)) h h0
          (hold r hr' hg h0)
      · exact localOK_oEX hH hD30 hxDU hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hxSQ hxSR hxr hMat hBnew hBlim hFr
          hr' (gX_of_split hc hg' (Or.inr h)) h h0 (hold r hr' hg h0) (hlim r hr' hg h0).mem
    · exact hcr r hr' hg h1
  exact SnFinal4.air_final_sorted_sn4 D writes prev post n rest nb np hP hr hrN hrS (fun T hT => (hrX T hT).1) hxV hn hprev hpost hCR
    hSU hSM hrest hlongS hlongM cs hlen hcs committed hcomm T hT0 hF

end StateM5a.SnFinal5
