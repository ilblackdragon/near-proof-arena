import StateM5a.SnContRestAll
import StateM5a.SnContLimbs

/-!
# StateM5a.SnFinal6 — batched FINAL with every continued-key premise from `Holds`

**`air_final_sorted_sn6`** (M5a-8): `SnFinal5.air_final_sorted_sn5` with, newly from `Holds`
(`Sha256CR` for the full key of a continued head, `SnContKey*`):

* `SnContMem` (`SnContLimbs.snContMem_of`);
* `hlongS` / `hlongM` (`SnContResp.hlongS_of` / `hlongM_of`: the continued `oLS` / `oLM`
  responders' `SibRel` / `MatRel`);
* `SnFreshLong` (`SnContResp.snFreshLong_of`: `FreshRel` of the continued `oEP` / `oEM` rows);
* `SnContRest` (`SnContRestAll.snContRest_of`: `LocalOK` of every continued-key walk row).

New static premise `hrK` (no extra table touches `KCR`; true of the STATE tables and the tape).
-/

namespace StateM5a.SnFinal6

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.RowSnAll StateM5a.RowSnAll2
open StateM5a.SnAssembly StateM5a.SnResp StateM5a.SnLimbsAll StateM5a.SnFreshLimbs StateM5a.SnStore2 StateM5a.RowBrN
open StateM5a.SnFinal5 StateM5a.SnContResp StateM5a.SnLimbsAll StateM5a.SnFreshLimbs

set_option maxRecDepth 100000

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 StateM5a.VerStore StateM5a.VerAssembly in
set_option maxHeartbeats 8000000 in
/-- **Batched FINAL in the spec's order from `Holds`**: every continued-key premise discharged
(M5a-8). -/
theorem air_final_sorted_sn6 {tr : Trace Fp} {pub : List Fp} (D : Nat)
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
    (hrK : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)
    (hxV : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions B_VER = false)
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (hCR : Walk.Sha256CR)
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
  have hxN := fun T hT => (hP.hsil T hT).1
  have hxL := fun T hT => (hP.hsil T hT).2.1
  have hxB := fun T hT => (hP.hsil T hT).2.2.2.1
  have hxD := fun T hT => (hP.hsil T hT).2.2.2.2.1
  have hxK := fun T hT => (hP.hsil T hT).2.2.2.2.2.1
  have hxr : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, ∀ i ∈ T.interactions, i.bus ≠ B_RNG :=
    fun T hT i hi => (hP.hx T hT i hi).2.2.2.1
  have hxR := tp B_KCR (by decide) (by decide) (fun T hT => (hrN T hT).2.2)
  have hxRr : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, ∀ i ∈ T.interactions, i.bus ≠ B_KCR :=
    fun T hT i hi => by
      rcases List.mem_cons.1 hT with rfl | hT
      · rcases tape_bus writes prev post n i hi with e | e <;> rw [e] <;> decide
      · exact hrK T hT i hi
  have hxP := tp B_SPR (by decide) (by decide) (fun T hT => (hrX T hT).2.1)
  have hxSQ := tp B_SXQ (by decide) (by decide) (fun T hT => (hrX T hT).2.2.2.1)
  have hCM := SnContLimbs.snContMem_of hH hxB hxD hxK hxR hxRr
  have hD30 : D ≤ 30 := by have := hP.hD; omega
  have hxDU : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, ∀ i ∈ T.interactions,
      i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP := fun T hT i hi => by
    rcases List.mem_cons.1 hT with rfl | hT
    · rcases tape_bus writes prev post n i hi with e | e <;> rw [e] <;> decide
    · exact ⟨(hr T hT i hi).1, (hr T hT i hi).2.1⟩
  have hxU : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions B_UP = false :=
    fun T hT => VerAssembly.sendsOn_false_of fun i hi => (hxDU T hT i hi).2
  have hxQ := tp B_SPQ (by decide) (by decide) (fun T hT => (hrX T hT).1)
  have hxMQ := tp B_MATQ (by decide) (by decide) (fun T hT => (hrS T hT).1)
  have hxM := tp B_MATR (by decide) (by decide) (fun T hT => (hrS T hT).2.1)
  have hxE := tp B_EPQ (by decide) (by decide) (fun T hT => (hrX T hT).2.2.1)
  have hxSR := tp B_SXR (by decide) (by decide) (fun T hT => (hrX T hT).2.2.2.2)
  have hSU := snUpLimbs_of hH hxB hxD hxK hxN hxr hxV hxP hCM
  have hSM := snMatLimbs_of hH hxB hxD hxK hxN hxr hCM
  have hON := oslNodeLimbs_of hH hxB hxD hxK hxN hxr hxQ hxSR hCM
  have hFN := snFreshNew_of hH hxB hxD hxK hxN hxr hxP hxSQ hCM
  have hFL := snFreshLong_of hH hxB hxD hxK hxR hxRr hxN hxr hCR (storeOf (brVers tr pub ++ snVers tr pub)) hxP hxSQ hCM
  have hlongM := hlongM_of hH hxB hxD hxK hxR hxRr hxN hxL hxr hCR (storeOf (brVers tr pub ++ snVers tr pub))
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
  have hcr := SnContRestAll.snContRest_of hH hD30 hxDU hxN hxL hxK hxR hxQ hxMQ hxM hxP hxE hxSQ hxSR hxr hxB hxD
    hxRr hxV hxU hCR hSU hMat hBnew hBlim hFr
  exact air_final_sorted_sn5 D writes prev post n rest nb np hP hr hrN hrS hrX hxV hn hprev hpost hCR hCM
    hFL hcr (hlongS_of hH hxB hxD hxK hxR hxRr hxN hxL hxr hCR _) hlongM
    cs hlen hcs committed hcomm T hT0 hF

end StateM5a.SnFinal6
