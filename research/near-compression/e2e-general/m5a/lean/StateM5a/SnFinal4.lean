import StateM5a.SnResp
import StateM5a.WalkEnd
import StateM5a.SnRange
import StateM5a.BrVl

/-!
# StateM5a.SnFinal4 — batched FINAL with the record and range premises of the short keys from `Holds`

**`air_final_sorted_sn4`**: `SnResp.air_final_sorted_sn2` with, from `Holds` (M5a-6):

* the version store `snVers := SnStore2.snVers tr pub` and its distinct ids (`vers_nodup`, was `hnd`);
* `BR` `hVl` / `hVP` (`BrVl.hVl_of` / `hVP_of`, after the AIR's `RNG [nvl]` lookups);
* `BR` `OslApart` (`WalkEnd.oslApart`);
* the `SN` records of the rows whose key fits the head (`cont = 0`; the premises are now stated for
  those rows only): `SnOldAll`, `SnNewAll`, `SnOldAny`, `SnNewAny` (`SnStore2.sn_oldOK` /
  `sn_newOK`: SHA-256 contract, `VER` balance, `Sha256CR`);
* the `SN` ranges at `cont = 0`: `SnLimbs3`, `SnLeafMemLt`, `SnMatLeaf` (`SnRange`).

Remaining premises (named): `SnUpLimbs`, `SnMatLimbs` (the 16-bit memory limbs every `SN` row
sends on `UP` / `MATR`; at `cont = 0` they follow from `SnRange.sn_NM_lt` / `sn_M_lt` except a split
row's `sm`, received on `SPR`), `SnRest2` (the splits and continued keys: lean-wip/ holds the
split-row steps, not yet compiled within the memory budget), `hlongS`, `hlongM`.
-/

namespace StateM5a.SnFinal4

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnN StateM5a.RowSnAll StateM5a.RowSnAll2
open StateM5a.SnAssembly StateM5a.SnResp StateM5a.SnStore2 StateM5a.SnRange StateM5a.SnHashed

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp} {t r : Nat}

theorem sn_mem_gold' : Sn.c "gold" - (Sn.c "act" - Sn.c "oLM" - Sn.c "oEP" - Sn.c "oEM") ∈ Sn.constraints :=
  sn_mem_gold

/-- `gold = 1` on an active row that is not a builder (`oLM`, `oEP`, `oEM` all `0`). -/
theorem gold_of (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0) (hA : ev tr t r pub (Sn.c "act") = 1)
    (h1 : ev tr t r pub (Sn.c "oLM") = 0) (h2 : ev tr t r pub (Sn.c "oEP") = 0) (h3 : ev tr t r pub (Sn.c "oEM") = 0) :
    ev tr t r pub (Sn.c "gold") = 1 := by
  have e := eq_of_sub (FieldRows.hold rfl hc sn_mem_gold')
  rw [e, ev_sub, ev_sub, ev_sub, hA, h1, h2, h3]

end

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : XSbHi D extra nb np tr pub)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
  (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)

include hH hxB hxD hxK hN hxr hxV in
theorem snOldAll_of (hCR : Walk.Sha256CR) :
    SnOldAll (storeOf (VerStore.brVers tr pub ++ snVers tr pub)) tr pub := by
  intro r hr hg hcont
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨-, hA, hLS, hLM, hEP, hEM, -⟩ := sn_flags' hc (eval_one_ev hg)
  exact sn_oldOK hH hxB hxD hxK hN hxr hxV hCR hr (gold_of hc hA hLM hEP hEM) hcont

include hH hxB hxD hxK hN hxr hxV in
theorem snOldAny_of (hCR : Walk.Sha256CR) :
    SnOldAny (storeOf (VerStore.brVers tr pub ++ snVers tr pub)) tr pub := by
  intro r hr h1 hcont
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨hfl, hact, h2, h3, h4, -, -, -, -⟩ := sn_ops hc
  have := hfl "act" (by simp [snNames]); have := hfl "oLM" (by simp [snNames])
  have := hfl "oEP" (by simp [snNames]); have := hfl "oEM" (by simp [snNames])
  have hA : ev tr 3 r pub (Sn.c "act") = 1 := by omega
  exact sn_oldOK hH hxB hxD hxK hN hxr hxV hCR hr
    (gold_of hc hA (by omega) (by omega) (by omega)) hcont

include hH hxB hxD hxK hN hxr in
theorem snNewAll_of : SnNewAll (storeOf (VerStore.brVers tr pub ++ snVers tr pub)) tr pub :=
  fun r hr _ hcont hn => sn_newOK hH hxB hxD hxK hN hxr hr hn hcont

include hH hxB hxD hxK hN hxr in
theorem snNewAny_of : SnNewAny (storeOf (VerStore.brVers tr pub ++ snVers tr pub)) tr pub := by
  intro r hr h1 hcont
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨b, h1', h2, h3, h4, -, -, -, h9⟩ := sn_ops hc
  have := b "act" (by simp [snNames])
  exact sn_newOK hH hxB hxD hxK hN hxr hr (by omega) hcont

include hH hxB hxD hxK hN hxr hxV in
theorem snLimbs3_of : SnLimbs3 tr pub := by
  intro r hr hg hcont
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := eval_one_ev hg
  obtain ⟨-, hA, hLS, hLM, hEP, hEM, -⟩ := sn_flags' hc hg'
  refine ⟨sn_M_lt hH hxB hxD hxK hN hxr hxV hr (gold_of hc hA hLM hEP hEM) hcont,
    fun hn => sn_NM_lt hH hxB hxD hxK hN hxr hr hn hcont, fun h1 t ht => ?_⟩
  exact (sn_leafMem_lt hH hxB hxD hxK hN hxr hr (Or.inl h1) hcont).1 t ht

include hH hxB hxD hxK hN hxr in
theorem snLeafMemLt_of : SnLeafMemLt tr pub :=
  fun r hr _ hcont h1 => (sn_leafMem_lt hH hxB hxD hxK hN hxr hr (Or.inl h1) hcont).2

include hH hxB hxD hxK hN hxr in
theorem snMatLeaf_of : SnMatLeaf tr pub :=
  fun r hr h1 hcont => sn_leafMem_lt hH hxB hxD hxK hN hxr hr (Or.inr h1) hcont

end

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 StateM5a.VerStore StateM5a.WalkEnd StateM5a.VerAssembly in
set_option maxHeartbeats 8000000 in
/-- **Batched FINAL in the spec's order from `Holds`**, the record and range premises of the
short-key `SN` rows discharged (M5a-6). -/
theorem air_final_sorted_sn4 {tr : Trace Fp} {pub : List Fp} (D : Nat)
    (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table) (nb np : Nat)
    {compress : List Nat → List Nat → List Nat}
    (hP : Prem tr pub D (tapeTable (m5aTape writes prev post n) :: rest) nb np compress)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH)
    (hrN : ∀ T ∈ rest, sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KC = false ∧
      sendsOn T.interactions B_KCR = false)
    (hrS : ∀ T ∈ rest, sendsOn T.interactions B_MATQ = false ∧ sendsOn T.interactions B_MATR = false ∧
      sendsOn T.interactions B_SIBQ = false ∧ sendsOn T.interactions B_SIBA = false)
    (hrQ : ∀ T ∈ rest, sendsOn T.interactions B_SPQ = false)
    (hxV : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions B_VER = false)
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (hCR : Walk.Sha256CR)
    (hSU : BrRange.SnUpLimbs tr pub) (hSM : BrRange.SnMatLimbs tr pub)
    (hrest : SnRest2 (storeOf (brVers tr pub ++ snVers tr pub)) (keyOf tr) tr pub)
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
  have hxB := hP.hxB
  have hxD := fun T hT => (hP.hsil T hT).2.2.2.1
  have hxK := fun T hT => (hP.hsil T hT).2.2.2.2.1
  have hxr : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, ∀ i ∈ T.interactions, i.bus ≠ B_RNG :=
    fun T hT i hi => (hP.hx T hT i hi).2.2.2.1
  have hxR := tp B_KCR (by decide) (by decide) (fun T hT => (hrN T hT).2.2)
  have hxQ := tp B_SPQ (by decide) (by decide) hrQ
  have hxDU : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, ∀ i ∈ T.interactions,
      i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP := fun T hT i hi => by
    rcases List.mem_cons.1 hT with rfl | hT
    · rcases tape_bus writes prev post n i hi with e | e <;> rw [e] <;> decide
    · exact ⟨(hr T hT i hi).1, (hr T hT i hi).2.1⟩
  exact air_final_sorted_sn2 D writes prev post n rest nb np hP hr hrN hrS hxV hn hprev hpost (snVers tr pub)
    (vers_nodup hH) hSU hSM (BrVl.hVl_of hH hxB hxD hxK hxr hxV) (BrVl.hVP_of hH hxB hxD hxK hxr hxV)
    (oslApart hH hD30 hxDU hxN hxL hxK hxR hxQ)
    (snOldAll_of hH hxB hxD hxK hxN hxr hxV hCR) (snNewAll_of hH hxB hxD hxK hxN hxr)
    (snOldAny_of hH hxB hxD hxK hxN hxr hxV hCR) (snNewAny_of hH hxB hxD hxK hxN hxr)
    (snLimbs3_of hH hxB hxD hxK hxN hxr hxV) (snLeafMemLt_of hH hxB hxD hxK hxN hxr)
    (snMatLeaf_of hH hxB hxD hxK hxN hxr) hrest hlongS hlongM cs hlen hcs committed hcomm T hT0 hF

end StateM5a.SnFinal4
