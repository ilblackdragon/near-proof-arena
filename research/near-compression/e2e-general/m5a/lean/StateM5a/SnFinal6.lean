import StateM5a.SnContResp
import StateM5a.SnContLimbs

/-!
# StateM5a.SnFinal6 — batched FINAL with the continued-key responders from `Holds`

**`air_final_sorted_sn6`** (M5a-8): `SnFinal5.air_final_sorted_sn5` with, newly from `Holds`
(`Sha256CR` for the full key of a continued head, `SnContKey*`):

* `SnContMem` (`SnContLimbs.snContMem_of`);
* `hlongS` / `hlongM` (`SnContResp.hlongS_of` / `hlongM_of`: the continued `oLS` / `oLM`
  responders' `SibRel` / `MatRel`);
* `SnFreshLong` (`SnContResp.snFreshLong_of`: `FreshRel` of the continued `oEP` / `oEM` rows).

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
open StateM5a.SnFinal5 StateM5a.SnContResp

set_option maxRecDepth 100000

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 StateM5a.VerStore StateM5a.VerAssembly in
set_option maxHeartbeats 8000000 in
/-- **Batched FINAL in the spec's order from `Holds`**: the continued-key responders and memory
limbs discharged (M5a-8); `SnContRest` (`LocalOK` of the continued-key walk rows) remains. -/
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
    (hcr : SnContRest (storeOf (brVers tr pub ++ snVers tr pub)) (keyOf tr) tr pub)
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
  exact air_final_sorted_sn5 D writes prev post n rest nb np hP hr hrN hrS hrX hxV hn hprev hpost hCR hCM
    (snFreshLong_of hH hxB hxD hxK hxR hxRr hxN hxr hCR _ hxP hxSQ hCM) hcr
    (hlongS_of hH hxB hxD hxK hxR hxRr hxN hxL hxr hCR _) (hlongM_of hH hxB hxD hxK hxR hxRr hxN hxL hxr hCR _)
    cs hlen hcs committed hcomm T hT0 hF

end StateM5a.SnFinal6
