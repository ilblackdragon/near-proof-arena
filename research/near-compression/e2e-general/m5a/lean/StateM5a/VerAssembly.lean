import StateM5a.BrMat

/-!
# StateM5a.VerAssembly — `BrStore` with `old` / `new` from `VER` balance, and the final assembly

`BrStore.old` / `BrStore.new` of every active `BR` row follow from `Holds` (the `VER` bus) with the
store `σ = storeOf (brVers ++ rest)` (`rest`: the `SN` rows' version publications, ids distinct)
and the SHA-256 facts of the hashing rows (`BrHashed`, from `Holds` by `BrDigest.brHashed`).
The range facts `BrRangesW` come from `BrRange.brRangesW_of`, the `MATR` / `SIBA` answers
(`BrRest`) from `BrMat.br_mat` / `BrSib.br_sib`.  **`air_final_sorted_ver`**:
`FinalOrder.air_final_sorted` for the concrete decoder with that store, the remaining premises being
on the `SN` side (the memory limbs it sends, `SnUpLimbs` / `SnMatLimbs`; its responder relations
`SnSibOK` / `SnMatOK`; its rows' `LocalOK`), the old value length (16-bit limbs on rows reading
their node on `VER`; `< P`), and `OslApart` (a split's new branch is not at an active row's walk
position).
-/

namespace StateM5a.VerAssembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrN StateM5a.RowHloc StateM5a.RowFacts StateM5a.VerStore
open StateM5a.KeyDecode

local notation "P" => 2013265921

/-- The non-store part of a `BR` row's facts (premises): the `MATR` / `SIBA` answers. -/
structure BrRest (σ : Store) (tr : Trace Fp) (pub : List Fp) (r : Nat) : Prop where
  mat : ev tr 2 r pub (Br.c "oDL") = 1 ∨ ev tr 2 r pub (Br.c "oUN") = 1 →
    MatRel σ (keyOf tr) (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "st2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)))
      (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
      (le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)))
  sib : ev tr 2 r pub (Br.c "oD1") = 1 →
    SibRel σ (keyOf tr) (ev tr 2 r pub (Br.c "d") + 1)
      (refOf (E tr 2 r pub Br.isnSib) ((pack2 Br.chSib).map (E tr 2 r pub)))
      (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)))

/-- **`BrStore` from `VER`.** -/
theorem brStore_of {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false) (hCR : Walk.Sha256CR) (hHs : BrHashed tr pub)
    (rest : List (Nat × Rec)) (hnd : ((brVers tr pub ++ rest).map (·.1)).Nodup)
    {r : Nat} (hr : r < tr.height 2) (hg : ev tr 2 r pub Br.gold = 1) (hW : BrRangesW tr pub r)
    (hR : BrRest (storeOf (brVers tr pub ++ rest)) tr pub r) :
    BrStore (storeOf (brVers tr pub ++ rest)) tr pub r :=
  ⟨br_oldOK hH hxV hCR hHs _ (brVers_hv hH rest hnd) hr hg,
   fun h => br_newOK hH hHs _ (brVers_hv hH rest hnd) hr h, hW, hR.mat, hR.sib⟩

theorem sendsOn_false_of {is : List Interaction} {b : Nat} (h : ∀ i ∈ is, i.bus ≠ b) : sendsOn is b = false :=
  List.any_eq_false.2 fun i hi => by simp [h i hi]

open StateM5a.Tape in
theorem tape_not (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (b : Nat) (h1 : b ≠ B_WRITE)
    (h2 : b ≠ B_TCH) : sendsOn (tapeTable (m5aTape writes prev post n)).interactions b = false :=
  sendsOn_false_of fun i hi => by
    rcases tape_bus writes prev post n i hi with e | e <;> rw [e] <;> intro e' <;> simp_all

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 in
/-- **Batched FINAL in the spec's order, with the version store from `VER`.** -/
theorem air_final_sorted_ver {tr : Trace Fp} {pub : List Fp} (D : Nat)
    (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table) (nb np : Nat)
    {compress : List Nat → List Nat → List Nat}
    (hP : Prem tr pub D (tapeTable (m5aTape writes prev post n) :: rest) nb np compress)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH)
    (hrN : ∀ T ∈ rest, sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KC = false ∧
      sendsOn T.interactions B_KCR = false)
    (hrS : ∀ T ∈ rest, sendsOn T.interactions B_MATQ = false ∧ sendsOn T.interactions B_MATR = false ∧
      sendsOn T.interactions B_SIBQ = false ∧ sendsOn T.interactions B_SIBA = false)
    (hxV : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions B_VER = false)
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (snVers : List (Nat × Rec))
    (hnd : ((brVers tr pub ++ snVers).map (·.1)).Nodup)
    (hSU : BrRange.SnUpLimbs tr pub) (hSM : BrRange.SnMatLimbs tr pub)
    (hVl : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ev tr 2 r pub (Br.c "gsha") = 0 →
      ∀ k, k < 2 → ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) k) < 65536)
    (hVP : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → brVlen tr pub r < 2013265921)
    (hSib : BrSib.SnSibOK (storeOf (brVers tr pub ++ snVers)) (keyOf tr) tr pub)
    (hMat : BrMat.SnMatOK (storeOf (brVers tr pub ++ snVers)) (keyOf tr) tr pub) (hOsl : BrMat.OslApart tr pub)
    (hsn : ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem (storeOf (brVers tr pub ++ snVers)) (keyOf tr)) x)
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
  have hxB := fun T hT => (hP.hsil T hT).2.2.2.1
  have hxD := fun T hT => (hP.hsil T hT).2.2.2.2.1
  have hxK := fun T hT => (hP.hsil T hT).2.2.2.2.2.1
  have hxN := fun T hT => (hP.hsil T hT).1
  have hxR := tp B_KCR (by decide) (by decide) (fun T hT => (hrN T hT).2.2)
  have hxDU : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, ∀ i ∈ T.interactions,
      i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP := fun T hT i hi => by
    rcases List.mem_cons.1 hT with rfl | hT
    · rcases tape_bus writes prev post n i hi with e | e <;> rw [e] <;> decide
    · exact ⟨(hr T hT i hi).1, (hr T hT i hi).2.1⟩
  have hxU := tp B_UP (by decide) (by decide) (fun T hT => sendsOn_false_of fun i hi => (hr T hT i hi).2.1)
  have hxQ := tp B_MATQ (by decide) (by decide) (fun T hT => (hrS T hT).1)
  have hxM := tp B_MATR (by decide) (by decide) (fun T hT => (hrS T hT).2.1)
  have hxSQ := tp B_SIBQ (by decide) (by decide) (fun T hT => (hrS T hT).2.2.1)
  have hxSA := tp B_SIBA (by decide) (by decide) (fun T hT => (hrS T hT).2.2.2)
  have hD30 : D ≤ 30 := by have := hP.hD; omega
  exact air_final_sorted_cDc (storeOf (brVers tr pub ++ snVers)) D writes prev post n rest nb np hP hr hrN hn hprev
    hpost (fun r hr' hg => brStore_of hP.hH hxV hP.hCR (BrDigest.brHashed hP.hH hxB hxD hxK) snVers hnd hr' hg
      (BrRange.brRangesW_of hP.hH hxB hxD hxK (fun T hT i hi => (hP.hx T hT i hi).2.2.2.1) hxV hxU hxM
        hSU hSM hVl hVP hr' hg)
      ⟨fun h => BrMat.br_mat hP.hH hD30 hxDU hxN hxK hxR hxQ hxM hMat hOsl hr' h,
       fun h => BrSib.br_sib hP.hH hD30 hxDU hxN hxK hxR hxSQ hxSA hSib hr' h⟩) hsn
    cs hlen hcs committed hcomm T hT0 hF

end StateM5a.VerAssembly
