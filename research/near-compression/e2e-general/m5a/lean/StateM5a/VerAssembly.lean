import StateM5a.BrDigest

/-!
# StateM5a.VerAssembly — `BrStore` with `old` / `new` from `VER` balance, and the final assembly

`BrStore.old` / `BrStore.new` of every active `BR` row follow from `Holds` (the `VER` bus) with the
store `σ = storeOf (brVers ++ rest)` (`rest`: the `SN` rows' version publications, ids distinct)
and the SHA-256 facts of the hashing rows (`BrHashed`, from `Holds` by `BrDigest.brHashed`).
**`air_final_sorted_ver`**: `FinalOrder.air_final_sorted` for the concrete decoder with that store,
the remaining premises being the memory-limb ranges, the `MATR` / `SIBA` answers and the `SN` rows'
`LocalOK`.
-/

namespace StateM5a.VerAssembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrN StateM5a.RowHloc StateM5a.RowFacts StateM5a.VerStore
open StateM5a.KeyDecode

local notation "P" => 2013265921

/-- The non-store part of a `BR` row's facts (premises). -/
structure BrRest (σ : Store) (tr : Trace Fp) (pub : List Fp) (r : Nat) : Prop where
  ranges : BrRangesW tr pub r
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
    {r : Nat} (hr : r < tr.height 2) (hg : ev tr 2 r pub Br.gold = 1)
    (hR : BrRest (storeOf (brVers tr pub ++ rest)) tr pub r) :
    BrStore (storeOf (brVers tr pub ++ rest)) tr pub r :=
  ⟨br_oldOK hH hxV hCR hHs _ (brVers_hv hH rest hnd) hr hg,
   fun h => br_newOK hH hHs _ (brVers_hv hH rest hnd) hr h, hR.ranges, hR.mat, hR.sib⟩

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 in
/-- **Batched FINAL in the spec's order, with the version store from `VER`.** -/
theorem air_final_sorted_ver {tr : Trace Fp} {pub : List Fp} (D : Nat)
    (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table) (nb np : Nat)
    {compress : List Nat → List Nat → List Nat}
    (hP : Prem tr pub D (tapeTable (m5aTape writes prev post n) :: rest) nb np compress)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH)
    (hrN : ∀ T ∈ rest, sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KC = false ∧
      sendsOn T.interactions B_KCR = false)
    (hxV : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions B_VER = false)
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (snVers : List (Nat × Rec))
    (hnd : ((brVers tr pub ++ snVers).map (·.1)).Nodup)
    (hR : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrRest (storeOf (brVers tr pub ++ snVers)) tr pub r)
    (hsn : ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem (storeOf (brVers tr pub ++ snVers)) (keyOf tr)) x)
    (cs : List (Bytes × Option Bytes)) (hlen : cs.length = n) (hcs : FinalChanges tr pub cs)
    (committed : List (Bytes × Option Bytes)) (hcomm : committed.Perm cs)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) (sortKV committed) = some (some T') ∧ rootHash (some T') = post :=
  air_final_sorted_cDc (storeOf (brVers tr pub ++ snVers)) D writes prev post n rest nb np hP hr hrN hn hprev hpost
    (fun r hr' hg => brStore_of hP.hH hxV hP.hCR
      (BrDigest.brHashed hP.hH (fun T hT => (hP.hsil T hT).2.2.2.1) (fun T hT => (hP.hsil T hT).2.2.2.2.1)
        (fun T hT => (hP.hsil T hT).2.2.2.2.2.1)) snVers hnd hr' hg (hR r hr' hg)) hsn
    cs hlen hcs committed hcomm T hT0 hF

end StateM5a.VerAssembly
