import StateM5a.RowSnAll
import StateM5a.RowSnE
import StateM5a.RowFacts

/-!
# StateM5a.RowSnAll2 — `hloc` for the `SN` rows with the upsert / delete-through-extension ops

`RowSnAll.hloc_sn` covered the find ops and `oLD`, `oLA`, `oEA`, `oLZ`, `oEZ`.  **`hloc_sn2`** adds
`oLR`, `oEU`, `oES`, `oEB`, `oED` (`RowSnN`, `RowSnE`); its premises:

* `SnOldAll σ` (as before) and `SnNewAll σ`: every active walk row with a new node publishes
  `snNew` under `snOut` (`VER` id / SHA-256, as `BR`'s `NewOK`);
* `SnLimbs`: the 16-bit memory limbs of an active walk row (old `mem`; new `nmem` with `gnew`; the
  child's `unm` / `uom` on `oEU`/`oEB`) and, on `oLR`, the value-length bytes `nx₀..₂`;
* `SnLeafMemLt`: on `oLR` the new leaf's 64-bit memory is `< P` — **not implied by the AIR**: its
  constraint `limb₀ + 65536·limb₁ = 100 + 2·hplen + vlen` is one field equation, and with 16-bit
  limbs `limb₀ + 65536·limb₁` reaches `2^32 > P` (an integrator decision; the honest value is `< 2^25`);
* `SnDepth` (as before);
* `SnRest2`: continued keys (`cont = 1`) and the splits `oLX`, `oEX`.
-/

namespace StateM5a.RowSnAll2

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM StateM5a.RowSnD StateM5a.KeyDecode StateM5a.KeyLookups StateM5a.RowSnAll
open StateM5a.RowSnN StateM5a.RowSnE

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- **Premise**: every active `SN` walk row with a new node publishes it (`VER` / SHA-256). -/
def SnNewAll (σ : Store) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 → ev tr 3 r pub (Sn.c "gnew") = 1 →
    NewOK σ (snOut tr pub r) (snNew tr pub r)

/-- The range facts of one active `SN` walk row. -/
structure SnLimbsAt (tr : Trace Fp) (pub : List Fp) (r : Nat) : Prop where
  mem : ∀ k, k < 4 → ev tr 3 r pub (Sn.M.getD k 0) < 65536
  nmem : ev tr 3 r pub (Sn.c "gnew") = 1 → ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536
  unm : ev tr 3 r pub (Sn.c "oEU") = 1 ∨ ev tr 3 r pub (Sn.c "oEB") = 1 →
    ∀ k, k < 4 → ev tr 3 r pub (Sn.c "unm" k) < 65536
  uom : ev tr 3 r pub (Sn.c "oEU") = 1 → ∀ k, k < 4 → ev tr 3 r pub (Sn.c "uom" k) < 65536
  nx : ev tr 3 r pub (Sn.c "oLR") = 1 → ∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256

/-- **Premise**: the range facts of every active `SN` walk row. -/
def SnLimbs (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 → SnLimbsAt tr pub r

/-- **Premise (not implied by the AIR)**: the new leaf's memory of an `oLR` row is `< P`. -/
def SnLeafMemLt (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 → ev tr 3 r pub (Sn.c "oLR") = 1 → snNMem tr pub r < P

/-- **Premise**: the `SN` rows not covered — continued keys and splits. -/
def SnRest2 (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 →
    (ev tr 3 r pub (Sn.c "cont") = 1 ∨ ev tr 3 r pub (Sn.c "oLX") = 1 ∨ ev tr 3 r pub (Sn.c "oEX") = 1) →
    LocalOK (Sem σ keyOf) (snRow tr pub r)

theorem sn_gnew {tr : Trace Fp} {r : Nat} {pub : List Fp} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1) {o : String}
    (ho : o = "oLR" ∨ o = "oEU" ∨ o = "oEB") (h1 : ev tr 3 r pub (Sn.c o) = 1) :
    ev tr 3 r pub (Sn.c "gnew") = 1 := by
  have e := eq_of_sub (FieldRows2.sn_hold hc (e := Sn.c "gnew" - (Sn.c "oLR" + Sn.c "oLM" + Sn.c "oEU" +
    Sn.c "oEB" + Sn.c "oEP" + Sn.c "oEM")) (by unfold Sn.constraints; simp))
  obtain ⟨hb, -, -, hLM, hEP, hEM, hs, -, hU, hD, -⟩ := sn_flags' hc hg
  have b1 := hb "oLR" (by simp [snNames]); have b3 := hb "oEU" (by simp [snNames])
  have b4 := hb "oEB" (by simp [snNames])
  simp only [ev_hadd, hLM, hEP, hEM] at e
  rcases ho with rfl | rfl | rfl <;> omega

set_option maxHeartbeats 4000000 in
/-- **Every decoded `SN` row is `LocalOK`**, the uncovered rows (continued keys, splits) as the
premise `SnRest2`. -/
theorem hloc_sn2 {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp} {σ : Store}
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hold : SnOldAll σ tr pub) (hnew : SnNewAll σ tr pub) (hlim : SnLimbs tr pub)
    (hlm : SnLeafMemLt tr pub) (hd : SnDepth tr pub) (hrest : SnRest2 σ (keyOf tr) tr pub) :
    ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem σ (keyOf tr)) x := by
  refine hloc_sn hH hN hL hold hd ?_
  intro r hr hg hops
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := eval_one_ev hg
  have hd' := hd r hr hg
  have ho := hold r hr hg
  have hl := hlim r hr hg
  have hnib : ∀ j < 64, (Sn.b j).eval tr 3 r pub = 1 →
      (keyOf tr (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)) :=
    fun j hj hgj => (sn_nib hH hN j hj hr hgj).1
  have hnib2 : ∀ j < 64, (Sn.c "g2" * Sn.a j).eval tr 3 r pub = 1 →
      (keyOf tr (ev tr 3 r pub (Sn.c "kid2")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)) :=
    fun j hj hgj => (sn_nib2 hH hN j hj hr hgj).1
  have hklen : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1 →
      (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "klen") :=
    fun h => sn_klen_leaf hH hL hr h
  have hcb := FieldRows2.sn_bool hc "cont" (by simp)
  by_cases hcont : ev tr 3 r pub (Sn.c "cont") = 0
  · rcases hops with h | h | h | h | h | h | h | h
    · omega
    · exact localOK_oES hc hg' hcont hd' hnib ho h
    · exact localOK_oLR hc hg' h hcont hd' hnib hklen ho (hnew r hr hg (sn_gnew hc hg' (Or.inl rfl) h))
        (hl.nmem (sn_gnew hc hg' (Or.inl rfl) h)) (hlm r hr hg h) (hl.nx h)
    · exact localOK_oEU hc hg' h hcont hd' hnib ho (hnew r hr hg (sn_gnew hc hg' (Or.inr (Or.inl rfl)) h))
        hl.mem (hl.nmem (sn_gnew hc hg' (Or.inr (Or.inl rfl)) h)) (hl.unm (Or.inl h)) (hl.uom h)
    · exact localOK_oED hc hg' hcont hd' hnib ho h hnib2 (RowFacts.keyOf_bounds hH)
    · exact localOK_oEB hc hg' hcont hd' hnib ho h (hnew r hr hg (sn_gnew hc hg' (Or.inr (Or.inr rfl)) h))
        (hl.nmem (sn_gnew hc hg' (Or.inr (Or.inr rfl)) h)) (hl.unm (Or.inr h))
    · exact hrest r hr hg (Or.inr (Or.inl h))
    · exact hrest r hr hg (Or.inr (Or.inr h))
  · exact hrest r hr hg (Or.inl (by omega))

end StateM5a.RowSnAll2
