import StateM5a.RowSnD
import StateM5a.KeyLookups

/-!
# StateM5a.RowSnAll — every decoded `SN` walk row is `LocalOK` (`hloc_sn`)

From `Holds` of the AIR (the `NIB` / `KLEN` lookups via `KeyLookups`), for every decoded `SN` row
(`rowsOf cDc snW tr 3 pub`) with a head key (`cont = 0`) and one of the ops `oLF`, `oEF`, `oLA`,
`oEA`, `oLZ`, `oEZ`, `oLD`, its `LocalOK (Sem σ keyOf)`.  Named premises:

* `SnOldAll σ`: every active row's old record under its input ref (`OldOK σ snIn snOld`: the
  `VER` read / the row's SHA-256, as for `BR`);
* `SnDepth`: the depth of an active row is `< P − 64`;
* `SnRest σ keyOf`: the rows not covered here — continued keys (`cont = 1`) and the ops `oES`, `oLR`,
  `oEU`, `oED`, `oEB`, `oLX`, `oEX` (new records: `NewOK`, memory chains, splits).
-/

namespace StateM5a.RowSnAll

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM StateM5a.RowSnD StateM5a.KeyDecode StateM5a.KeyLookups

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- **Premise**: every active `SN` row's old record (`VER` / SHA-256). -/
def SnOldAll (σ : Store) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 → ev tr 3 r pub (Sn.c "cont") = 0 → OldOK σ (snIn tr pub r) (snOld tr pub r)

/-- **Premise**: active `SN` rows are not near the field's top in depth. -/
def SnDepth (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 → ev tr 3 r pub (Sn.c "d") + 64 < P

/-- **Premise**: the `SN` rows not covered here. -/
def SnRest (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 →
    (ev tr 3 r pub (Sn.c "cont") = 1 ∨ ev tr 3 r pub (Sn.c "oES") = 1 ∨ ev tr 3 r pub (Sn.c "oLR") = 1 ∨ ev tr 3 r pub (Sn.c "oEU") = 1 ∨
      ev tr 3 r pub (Sn.c "oED") = 1 ∨ ev tr 3 r pub (Sn.c "oEB") = 1 ∨ ev tr 3 r pub (Sn.c "oLX") = 1 ∨
      ev tr 3 r pub (Sn.c "oEX") = 1) →
    LocalOK (Sem σ keyOf) (snRow tr pub r)

/-- The ops of an active walk row cover it (plain arithmetic). -/
theorem cover (mF mU mD a b c d e f g h i j k l m n : Nat) (ba : a ≤ 1) (bb : b ≤ 1) (bc : c ≤ 1) (bd : d ≤ 1)
    (be : e ≤ 1) (bf : f ≤ 1) (bg : g ≤ 1) (bh : h ≤ 1) (bi : i ≤ 1) (bj : j ≤ 1) (bk : k ≤ 1) (bl : l ≤ 1)
    (bm : m ≤ 1) (bn : n ≤ 1) (hs : mF + mU + mD = 1) (hF : a + b + c + d = mF) (hU : e + f + g + h = mU)
    (hD : i + j + k + l + m + n = mD) :
    a = 1 ∨ b = 1 ∨ c = 1 ∨ d = 1 ∨ e = 1 ∨ f = 1 ∨ g = 1 ∨ h = 1 ∨ i = 1 ∨ j = 1 ∨ k = 1 ∨ l = 1 ∨
      m = 1 ∨ n = 1 := by
  omega

set_option maxHeartbeats 4000000 in
/-- **Every decoded `SN` row is `LocalOK`** (the uncovered rows as the named premise `SnRest`). -/
theorem hloc_sn {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp} {σ : Store}
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hold : SnOldAll σ tr pub) (hd : SnDepth tr pub) (hrest : SnRest σ (keyOf tr) tr pub) :
    ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem σ (keyOf tr)) x := by
  intro x hx
  obtain ⟨r, hr, hg, rfl⟩ := mem_snRows hx
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := eval_one_ev hg
  have hd' := hd r hr hg
  have hnib : ∀ j < 64, (Sn.b j).eval tr 3 r pub = 1 →
      (keyOf tr (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)) :=
    fun j hj hgj => (sn_nib hH hN j hj hr hgj).1
  have hklen : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1 →
      (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "klen") :=
    fun h => sn_klen_leaf hH hL hr h
  have hmisN : (Sn.c "mN" + Sn.c "mL").eval tr 3 r pub = 1 →
      (keyOf tr (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + Sn.c "jm")]? = some (ev tr 3 r pub (Sn.c "y")) :=
    fun h => (sn_nib_mis hH hN hr h).1
  have hmisK : (Sn.c "mK").eval tr 3 r pub = 1 →
      (keyOf tr (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "jm") :=
    fun h => sn_klen_mK hH hL hr h
  have hcb := FieldRows2.sn_bool hc "cont" (by simp)
  by_cases hcont : ev tr 3 r pub (Sn.c "cont") = 0
  · obtain ⟨hb, -, -, -, -, -, hs, hF, hU, hD, -⟩ := sn_flags' hc hg'
    have ho := hold r hr hg hcont
    rcases cover _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hb "oLF" (by simp [snNames])) (hb "oEF" (by simp [snNames])) (hb "oLA" (by simp [snNames])) (hb "oEA" (by simp [snNames])) (hb "oLR" (by simp [snNames])) (hb "oEU" (by simp [snNames])) (hb "oLX" (by simp [snNames])) (hb "oEX" (by simp [snNames])) (hb "oLD" (by simp [snNames])) (hb "oED" (by simp [snNames])) (hb "oLZ" (by simp [snNames])) (hb "oEZ" (by simp [snNames])) (hb "oES" (by simp [snNames])) (hb "oEB" (by simp [snNames])) hs hF hU hD with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact localOK_oLF hc hg' h hcont hd' hnib hklen ho
    · exact localOK_oEF hc hg' h hcont hd' hnib ho
    · exact localOK_oLA hc hg' hcont hd' hmisN hmisK ho h
    · exact localOK_oEA hc hg' hcont hd' hmisN hmisK ho h
    · exact hrest r hr hg (Or.inr <| Or.inr <| Or.inl h)
    · exact hrest r hr hg (Or.inr <| Or.inr <| Or.inr <| Or.inl h)
    · exact hrest r hr hg (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h)
    · exact hrest r hr hg (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| h)
    · exact localOK_oLD hc hg' hcont hd' hnib ho hklen h
    · exact hrest r hr hg (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h)
    · exact localOK_oLZ hc hg' hcont hd' hmisN hmisK ho h
    · exact localOK_oEZ hc hg' hcont hd' hmisN hmisK ho h
    · exact hrest r hr hg (Or.inr <| Or.inl h)
    · exact hrest r hr hg (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h)
  · exact hrest r hr hg (Or.inl (by omega))

end StateM5a.RowSnAll
