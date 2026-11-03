import StateM5a.RowHloc
import StateM5a.FinalOrder
import StateM5a.WsDecode3

/-!
# StateM5a.RowFacts — the key, depth and memory-order fields of `BrRowFacts` from `Holds`

* **`br_mono`**: the `dm` chain (`memChain (oDH + oDL) dm mem [] om`, M5a-5) with `dm` bytes from
  `RNG` gives `om ≤ mem` — the premise the spec's truncated `mem − om + nm` needs (`oDH`/`oDL`).
* **`brRowFacts_of`**: on the AIR, `BrRowFacts σ (keyOf tr)` follows from the store / range part
  `BrStore` alone: `nib` / `klen` are `KeyLookups.br_nib` / `br_klen`, `depth` is
  `DepthBound.br_depth`, `mono` is `br_mono`.
* **`hloc_br_air`**, **`hloc_air`**: `hloc` for `walkRows cDc` with `keyOf := KeyDecode.keyOf tr`,
  from `Holds`, `BrStore` per active `BR` row, the uncovered `BR` ops and the `SN` rows.
* **`air_final_sorted_cDc`**: `FinalOrder.air_final_sorted` for the concrete decoder (`cDc_std`)
  with its `hloc` discharged as above.
-/

namespace StateM5a.RowFacts

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN
open StateM5a.RowBrU StateM5a.RowBrK StateM5a.RowHloc StateM5a.KeyDecode

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- The store and range part of a `BR` row's facts (premise: `VER` / SHA-256 decoding, limbs). -/
structure BrStore (σ : Store) (tr : Trace Fp) (pub : List Fp) (r : Nat) : Prop where
  old : OldOK σ (brIn tr pub r) (brOld tr pub r)
  new : ev tr 2 r pub (Br.c "gnew") = 1 → NewOK σ (brOut tr pub r) (brNew tr pub r)
  ranges : BrRanges tr pub r
  /-- `oDL`: the `MATQ`/`MATR` answer (`BusSplit.mat_reqresp`; responders `SN.oLM`). -/
  mat : ev tr 2 r pub (Br.c "oDL") = 1 →
    MatRel σ (keyOf tr) (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "st2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)))
      (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))
      (le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)))

theorem br_mem_dm {e : Expr}
    (he : e ∈ memChain (Br.c "oDH" + Br.c "oDL") (memLimbs Br.T "dm") Br.M []
      ((List.range 4).map fun k => Br.c "om" k) (fun k => Br.c "cyd" k)) : e ∈ Br.constraints := by
  unfold Br.constraints; exact List.mem_append_left _ (List.mem_append_right _ he)

theorem br_mem_rng_dm : ∀ b, b < 8 → memD (rcv B_RNG (Br.c "oDH" + Br.c "oDL") [Br.c "dm" b]) Br.interactions = true := by
  decide

theorem br_mem_rng_nvl : ∀ t, t < 4 → memD (rcv B_RNG (Br.c "oUV") [Br.c "nvl" t]) Br.interactions = true := by
  decide

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem ev_limb_lt {a b : Expr} (ha : ev tr 2 r pub a < 256) (hb : ev tr 2 r pub b < 256) :
    ev tr 2 r pub (a + K 256 * b) < 65536 := by
  rw [ev_hadd, ev_hmul, show K 256 = Expr.const 256 from rfl, ev_const]
  simp only [Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show 256 * ev tr 2 r pub b < P by omega),
    Nat.mod_eq_of_lt (show ev tr 2 r pub a + 256 * ev tr 2 r pub b < P by omega)]
  omega

theorem dm_limb (k : Nat) (hk : k < 4) :
    (memLimbs Br.T "dm").getD k 0 = Br.c "dm" (2 * k) + K 256 * Br.c "dm" (2 * k + 1) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 4000000 in
/-- **`om ≤ mem`** on an `oDH` / `oDL` row, from the `dm` chain and `RNG`. -/
theorem br_mono (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub (Br.c "oDH" + Br.c "oDL") = 1) (hR : BrRanges tr pub r)
    (hdm : ∀ b, b < 8 → ev tr 2 r pub (Br.c "dm" b) < 256) :
    le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) ≤ brMem tr pub r := by
  have hdl : ∀ k, k < 4 → ev tr 2 r pub ((memLimbs Br.T "dm").getD k 0) < 65536 := fun k hk => by
    rw [dm_limb k hk]; exact ev_limb_lt (hdm _ (by omega)) (hdm _ (by omega))
  have q := memChain_sound _ _ _ _ _ _ (fun e he => FieldRows.hold rfl hc (br_mem_dm he)) hg (by
    intro k hk
    have hd := hdl k hk
    have h := hR.1 k hk
    simp only [bE] at h
    have hm : ev tr 2 r pub (Br.M.getD k 0) < 65536 := h.1
    have ho : ev tr 2 r pub (Br.c "om" k) < 65536 := h.2.2.2
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp only [List.range, List.range.loop, List.map_cons, List.map_nil,
        List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at hm ho ⊢ <;>
      refine ⟨by omega, by omega, by simp [ev_const], by omega⟩)
  unfold V4 at q
  unfold brMem le4
  simp only [Br.M, memLimbs, limb16, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, E, bE] at q ⊢
  have e0 : ev tr 2 r pub (0 : Expr) = 0 := ev_const 0
  simp only [e0] at q
  change ((_ : Nat) : Int) + _ = _ at q
  unfold ev at q
  omega

end

/-- **`BrRowFacts` from `Holds` and the store / range part.** -/
theorem brRowFacts_of {tr : Trace Fp} {pub : List Fp} {σ : Store} {D : Nat} {extra : List Table} {nb np : Nat}
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    {r : Nat} (hr : r < tr.height 2) (hg : ev tr 2 r pub Br.gold = 1) (hS : BrStore σ tr pub r) :
    BrRowFacts σ (keyOf tr) tr pub r := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have h2 : (fullAir D extra nb np).tables[2]! = Br.table := by
    rw [WsDecode.full_get 2 (by decide)]; rfl
  refine ⟨hS.old, hS.new, hS.ranges, fun h => (KeyLookups.br_nib hH hN hr (ev_one_eval h)).1,
    fun h => KeyLookups.br_klen hH hL hr (ev_one_eval h), fun h => ?_, fun h => ?_, fun h t ht => ?_, hS.mat⟩
  · have := DepthBound.br_depth hH hN r hr h; omega
  · brfacts hc hg
    have hg' : ev tr 2 r pub (Br.c "oDH" + Br.c "oDL") = 1 := by
      rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]; omega
    refine br_mono hc hg' hS.ranges (fun b hb => ?_)
    exact WsDecode3.rng_rcv hH hxr (t := 2) (by simp [fullAir, m5aAir])
      (by rw [h2]; exact memD_mem (br_mem_rng_dm b hb)) hr (ev_one_eval hg')
  · exact WsDecode3.rng_rcv hH hxr (t := 2) (by simp [fullAir, m5aAir])
      (by rw [h2]; exact memD_mem (br_mem_rng_nvl t ht)) hr (ev_one_eval h)

/-- **`hloc` for the decoded `BR` rows on the AIR**, with `keyOf := KeyDecode.keyOf tr`. -/
theorem hloc_br_air {tr : Trace Fp} {pub : List Fp} (σ : Store) (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    (hS : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrStore σ tr pub r)
    (hbrRest : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ∀ o ∈ walkOps, o ∉ brCovered →
      ev tr 2 r pub (Br.c o) = 1 → LocalOK (Sem σ (keyOf tr)) (brRow tr pub r)) :
    ∀ x ∈ rowsOf cDc brW tr 2 pub, LocalOK (Sem σ (keyOf tr)) x :=
  hloc_br σ (keyOf tr) D extra nb np hH
    (fun r hr hg => brRowFacts_of hH hN hL hxr hr hg (hS r hr hg)) hbrRest

/-- **`hloc` for the concrete decoder on the AIR** (`keyOf := KeyDecode.keyOf tr`). -/
theorem hloc_air {tr : Trace Fp} {pub : List Fp} (σ : Store) (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    (hS : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrStore σ tr pub r)
    (hbrRest : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ∀ o ∈ walkOps, o ∉ brCovered →
      ev tr 2 r pub (Br.c o) = 1 → LocalOK (Sem σ (keyOf tr)) (brRow tr pub r))
    (hsn : ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem σ (keyOf tr)) x) :
    ∀ x ∈ walkRows cDc tr pub, LocalOK (SemS σ (keyOf tr)) x := by
  intro x hx
  rw [localOK_semS_iff]
  rcases List.mem_append.1 hx with hx | hx
  · exact hloc_br_air σ D extra nb np hH hN hL hxr hS hbrRest x hx
  · exact hsn x hx

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 in
/-- **Batched FINAL in the spec's order, for the concrete decoder.**  `FinalOrder.air_final_sorted`
with `Dc := cDc` (`cDc_std`) and `hloc` from `hloc_air`. -/
theorem air_final_sorted_cDc {tr : Trace Fp} {pub : List Fp} (σ : Store) (D : Nat)
    (writes : List (List Nat)) (prev post : Bytes) (n : Nat) (rest : List Table) (nb np : Nat)
    {compress : List Nat → List Nat → List Nat}
    (hP : Prem tr pub D (tapeTable (m5aTape writes prev post n) :: rest) nb np compress)
    (hr : ∀ T ∈ rest, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH)
    (hrN : ∀ T ∈ rest, sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KC = false ∧
      sendsOn T.interactions B_KCR = false)
    (hn : n < 2013265921) (hprev : prev.length = 32) (hpost : post.length = 32)
    (hS : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → BrStore σ tr pub r)
    (hbrRest : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ∀ o ∈ walkOps, o ∉ brCovered →
      ev tr 2 r pub (Br.c o) = 1 → LocalOK (Sem σ (keyOf tr)) (brRow tr pub r))
    (hsn : ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem σ (keyOf tr)) x)
    (cs : List (Bytes × Option Bytes)) (hlen : cs.length = n) (hcs : FinalChanges tr pub cs)
    (committed : List (Bytes × Option Bytes)) (hcomm : committed.Perm cs)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) (sortKV committed) = some (some T') ∧ rootHash (some T') = post :=
  air_final_sorted σ cDc cDc_std D writes prev post n rest nb np hP hr hrN hn hprev hpost
    (hloc_air σ D _ nb np hP.hH (fun T hT => (hP.hsil T hT).1) (fun T hT => (hP.hsil T hT).2.1)
      (fun T hT i hi => (hP.hx T hT i hi).2.2.2.1) hS hbrRest hsn)
    cs hlen hcs committed hcomm T hT0 hF

end StateM5a.RowFacts
