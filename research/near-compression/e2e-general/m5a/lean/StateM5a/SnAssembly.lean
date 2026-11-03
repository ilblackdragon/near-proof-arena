import StateM5a.SnDepthAll
import StateM5a.VerAssembly

/-!
# StateM5a.SnAssembly — the `SN` side of `hloc` from `Holds`, and the final assembly

* `sn_unom_lt`: the child answer limbs `unm` / `uom` an `SN` row receives on `UP` are 16-bit
  (`BrRange.up_sent_lt`, the `SN` senders through `SnUpLimbs`);
* **`hloc_sn3`**: every decoded `SN` row is `LocalOK`, from `Holds` and the record-level premises
  `SnOldAll`, `SnNewAll`, `SnLimbs3` (old / new memory limbs, `oLR` value-length bytes),
  `SnLeafMemLt` (not implied by the AIR, see `RowSnAll2`) and `SnRest2` (continued keys, splits);
  the depth bound (`SnDepthAll.sn_depth_all`) and `unm`/`uom` are discharged;
* **`air_final_sorted_sn`**: `VerAssembly.air_final_sorted_ver` with `hsn` replaced by those
  premises.
-/

namespace StateM5a.SnAssembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM StateM5a.KeyDecode StateM5a.KeyLookups StateM5a.RowSnAll StateM5a.RowSnN
open StateM5a.RowSnAll2 StateM5a.BrRange

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem sn_ui_unm (k : Nat) (hk : k < 4) :
    snW.ui[20 + k]? = some ((Sn.c "oEU" + Sn.c "oEB") * Sn.c "unm" k) := by
  rw [sn_ui]; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem sn_ui_uom (k : Nat) (hk : k < 4) : snW.ui[24 + k]? = some (Sn.c "uom" k) := by
  rw [sn_ui]; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem sn_up_r : { bus := B_UP, mult := [snW.gdn], msg := snW.ui, send := false } ∈ Sn.interactions :=
  (List.mem_filter.1 (by rw [sn_ur]; exact List.mem_singleton_self _)).1

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : XSbHi D extra nb np tr pub)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
  (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)
  (hxU : ∀ T ∈ extra, sendsOn T.interactions B_UP = false)

include hH hxB hxD hxK hxr hxV hxU in
/-- **The child answer limbs** an `SN` row receives on `UP`. -/
theorem sn_unom_lt (hSU : SnUpLimbs tr pub) {r : Nat} (hr : r < tr.height 3)
    (hd : ev tr 3 r pub (Sn.c "gdn") = 1) :
    ∀ k, k < 4 → ev tr 3 r pub ((Sn.c "oEU" + Sn.c "oEB") * Sn.c "unm" k) < 65536 ∧
      ev tr 3 r pub (Sn.c "uom" k) < 65536 := by
  intro k hk
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_up_r) hr rfl (ev_one_eval hd)
  have hs := up_sent_lt hH hxB hxD hxK hxr hxV hxU hSU (recv_sent hH hm)
  have a := hs (20 + k) (by omega) (by omega)
  have b := hs (24 + k) (by omega) (by omega)
  simp only [Interaction.msgVal] at a b
  rw [getD_map_some (sn_ui_unm k hk)] at a
  rw [getD_map_some (sn_ui_uom k hk)] at b
  exact ⟨a, b⟩

end

/-- The range facts of one active `SN` walk row not derived here (old / new memory limbs: `VER` /
SHA-256 bytes / `RNG`; the `oLR` value-length bytes: `RNG` on version leaves, SHA-256 bytes on
hashed ones). -/
structure SnLimbsAt3 (tr : Trace Fp) (pub : List Fp) (r : Nat) : Prop where
  mem : ∀ k, k < 4 → ev tr 3 r pub (Sn.M.getD k 0) < 65536
  nmem : ev tr 3 r pub (Sn.c "gnew") = 1 → ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536
  nx : ev tr 3 r pub (Sn.c "oLR") = 1 → ∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256

def SnLimbs3 (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → snW.g.eval tr 3 r pub = 1 → ev tr 3 r pub (Sn.c "cont") = 0 → SnLimbsAt3 tr pub r

theorem gdn_of {tr : Trace Fp} {r : Nat} {pub : List Fp} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1)
    (h : ev tr 3 r pub (Sn.c "oEU") = 1 ∨ ev tr 3 r pub (Sn.c "oEB") = 1) :
    ev tr 3 r pub (Sn.c "gdn") = 1 ∧ ev tr 3 r pub (Sn.c "oEU" + Sn.c "oEB") = 1 := by
  obtain ⟨hb, -, -, -, -, -, hs, hF, hU, hD, -, -, hgdn, -, -⟩ := sn_flags' hc hg
  have b1 := hb "oEF" (by simp [snNames]); have b2 := hb "oEU" (by simp [snNames])
  have b3 := hb "oED" (by simp [snNames]); have b4 := hb "oES" (by simp [snNames])
  have b5 := hb "oEB" (by simp [snNames])
  clear hb
  rw [ev_hadd]
  omega

set_option maxHeartbeats 4000000 in
/-- **Every decoded `SN` row is `LocalOK`** (depth and child limbs from `Holds`). -/
theorem hloc_sn3 {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp} {σ : Store}
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hxB : XSbHi D extra nb np tr pub)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)
    (hxU : ∀ T ∈ extra, sendsOn T.interactions B_UP = false) (hSU : SnUpLimbs tr pub)
    (hold : SnOldAll σ tr pub) (hnew : SnNewAll σ tr pub) (hlim : SnLimbs3 tr pub)
    (hlm : SnLeafMemLt tr pub) (hrest : SnRest2 σ (keyOf tr) tr pub) :
    ∀ x ∈ rowsOf cDc snW tr 3 pub, LocalOK (Sem σ (keyOf tr)) x := by
  refine hloc_sn2 hH hN hL hold hnew ?_ hlm (SnDepthAll.sn_depth_all hH hN hL) hrest
  intro r hr hg hcont
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hg' : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1 := eval_one_ev hg
  have hl := hlim r hr hg hcont
  refine ⟨hl.mem, hl.nmem, fun h k hk => ?_, fun h k hk => ?_, hl.nx⟩
  · obtain ⟨hd, he⟩ := gdn_of hc hg' h
    have := (sn_unom_lt hH hxB hxD hxK hxr hxV hxU hSU hr hd k hk).1
    rwa [ev_gm he] at this
  · exact (sn_unom_lt hH hxB hxD hxK hxr hxV hxU hSU hr (gdn_of hc hg' (Or.inl h)).1 k hk).2

open StateM5a.Tape StateM5a.FinalOrder StateM5a.Sha512If NearSpecV3.D2 StateM5a.VerStore StateM5a.VerAssembly in
/-- **Batched FINAL in the spec's order, the version store from `VER`, the `SN` rows' `LocalOK`
from `Holds`** up to the record-level `SN` premises (`SnOldAll`, `SnNewAll`, `SnLimbs3`,
`SnLeafMemLt`, `SnRest2`). -/
theorem air_final_sorted_sn {tr : Trace Fp} {pub : List Fp} (D : Nat)
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
    (hold : SnOldAll (storeOf (brVers tr pub ++ snVers)) tr pub)
    (hnew : SnNewAll (storeOf (brVers tr pub ++ snVers)) tr pub) (hlim : SnLimbs3 tr pub)
    (hlm : SnLeafMemLt tr pub) (hrest : SnRest2 (storeOf (brVers tr pub ++ snVers)) (keyOf tr) tr pub)
    (cs : List (Bytes × Option Bytes)) (hlen : cs.length = n) (hcs : FinalChanges tr pub cs)
    (committed : List (Bytes × Option Bytes)) (hcomm : committed.Perm cs)
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) (sortKV committed) = some (some T') ∧ rootHash (some T') = post := by
  have hxU : ∀ T ∈ tapeTable (m5aTape writes prev post n) :: rest, sendsOn T.interactions B_UP = false :=
    fun T hT => by
      rcases List.mem_cons.1 hT with rfl | hT
      · exact tape_not writes prev post n B_UP (by decide) (by decide)
      · exact sendsOn_false_of fun i hi => (hr T hT i hi).2.1
  exact air_final_sorted_ver D writes prev post n rest nb np hP hr hrN hrS hxV hn hprev hpost snVers hnd hSU hSM
    hVl hVP hSib hMat hOsl
    (hloc_sn3 hP.hH (fun T hT => (hP.hsil T hT).1) (fun T hT => (hP.hsil T hT).2.1)
      hP.hxB (fun T hT => (hP.hsil T hT).2.2.2.1)
      (fun T hT => (hP.hsil T hT).2.2.2.2.1) (fun T hT i hi => (hP.hx T hT i hi).2.2.2.1) hxV hxU hSU
      hold hnew hlim hlm hrest)
    cs hlen hcs committed hcomm T hT0 hF

end StateM5a.SnAssembly
