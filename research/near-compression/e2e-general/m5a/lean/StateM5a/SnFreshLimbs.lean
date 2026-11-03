import StateM5a.SnLimbsAll
import StateM5a.SnSplitEXA

/-!
# StateM5a.SnFreshLimbs — the limb premises of the split protocol from `Holds` (M5a-7)

The split rows' responders (`SnSplitLoc`, `SnFinal3` in M5a-6's `lean-wip/`) took three range
premises; here they are derived from `Holds` (the continued-key memory limbs through
`SnLimbsAll.SnContMem`):

* **`oslNodeLimbs_of`** (`OslNodeLimbs`): a split's new branch (`BR.oSL`) over an old *node*
  (`xl = 0`) holds the old side's memory `nm2 = xm` of the split row (`SPQ`); `xm` is `0` on a leaf
  split, and on an extension split the extension's child memory `CM` (bytes `cmb` in `RNG`, `z = 1`)
  or the re-keyed extension's new memory `sxm` (`SXR`, sent by an `oEM` row: its `NM`);
* **`oep_unm_lt`**: the child memory `unm` an `oEP` row receives on `SPR` is the sender's new memory
  (`oSL`: `BR` `NM`; `oEP`: `SN` `NM`);
* **`oem_unm_lt`**: the child memory `unm` an `oEM` row receives on `SXQ` is the split row's `CM`;
* **`snFreshNew_of`** (`SnFreshNew`): a short-key `oEP`/`oEM` row publishes its new node
  (`SnStore2.sn_newOK`), its new memory limbs and its `unm` are 16-bit.
-/

namespace StateM5a.SnFreshLimbs

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF StateM5a.SnSplit StateM5a.SnRange StateM5a.SnLimbsAll StateM5a.SnSplitLoc

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- The old-side memory limbs `nm2` of a split's new branch over a node (`xl = 0`). -/
def OslNodeLimbs (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 2 → ev tr 2 r pub (Br.c "oSL") = 1 → ev tr 2 r pub (Br.c "xl") = 0 →
    ∀ k, k < 4 → ev tr 2 r pub (Br.c "nm2" k) < 65536

/-- A short-key fresh-extension row (`oEP`/`oEM`) publishes its new record; its memory limbs (its
`nmem`, the received `unm`) are 16-bit. -/
def SnFreshNew (σ : Store) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ p, p < tr.height 3 → (ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) →
    ev tr 3 p pub (Sn.c "cont") = 0 →
    NewOK σ (snOut tr pub p) (snNew tr pub p) ∧ (∀ k, k < 4 → ev tr 3 p pub (Sn.NM.getD k 0) < 65536) ∧
      (∀ k, k < 4 → ev tr 3 p pub (Sn.c "unm" k) < 65536)

theorem CM_get (k : Nat) (hk : k < 4) : Sn.CM.getD k 0 = limb16 (fun b => Sn.c "cmb" b) k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)

include hH hxr in
/-- An extension split's child memory limbs `CM` (bytes in `RNG`). -/
theorem cm_lt {s : Nat} (hs : s < tr.height 3) (h1 : ev tr 3 s pub (Sn.c "oEX") = 1) :
    ∀ k, k < 4 → ev tr 3 s pub (Sn.CM.getD k 0) < 65536 := by
  intro k hk
  have rb : ∀ t, t < 8 → ev tr 3 s pub (Sn.c "cmb" t) < 256 := fun t ht =>
    WsDecode3.rng_rcv hH hxr (t := 3) (by simp [fullAir, m5aAir])
      (by rw [WsDecode.full_get 3 (by decide)]; exact memD_mem (sn_rng_cmb t ht)) hs (ev_one_eval h1)
  rw [CM_get k hk]; exact ev_limb16_byte3 (rb _ (by omega)) (rb _ (by omega))

include hH hxB hxD hxK hN hxr in
set_option maxHeartbeats 8000000 in
/-- **A split row's old-side memory `xm`** is 16-bit. -/
theorem xm_lt (hxS : ∀ T ∈ extra, sendsOn T.interactions B_SXR = false) (hCM : SnContMem tr pub)
    {s : Nat} (hs : s < tr.height 3) : ∀ k, k < 4 → ev tr 3 s pub (Sn.c "xm" k) < 65536 := by
  intro k hk
  have hc := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have e := eq_of_sub (FieldRows2.sn_hold hc (sn_mem_xm k hk))
  have bE := FieldWalk2.sn_flag_le hc "oEX" (by simp)
  have bz := bool_le (FieldRows2.sn_hold hc (e := bool (Sn.c "z")) (by unfold Sn.constraints; simp))
  rcases (by omega : ev tr 3 s pub (Sn.c "oEX") = 0 ∨ ev tr 3 s pub (Sn.c "oEX") = 1) with h0 | h1
  · rw [e, ev_gm0 h0]; omega
  rw [e, ev_gm h1]
  rcases (by omega : ev tr 3 s pub (Sn.c "z") = 0 ∨ ev tr 3 s pub (Sn.c "z") = 1) with z0 | z1
  · have g1 : ev tr 3 s pub (1 - Sn.c "z") = 1 := by rw [ev_sub, ev_one, z0]
    rw [ev_hadd, ev_gm0 z0, ev_gm g1, Nat.zero_add, Nat.mod_eq_of_lt (ev_lt _)]
    have gx : ev tr 3 s pub (Sn.c "oEX" * (1 - Sn.c "z")) = 1 := by rw [ev_gm h1]; exact g1
    obtain ⟨p, hp, hM, he⟩ := sxr_src hH hxS hs gx
    obtain ⟨-, -, -, -, -, em⟩ := hdr4_dec he (by simp [pack2])
    have e2 := map4_get (by simp [Sn.NM, memLimbs]) (by simp) em hk
    rw [getD_r4 _ hk] at e2
    have hcp := tbl_sn D extra nb np hH p (List.mem_range.2 hp)
    have := sn_NM_all hH hxB hxD hxK hN hxr hCM hp
      (gnew_of hcp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hM) k hk
    exact fpeq e2.symm this
  · have g0 : ev tr 3 s pub (1 - Sn.c "z") = 0 := by rw [ev_sub, ev_one, z1]
    rw [ev_hadd, ev_gm z1, ev_gm0 g0, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
    exact cm_lt hH hxr hs h1 k hk

include hH hxB hxD hxK hN hxr in
set_option maxHeartbeats 8000000 in
/-- **`OslNodeLimbs` from `Holds`** (and `SnContMem`). -/
theorem oslNodeLimbs_of (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SPQ = false)
    (hxS : ∀ T ∈ extra, sendsOn T.interactions B_SXR = false) (hCM : SnContMem tr pub) :
    OslNodeLimbs tr pub := by
  intro r hr h1 hx0 k hk
  obtain ⟨s, hs, -, hq⟩ := osl_spq hH hxQ hr h1
  have e : E tr 3 s pub (Sn.c "xm" k) = E tr 2 r pub ((1 - Br.c "xl") * Br.c "nm2" k) := by
    have := congrArg (fun l => l[23 + k]?) hq
    simp only [List.getElem?_map] at this
    rw [show snSpQ[23 + k]? = some (Sn.c "xm" k) by
          unfold snSpQ; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl,
        show brSpQ[23 + k]? = some ((1 - Br.c "xl") * Br.c "nm2" k) by
          unfold brSpQ; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl] at this
    simpa using this
  have g : ev tr 2 r pub (1 - Br.c "xl") = 1 := by rw [ev_sub, ev_one, hx0]
  have := xm_lt hH hxB hxD hxK hN hxr hxS hCM hs k hk
  have e' := congrArg Fp.toNat e
  change ev tr 3 s pub (Sn.c "xm" k) = ev tr 2 r pub ((1 - Br.c "xl") * Br.c "nm2" k) at e'
  rw [e', ev_gm2 g] at this
  exact this

include hH hxB hxD hxK hN hxr in
set_option maxHeartbeats 8000000 in
/-- **The child memory an `oEP` row receives** (`SPR`) is 16-bit. -/
theorem oep_unm_lt (hxP : ∀ T ∈ extra, sendsOn T.interactions B_SPR = false) (hCM : SnContMem tr pub)
    {p : Nat} (hp : p < tr.height 3) (h1 : ev tr 3 p pub (Sn.c "oEP") = 1) :
    ∀ k, k < 4 → ev tr 3 p pub (Sn.c "unm" k) < 65536 := by
  intro k hk
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_spr_rP) hp rfl (ev_one_eval h1)
  rcases spr_src hH hxP hm with ⟨r, hr, hr1, he⟩ | ⟨p', hp', hp1, he⟩
  · have he' : brSprS.map (E tr 2 r pub) = snSprP.map (E tr 3 p pub) := he.symm
    obtain ⟨-, -, -, -, em⟩ := spr_dec he' (by simp [pack2])
    have e := map4_get (by simp [Br.NM, memLimbs]) (by simp) em hk
    rw [getD_r4 _ hk] at e
    have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
    exact fpeq e.symm (br_NM_lt hH hxB hxD hxK hxr hr (osl_flags hc hr1).2.1 k hk)
  · have he' : snSprS.map (E tr 3 p' pub) = snSprP.map (E tr 3 p pub) := he.symm
    obtain ⟨-, -, -, -, em⟩ := spr_dec he' (by simp [pack2])
    have e := map4_get (by simp [Sn.NM, memLimbs]) (by simp) em hk
    rw [getD_r4 _ hk] at e
    have hc := tbl_sn D extra nb np hH p' (List.mem_range.2 hp')
    exact fpeq e.symm (sn_NM_all hH hxB hxD hxK hN hxr hCM hp'
      (gnew_of hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hp1) k hk)

include hH hxr in
set_option maxHeartbeats 8000000 in
/-- **The child memory an `oEM` row receives** (`SXQ`) is 16-bit. -/
theorem oem_unm_lt (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SXQ = false)
    {p : Nat} (hp : p < tr.height 3) (h1 : ev tr 3 p pub (Sn.c "oEM") = 1) :
    ∀ k, k < 4 → ev tr 3 p pub (Sn.c "unm" k) < 65536 := by
  intro k hk
  obtain ⟨s, hs, hX, he⟩ := sxq_src hH hxQ hp h1
  have hcs := tbl_sn D extra nb np hH s (List.mem_range.2 hs)
  have hE := (gX_of_oEX hcs hX).2
  obtain ⟨-, -, -, -, -, -, em⟩ := hdr5_dec he (by simp [pack2])
  have e := map4_get (by simp [Sn.CM, memLimbs]) (by simp) em hk
  rw [getD_r4 _ hk] at e
  exact fpeq e.symm (cm_lt hH hxr hs hE k hk)

include hH hxB hxD hxK hN hxr in
/-- **`SnFreshNew` from `Holds`** (and `SnContMem`). -/
theorem snFreshNew_of (hxP : ∀ T ∈ extra, sendsOn T.interactions B_SPR = false)
    (hxQ : ∀ T ∈ extra, sendsOn T.interactions B_SXQ = false) (hCM : SnContMem tr pub) :
    SnFreshNew (storeOf (VerStore.brVers tr pub ++ SnStore2.snVers tr pub)) tr pub := by
  intro p hp h hcont
  have hc := tbl_sn D extra nb np hH p (List.mem_range.2 hp)
  have hg : ev tr 3 p pub (Sn.c "gnew") = 1 := by
    rcases h with h | h
    · exact gnew_of hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h
    · exact gnew_of hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h
  refine ⟨SnStore2.sn_newOK hH hxB hxD hxK hN hxr hp hg hcont, sn_NM_lt hH hxB hxD hxK hN hxr hp hg hcont, ?_⟩
  rcases h with h | h
  · exact oep_unm_lt hH hxB hxD hxK hN hxr hxP hCM hp h
  · exact oem_unm_lt hH hxr hxQ hp h

end

end StateM5a.SnFreshLimbs
