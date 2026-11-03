import StateM5a.SnContLocA
import StateM5a.RowSnE

/-!
# StateM5a.SnContLocB — `LocalOK` of the upsert / delete-through-extension ops over any node key

`RowSnN.localOK_oLR` / `oEU` and `RowSnE.localOK_oES` / `oEB` / `oED` with the head key replaced
by a key `kk` given with: its old (and new) record `gRecK kk` (`OldOK` / `NewOK`), `|kk| = klen`,
`d + klen < P`, the walk key from `d` starting with `kk` (and `kid2`'s on `oED`), and the new
node's memory in terms of `kk` (`leafMem kk vlen` on `oLR`, `extOwnMem kk + unm` on `oEB`).
-/

namespace StateM5a.SnContLocB

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM StateM5a.RowSnD StateM5a.RowSnN StateM5a.RowSnE StateM5a.SnContRec1

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

set_option maxHeartbeats 8000000 in
/-- **`SN.oLR`**: upsert at the leaf holding the key: the leaf's value is replaced. -/
theorem localOK_oLR_K {σ : Store} {keyOf : Nat → List Nat} {kk : List Nat}
    (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1) (h1 : ev tr 3 r pub (Sn.c "oLR") = 1)
    (hKl : kk.length = ev tr 3 r pub (Sn.c "klen"))
    (hdk : ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") < P)
    (hold : OldOK σ (snIn tr pub r) (gRecK tr pub r kk (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b)))
    (hKd : (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")) =
      kk ++ (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")))
    (hklen : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "klen"))
    (hnew : NewOK σ (snOut tr pub r) (gRecK tr pub r kk (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b)))
    (hmem : snNMem tr pub r = leafMem kk (ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t)))
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536) (hlt : snNMem tr pub r < P)
    (hnx : ∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLR : (Sn.c "oLR").eval tr 3 r pub = 1 := s1
  have eLM : (Sn.c "oLM").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 1 := s1
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have eIsL : (Sn.c "isL").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 1 := by
    have : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eS : Sn.gS.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    evsn; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 1 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 1
    rw [show Sn.mode.eval tr 3 r pub = 1 by evsn; grind]; rfl
  have hA : ev tr 3 r pub (Sn.c "act") = 1 := by omega
  have g : ev tr 3 r pub (Sn.c "oLR" + Sn.c "oLM") = 1 := eval_one_ev (by simp only [eval_add, eLR, eLM]; grind)
  have hK := hKd
  have hlen := hklen (by evsn; grind)
  rw [SnContLocA.ev_dkl hdk] at hlen
  rw [List.drop_eq_nil_of_le (show (keyOf (ev tr 3 r pub (Sn.c "kid"))).length ≤
    ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") by omega), List.append_nil] at hK
  have hvl : ev tr 3 r pub (Sn.c "dvlen") = ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t) :=
    FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_vl) g
  have hvh : ((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 r pub) =
      (pack2 fun b => Sn.c "nx" (4 + b)).map (E tr 3 r pub) := by
    simp only [pack2, List.map_map]
    apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.1 hi
    have := FieldVer.eq_of_gate (FieldRows2.sn_hold hc (sn_mem_dvh i hi')) g
    simp only [Function.comp, E]
    rw [show 4 + (2 * i + 1) = 5 + 2 * i by omega]
    exact Fp.ext this
  rw [SnContLocA.gRecK_nleaf (by omega)] at hnew
  unfold snNVal at hnew
  rw [SnContLocA.gRecK_leaf (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, snpay_vlen, snpay_vh]
  intro x hx1 hx2
  have e1 : ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t) = x.length := by rw [← hvl]; exact hx1
  have e2 : bytesOf ((pack2 fun b => Sn.c "nx" (4 + b)).map (sE tr pub r)) = sha256 x := by
    rw [← hx2, hvh]
  rw [e1, e2, hmem, e1] at hnew
  refine step_leafRep hold hK ?_ ?_ ?_ ?_ ?_
  · dsimp only; rw [nu_ref eNu eS eX]; exact hnew
  · show le4 _ = le4 _
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]
  · dsimp only; rw [nu_nm eNu eX, hmem, e1]
  · have := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.vlenOf fun t => Sn.c "nx" t); omega
  · dsimp only; rw [nu_nm eNu eX]; omega

set_option maxHeartbeats 8000000 in
/-- **`SN.oEU`**: upsert descend through an extension. -/
theorem localOK_oEU_K {σ : Store} {keyOf : Nat → List Nat} {kk : List Nat}
    (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1) (h1 : ev tr 3 r pub (Sn.c "oEU") = 1)
    (hKl : kk.length = ev tr 3 r pub (Sn.c "klen"))
    (hdk : ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") < P)
    (hold : OldOK σ (snIn tr pub r) (gRecK tr pub r kk (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b)))
    (hKd : (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")) =
      kk ++ (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")))
    (hnew : NewOK σ (snOut tr pub r) (gRecK tr pub r kk (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b)))
    (hM : ∀ k, k < 4 → ev tr 3 r pub (Sn.M.getD k 0) < 65536)
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536)
    (hu : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "unm" k) < 65536)
    (ho : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "uom" k) < 65536) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eEU : (Sn.c "oEU").eval tr 3 r pub = 1 := s1
  have eEB : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
  have eES : (Sn.c "oES").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 1 := s1
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 1 := by
    have : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eS : Sn.gS.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    evsn; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 1 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 1
    rw [show Sn.mode.eval tr 3 r pub = 1 by evsn; grind]; rfl
  have hF : ev tr 3 r pub (Sn.c "gfr") = 0 := by
    have a1 : ev tr 3 r pub (Sn.c "oEB") = 0 := by omega
    have a2 : ev tr 3 r pub (Sn.c "oEP") = 0 := by omega
    have a3 : ev tr 3 r pub (Sn.c "oEM") = 0 := by omega
    rw [eq_of_sub (FieldRows2.sn_hold hc sn_mem_gfr), ev_hadd, ev_hadd, a1, a2, a3]
  have eG : ev tr 3 r pub (Sn.c "oEU" + Sn.c "gfr") = 1 := by rw [ev_hadd, hF, h1]
  have hmem := sn_mem_eu hc eG hF hM hN hu ho
  have hK := hKd
  have hkl : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + kk.length := by
    rw [hKl, SnContLocA.ev_dkl hdk]
  rw [← hKl] at hK
  rw [SnContLocA.gRecK_ext (by omega)] at hold
  rw [SnContLocA.gRecK_next (by omega)] at hnew
  have cref : refOf (E tr 3 r pub ((Sn.c "oEU" + Sn.c "oEB") * Sn.c "nxf" + Sn.c "oES" * Sn.c "xf"))
        ((((pack2 (fun b => Sn.c "nx" b)).zip (pack2 fun b => Sn.c "x" b)).map
          (fun (p, q) => (Sn.c "oEU" + Sn.c "oEB") * p + Sn.c "oES" * q)).map (E tr 3 r pub)) =
      snNChild tr pub r := by
    rw [map_zip_left (Sn.c "oEU" + Sn.c "oEB") (Sn.c "oES") (fun p => p) _ (by evsn; grind) eES _
      (by simp [pack2])]
    unfold snNChild; congr 1; simp only [E, eval_add, eval_mul, eEU, eEB, eES]; grind
  have cnm : le4 (((List.range 4).map fun t => (Sn.c "oEU" + Sn.c "oEB") * Sn.c "unm" t).map (E tr 3 r pub)) =
      le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 r pub)) := by
    rw [map_gate (Sn.c "oEU" + Sn.c "oEB") (fun t => Sn.c "unm" t) (by evsn; grind), List.map_map]; rfl
  unfold LocalOK
  simp only [snRow]
  rw [if_pos (show snW.gdn.eval tr 3 r pub = 1 from eGdn)]
  dsimp only
  rw [sn_din, sn_dout, sn_uin, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, hkl]
  intro hch x hx1 hx2
  refine step_extDesc hold hK ?_ ?_ ?_ ?_ (hch x hx1 hx2)
  · dsimp only; rw [nu_ref eNu eS eX, cref, cnm]
    have : snMem tr pub r + le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 r pub)) -
        le4 (((List.range 4).map fun t => Sn.c "uom" t).map (E tr 3 r pub)) = snNMem tr pub r := by omega
    rw [this]; exact hnew
  · show le4 _ = le4 _
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]
  · dsimp only; rw [nu_nm eNu eX, cnm]; omega
  · dsimp only; rw [nu_nm eNu eX]; exact snNMem_lt hN
end

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp} {σ : Store} {keyOf : Nat → List Nat} {kk : List Nat}
  (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
  (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1)
  (hKl : kk.length = ev tr 3 r pub (Sn.c "klen"))
  (hdk : ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") < P)
  (hold : OldOK σ (snIn tr pub r) (gRecK tr pub r kk (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b)))
  (hKd : (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")) =
    kk ++ (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")))
include hc hg hKl hdk hold hKd

set_option maxHeartbeats 8000000 in
/-- **`SN.oES`**: delete below an extension whose child is `SAME`: the extension is `SAME`. -/
theorem localOK_oES_K (h1 : ev tr 3 r pub (Sn.c "oES") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  dfacts hc hg (Or.inl h1)
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
  have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
  have a3 : (Sn.c "oED").eval tr 3 r pub = 0 := s0
  have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
  have a5 : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
  have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
  have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
  have a8 : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
  have a9 : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
  have a10 : (Sn.c "oES").eval tr 3 r pub = 1 := s1
  have eNu : gnu.eval tr 3 r pub = 0 := by simp only [gnu, eval_add, a1, a2, a5]; grind
  have eS : Sn.gS.eval tr 3 r pub = 1 := by simp only [Sn.gS, eval_add, a8, a9, a10]; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by simp only [Sn.gX, eval_add, a6, a7]; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_SAME := by
    rw [ev_eq_of_eval (b := K RK_SAME) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_SAME]
  have hrkc : ev tr 3 r pub (Sn.c "rkc") = RK_SAME := by
    rw [FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_rkS) h1, ev_K3]; rfl
  have hK := hKd
  have hkl : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + kk.length := by
    rw [hKl, SnContLocA.ev_dkl hdk]
  rw [← hKl] at hK
  rw [SnContLocA.gRecK_ext (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_pos (show snW.gdn.eval tr 3 r pub = 1 from eGdn)]
  dsimp only
  rw [sn_din, sn_dout, sn_uin, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, hkl]
  intro hch
  refine step_extSame hold hK hrkc hrk (same_ref eNu eS eX) ?_ hch
  show le4 _ = le4 _
  rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]

set_option maxHeartbeats 8000000 in
/-- **`SN.oEB`**: delete below an extension whose child is a kept branch (`HB`): a new extension
over the branch's new ref (`HE`), memory `extOwnMem k + nm`. -/
theorem localOK_oEB_K (h1 : ev tr 3 r pub (Sn.c "oEB") = 1)
    (hnew : NewOK σ (snOut tr pub r) (gRecK tr pub r kk (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b)))
    (hmem : snNMem tr pub r = extOwnMem kk + le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 r pub)))
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536)
    (hu : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "unm" k) < 65536) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  have hA : ev tr 3 r pub (Sn.c "act") = 1 := (sn_flags' hc hg).2.1
  have b2 : ev tr 3 r pub (Sn.c "oEP") = 0 := (sn_flags' hc hg).2.2.2.2.1
  have b3 : ev tr 3 r pub (Sn.c "oEM") = 0 := (sn_flags' hc hg).2.2.2.2.2.1
  dfacts hc hg (Or.inr (Or.inl h1))
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
  have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
  have a3 : (Sn.c "oED").eval tr 3 r pub = 0 := s0
  have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
  have a5 : (Sn.c "oEB").eval tr 3 r pub = 1 := s1
  have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
  have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
  have a8 : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
  have a9 : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
  have a10 : (Sn.c "oES").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 1 := by simp only [gnu, eval_add, a1, a2, a5]; grind
  have eS : Sn.gS.eval tr 3 r pub = 0 := by simp only [Sn.gS, eval_add, a8, a9, a10]; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by simp only [Sn.gX, eval_add, a6, a7]; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_HE := by
    rw [ev_eq_of_eval (b := K RK_HE) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_HE]
  have hrkc : ev tr 3 r pub (Sn.c "rkc") = RK_HB := by
    rw [FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_rkB) h1, ev_K3]; rfl
  have hF : ev tr 3 r pub (Sn.c "gfr") = 1 := by
    rw [eq_of_sub (FieldRows2.sn_hold hc sn_mem_gfr), ev_hadd, ev_hadd, h1, b2, b3]
  have eG : ev tr 3 r pub (Sn.c "oEU" + Sn.c "gfr") = 1 := by
    rw [ev_hadd, hF, ev_of_eval a2]
  have hK := hKd
  have hkl : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + kk.length := by
    rw [hKl, SnContLocA.ev_dkl hdk]
  rw [← hKl] at hK
  rw [SnContLocA.gRecK_ext (by omega)] at hold
  rw [SnContLocA.gRecK_next (by omega)] at hnew
  have cref : refOf (E tr 3 r pub ((Sn.c "oEU" + Sn.c "oEB") * Sn.c "nxf" + Sn.c "oES" * Sn.c "xf"))
        ((((pack2 (fun b => Sn.c "nx" b)).zip (pack2 fun b => Sn.c "x" b)).map
          (fun (p, q) => (Sn.c "oEU" + Sn.c "oEB") * p + Sn.c "oES" * q)).map (E tr 3 r pub)) =
      snNChild tr pub r := by
    rw [map_zip_left (Sn.c "oEU" + Sn.c "oEB") (Sn.c "oES") (fun p => p) _ (by evsn; grind) a10 _
      (by simp [pack2])]
    unfold snNChild; congr 1; simp only [E, eval_add, eval_mul, a2, a5, a10]; grind
  have cnm : le4 (((List.range 4).map fun t => (Sn.c "oEU" + Sn.c "oEB") * Sn.c "unm" t).map (E tr 3 r pub)) =
      le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 r pub)) := by
    rw [map_gate (Sn.c "oEU" + Sn.c "oEB") (fun t => Sn.c "unm" t) (by evsn; grind), List.map_map]; rfl
  unfold LocalOK
  simp only [snRow]
  rw [if_pos (show snW.gdn.eval tr 3 r pub = 1 from eGdn)]
  dsimp only
  rw [sn_din, sn_dout, sn_uin, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, hkl]
  intro hch
  refine step_extBranch hold hK hrkc hrk ?_ ?_ ?_ ?_ hch
  · dsimp only; rw [nu_ref eNu eS eX, cref, cnm, ← hmem]; exact hnew
  · show le4 _ = le4 _
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]
  · dsimp only; rw [nu_nm eNu eX, cnm]; exact hmem
  · dsimp only; rw [nu_nm eNu eX]; exact snNMem_lt hN

set_option maxHeartbeats 8000000 in
/-- **`SN.oED`**: delete below an extension whose child is a leaf descriptor (`LD`): the
extension's key joins the leaf's (`extendChild`), result `LD` with start `d`. -/
theorem localOK_oED_K (h1 : ev tr 3 r pub (Sn.c "oED") = 1)
    (hKd2 : ev tr 3 r pub (Sn.c "g2") = 1 → (keyOf (ev tr 3 r pub (Sn.c "kid2"))).drop (ev tr 3 r pub (Sn.c "d")) =
      kk ++ (keyOf (ev tr 3 r pub (Sn.c "kid2"))).drop (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")))
    (hkey : ∀ K, (∀ y ∈ keyOf K, y < 16) ∧ (keyOf K).length ≤ 2 ^ 21) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  have hg2' := (sn_flags' hc hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  dfacts hc hg (Or.inr (Or.inr h1))
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have a0 : (Sn.c "oLF").eval tr 3 r pub = 0 := s0
  have a0' : (Sn.c "oEF").eval tr 3 r pub = 0 := s0
  have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
  have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
  have a3 : (Sn.c "oED").eval tr 3 r pub = 1 := s1
  have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
  have a5 : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
  have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
  have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
  have a8 : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
  have a9 : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
  have a10 : (Sn.c "oES").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_LD := by
    rw [ev_eq_of_eval (b := K RK_LD) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_LD]
  have hrkc : ev tr 3 r pub (Sn.c "rkc") = RK_LD := by
    rw [FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_rkD) h1, ev_K3]; rfl
  have hg2 : ev tr 3 r pub (Sn.c "g2") = 1 := by
    rw [hg2', h1, ev_of_eval a6, ev_of_eval a7]
  have hK := hKd
  have hK2 := hKd2 hg2
  have hkl : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + kk.length := by
    rw [hKl, SnContLocA.ev_dkl hdk]
  rw [← hKl] at hK hK2
  rw [SnContLocA.gRecK_ext (by omega)] at hold
  have eal : ev tr 3 r pub (Sn.c "oLF" * Sn.vlenOf (fun t => Sn.c "x" t) + (Sn.c "oEF" + Sn.c "oED") * Sn.c "alen") =
      ev tr 3 r pub ((Sn.c "oEF" + Sn.c "oED") * Sn.c "alen") := by
    apply ev_eq_of_eval; evsn; grind
  have eah : bytesOf (((pack2 fun b => Sn.c "x" (4 + b)).zip ((List.range 16).map fun i => Sn.c "avh" i)).map
        (fun (p, q) => Sn.c "oLF" * p + (Sn.c "oEF" + Sn.c "oED") * q) |>.map (E tr 3 r pub)) =
      bytesOf (((List.range 16).map fun i => (Sn.c "oEF" + Sn.c "oED") * Sn.c "avh" i).map (E tr 3 r pub)) := by
    rw [map_zip_right (Sn.c "oLF") (Sn.c "oEF" + Sn.c "oED") (fun p => p) _ a0 (by evsn; grind) _
      (by simp [pack2]), map_gate (Sn.c "oEF" + Sn.c "oED") (fun i => Sn.c "avh" i) (by evsn; grind),
      List.map_map]
    rfl
  unfold LocalOK
  simp only [snRow]
  rw [if_pos (show snW.gdn.eval tr 3 r pub = 1 from eGdn)]
  dsimp only
  rw [sn_din, sn_dout, sn_uin, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, hkl]
  intro hch
  refine step_extLeaf (hc := hch) hold hK hrkc hrk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · dsimp only; exact ev_gm h1
  · dsimp only; exact eal
  · dsimp only; exact eah
  · dsimp only; rw [ev_gm h1, ev_gm h1, hkl]; exact hK2
  · show le4 _ = le4 _
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]
  · dsimp only
    refine leaf_wf _ _ _ (fun y hy => (hkey _).1 y (List.mem_of_mem_drop hy))
      (by rw [List.length_drop]; have := (hkey (ev tr 3 r pub (Sn.c "oED" * Sn.c "kid2"))).2; omega)
      (ev_lt _) ?_
    rw [bytesOf_length]; simp [pack2]

end

end StateM5a.SnContLocB
