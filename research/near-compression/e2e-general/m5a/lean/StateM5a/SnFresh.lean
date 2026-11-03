import StateM5a.SnSplitBus

/-! # StateM5a.SnFresh — `FreshRel` of a fresh-extension row (`SN.oEP` / `oEM`); `fresh_short` at
`cont = 0` (split out of `SnSplit`, M5a-7: each module within the 20 GB Lean budget). -/

namespace StateM5a.SnSplit

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit StateM5a.SnSplitBus StateM5a.RowSnN
open StateM5a.RowSnF

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Fresh extensions (`oEP`, `oEM`) -/

/-- **What a fresh-extension row establishes**: the extension `K_kid[d .. d + klen)` over the child
`(nxf, nx)` with memory `unm`, published under `snOut` with memory `snNMem`. -/
def FreshRel (σ : Store) (keyOf : Nat → List Nat) (tr : Trace Fp) (pub : List Fp) (p : Nat) : Prop :=
  ExtOver σ (epKey keyOf (ev tr 3 p pub (Sn.c "d")) (ev tr 3 p pub (Sn.c "d" + Sn.c "klen")) (ev tr 3 p pub (Sn.c "kid")))
    (snNChild tr pub p) (le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 p pub)))
    (snOut tr pub p) (snNMem tr pub p)

/-- The arithmetic of `fresh_flags` on plain naturals (`omega` on the trace's `ev` atoms directly is
over the memory budget: its atom comparison unfolds the column lookups). -/
theorem fresh_arith {act mF mU mD oLS oLM oEP oEM oLF oEF oLA oEA oLR oEU oLX oEX oLD oED oLZ oEZ oES oEB
    isL isE gA gfr : Nat} (bA : act ≤ 1) (bP : oEP ≤ 1) (bM : oEM ≤ 1)
    (c1 : mF + (mU + (mD + (oLS + (oLM + (oEP + (oEM + 0)))))) = act)
    (c2 : oLF + (oEF + (oLA + (oEA + 0))) = mF)
    (c3 : oLR + (oEU + (oLX + (oEX + 0))) = mU)
    (c4 : oLD + (oED + (oLZ + (oEZ + (oES + (oEB + 0))))) = mD)
    (c5 : isL = oLF + (oLR + (oLD + (oLS + (oLM + (oLA + (oLZ + (oLX + 0))))))))
    (c6 : isE = oEF + (oEU + (oED + (oEA + (oEZ + (oES + (oEB + (oEX + (oEP + (oEM + 0))))))))))
    (c8 : gA = oLA + (oEA + (oLZ + (oEZ + (oLX + (oEX + 0))))))
    (c9 : gfr = oEB + (oEP + (oEM + 0)))
    (h : oEP = 1 ∨ oEM = 1) : gA = 0 ∧ isL = 0 ∧ isE = 1 ∧ act = 1 ∧ oEU = 0 ∧ gfr = 1 := by
  omega

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

open StateM5a.FieldWalk2 in
set_option maxHeartbeats 4000000 in
/-- The op bundle of a fresh-extension row. -/
theorem fresh_flags {p : Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 p pub = 0)
    (h : ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1) :
    ev tr 3 p pub (Sn.c "gA") = 0 ∧ ev tr 3 p pub (Sn.c "isL") = 0 ∧ ev tr 3 p pub (Sn.c "isE") = 1 ∧
    ev tr 3 p pub (Sn.c "act") = 1 ∧ ev tr 3 p pub (Sn.c "oEU") = 0 ∧ ev tr 3 p pub (Sn.c "gfr") = 1 := by
  have hb : ∀ s ∈ snNames, ev tr 3 p pub (Sn.c s) ≤ 1 := fun s hs => sn_flag_le hc s hs
  have S := fun (s : String) (l : List String) (h : s :: l ⊆ snNames) (hl : l.length ≤ 63) =>
    sn_sum hc s l h hl
  have e1 := S "mF" ["mU", "mD", "oLS", "oLM", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e2 := S "oLF" ["oEF", "oLA", "oEA"] (by simp [snNames]) (by simp)
  have e3 := S "oLR" ["oEU", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e4 := S "oLD" ["oED", "oLZ", "oEZ", "oES", "oEB"] (by simp [snNames]) (by simp)
  have e5 := S "oLF" ["oLR", "oLD", "oLS", "oLM", "oLA", "oLZ", "oLX"] (by simp [snNames]) (by simp)
  have e6 := S "oEF" ["oEU", "oED", "oEA", "oEZ", "oES", "oEB", "oEX", "oEP", "oEM"] (by simp [snNames]) (by simp)
  have e8 := S "oLA" ["oEA", "oLZ", "oEZ", "oLX", "oEX"] (by simp [snNames]) (by simp)
  have e9 := S "oEB" ["oEP", "oEM"] (by simp [snNames]) (by simp)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.sum_cons, List.sum_nil, sc]
    at e1 e2 e3 e4 e5 e6 e8 e9
  have c1 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_act)
  have c2 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mF)
  have c3 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mU)
  have c4 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_mD)
  have c5 := eq_of_sub (hold rfl hc sn_mem_isL)
  have c6 := eq_of_sub (hold rfl hc FieldWalk.sn_mem_isE)
  have c8 := eq_of_sub (hold rfl hc sn_mem_gA)
  have c9 := eq_of_sub (hold rfl hc sn_mem_gfr)
  rw [e1] at c1; rw [e2] at c2; rw [e3] at c3; rw [e4] at c4; rw [e5] at c5; rw [e6] at c6
  rw [e8] at c8; rw [e9] at c9
  exact fresh_arith (hb "act" (by simp [snNames])) (hb "oEP" (by simp [snNames])) (hb "oEM" (by simp [snNames]))
    c1 c2 c3 c4 c5 c6 c8 c9 h

set_option maxHeartbeats 8000000 in
/-- **`FreshRel` of a short-key fresh-extension row** (`cont = 0`). -/
theorem fresh_short {σ : Store} (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) {p : Nat} (hp : p < tr.height 3)
    (h : ev tr 3 p pub (Sn.c "oEP") = 1 ∨ ev tr 3 p pub (Sn.c "oEM") = 1)
    (hcont : ev tr 3 p pub (Sn.c "cont") = 0) (hnew : NewOK σ (snOut tr pub p) (snNew tr pub p))
    (hN : ∀ k, k < 4 → ev tr 3 p pub (Sn.NM.getD k 0) < 65536)
    (hu : ∀ k, k < 4 → ev tr 3 p pub (Sn.c "unm" k) < 65536) : FreshRel σ (keyOf tr) tr pub p := by
  have hc := tbl_sn D extra nb np hH p (List.mem_range.2 hp)
  obtain ⟨hA0, hL0, hE1, hA, hEU, hF⟩ := fresh_flags hc h
  -- depth: the first key nibble is looked up
  have hb0 : ev tr 3 p pub (Sn.b 0) = 1 := by
    rw [sn_b_eq_a hc hA0 0 (by decide)]
    have := FieldRows2.sn_hold hc SnDepthAll.sn_mem_ea0
    rw [RowSnN.ev_gm hE1, ev_sub, ev_one] at this
    have := ev_lt (tr := tr) (t := 3) (r := p) (pub := pub) (Sn.a 0)
    omega
  have hd0 := (sn_nib hH hxN 0 (by decide) hp (fp_of_ev1 hb0)).2
  rw [SnDepthAll.ev_d0 (e := K 0) (ev_const 0)] at hd0
  have hd : ev tr 3 p pub (Sn.c "d") + 64 < P := by omega
  have hK := sn_key_prefix (keyOf := keyOf tr) hc hcont hA0 hd (fun j hj hgj => (sn_nib hH hxN j hj hp hgj).1)
  have hkl0 := (FieldRows2.sn_flags hc hcont).1
  have hkl : ev tr 3 p pub (Sn.c "d" + Sn.c "klen") = ev tr 3 p pub (Sn.c "d") + (snKey tr pub p).length := by
    rw [snKey_length, ev_hadd, Nat.mod_eq_of_lt (by omega)]
  rw [← snKey_length] at hK
  have eG : ev tr 3 p pub (Sn.c "oEU" + Sn.c "gfr") = 1 := by rw [ev_hadd, hF, hEU]
  have hmem := RowSnE.sn_mem_eb hc hA hcont eG hF hN hu
  unfold FreshRel
  rw [hkl, epKey_eq hK]
  refine extOver_of_new (by rw [snNew_ext (by omega)] at hnew; exact hnew) hmem ⟨?_, snNMem_lt hN, ?_⟩
  · have hb := (RowFacts.keyOf_bounds hH (ev tr 3 p pub (Sn.c "kid"))).1
    unfold nibblesOk
    rw [List.all_eq_true]
    intro y hy
    have : y ∈ (keyOf tr (ev tr 3 p pub (Sn.c "kid"))).drop (ev tr 3 p pub (Sn.c "d")) := by
      rw [hK]; exact List.mem_append_left _ hy
    exact decide_eq_true (hb y (List.mem_of_mem_drop this))
  · rw [hp_length, snKey_length]; omega

end

end StateM5a.SnSplit
