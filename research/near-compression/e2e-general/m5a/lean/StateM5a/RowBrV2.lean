import StateM5a.RowBrV

/-!
# StateM5a.RowBrV2 — `localOK_oUV`, `localOK_oDV`

`BR.oUV` (write the value of the branch the key ends at) via `BusWalk.step_brUpVal`, and `BR.oDV`
(delete it, keeping `≥ 2` children) via `step_brDelVal`, from the pieces of `RowBrV`.  The new
value length is `|x|` exactly (`br_nvlen`: `RNG` bytes, `nvl₃ = 0`); `hnvl` is the `RNG` fact.
-/

namespace StateM5a.RowBrV2

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN
open StateM5a.RowBrU StateM5a.RowBrK StateM5a.RowBrV

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

/-- The `UP` result of a rewritten branch: new ref, new / old memory. -/
theorem new_up (eGn : (Br.c "gnew").eval tr 2 r pub = 1) (eS : Br.gSame.eval tr 2 r pub = 0)
    (eM : (Br.c "mU" + Br.c "mD").eval tr 2 r pub = 1) :
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).ref = brOut tr pub r ∧
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).nm = brNMem tr pub r ∧
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).om = brMem tr pub r := by
  rw [br_uout]
  refine ⟨?_, ?_, ?_⟩
  · show refOf _ _ = refOf _ _
    rw [map_zip_fst _ _ eGn eS _ _ (by simp [pack2])]
    have e1 : E tr 2 r pub (Br.c "gnew" * Br.c "nref" + Br.gSame * Br.c "oref") = bE tr pub r (Br.c "nref") := by
      simp only [E, bE]; evga; grind
    rw [e1]
  · show le4 _ = le4 _; rw [map_gate' _ _ eGn]
  · show le4 _ = le4 _; rw [map_gate' _ _ eM]

theorem payOf_vlen (m : Expr) (f : Expr → Fp) :
    (payOf ((payE (fun s j => Br.c s j) m).map f)).vlen = (f (Br.c "dvlen")).toNat := rfl

theorem payOf_vh (m : Expr) (f : Expr → Fp) :
    (payOf ((payE (fun s j => Br.c s j) m).map f)).vh = bytesOf (((List.range 16).map fun i => Br.c "dvh" i).map f) := by
  simp [payOf, payE]
  rw [List.take_of_length_le (by simp)]

set_option maxHeartbeats 8000000 in
/-- **`BR.oUV`**: write the value of the branch the key ends at. -/
theorem localOK_oUV {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oUV") = 1)
    (hklen : (keyOf (ev tr 2 r pub (Br.c "kid"))).length = ev tr 2 r pub (Br.c "d"))
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) (hnew : NewOK σ (brOut tr pub r) (brNew tr pub r))
    (hR : BrRanges tr pub r) (hnvl : ∀ t, t < 4 → ev tr 2 r pub (Br.c "nvl" t) < 256) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 0 := f0
  have eGn : (Br.c "gnew").eval tr 2 r pub = 1 := f1
  have eU : (Br.c "mU").eval tr 2 r pub = 1 := f1
  have eD : (Br.c "mD").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 1 := f1
  have eSL : (Br.c "oSL").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have hD1 : ev tr 2 r pub (Br.c "oD1") = 0 := by omega
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 1 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  obtain ⟨href, hnm, hom⟩ := new_up (tr := tr) (pub := pub) (r := r) eGn (by evg; grind) (by evg; grind)
  have hsel := br_sel_zero hc eAct (by evg; grind)
  have hkids := br_kids_same hc eGn eSL hD1 hsel
  have hmem := br_mem_uv hc eGn eSL eUV eDV hR
  have hlen := br_nvlen hc h1 hnvl
  have hnhv : ev tr 2 r pub (Br.c "nhv") = 1 := by
    have := FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_uv1) h1
    have b : ev tr 2 r pub (Br.c "nhv") ≤ 1 := bool_le (FieldRows.hold (L := Br.constraints) rfl hc (by
      unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp))
    rw [ev_sub, ev_one] at this
    omega
  have hbytes : (pack2 fun b => Br.c "nvh" b).map (bE tr pub r) =
      ((List.range 16).map fun i => Br.c "dvh" i).map (E tr 2 r pub) := by
    simp only [pack2, List.map_map]
    apply List.map_congr_left; intro i hi
    have h := List.mem_range.1 hi
    have e := Fp.ext (FieldVer.eq_of_gate (FieldRows.hold rfl hc (br_mem_uvh i h)) h1)
    simp only [Function.comp, bE, E, eval_add, eval_mul, eval_sm, eval_K] at e ⊢
    rw [e] <;> grind
  have hvo : valueMemOpt (brVal tr pub r) =
      (if ev tr 2 r pub (Br.c "hasv") = 1 then brVlen tr pub r + 50 else 0) := by
    unfold brVal; split <;> rfl
  unfold LocalOK
  simp only [brRow]
  rw [if_neg (show ¬ brW.gdn.eval tr 2 r pub = 1 from fun h => fp_zero_ne_one (eGdn.symm.trans h))]
  dsimp only
  rw [br_din]
  simp only [Sem, hmode]
  rw [payOf_kid]
  intro x hx1 hx2
  rw [payOf_vlen] at hx1
  rw [payOf_vh] at hx2
  have hxl : x.length = brNVlen tr pub r := by rw [hlen]; exact hx1.symm
  have hrec : Rec.branch (some (.ref x.length (sha256 x))) (brKids tr pub r)
      (brMem tr pub r + valueMem x.length - valueMemOpt (brVal tr pub r)) = brNew tr pub r := by
    unfold brNew brNewVal
    rw [if_pos hnhv, hkids, hbytes, ← hx2, ← hxl, hvo]
    congr 1
    unfold valueMem; rw [hxl]; omega
  refine step_brUpVal hold (drop_nil_of_len hklen) ?_ hom ?_ ?_ ?_
  · rw [href, hrec]; exact hnew
  · rw [hnm]; unfold valueMem; rw [hvo, hxl]; omega
  · rw [hxl]; unfold brNVlen
    have := (hR.2.1 0 (by decide)).2; have := (hR.2.1 1 (by decide)).2; omega
  · rw [hnm]; exact brNMem_lt hR

set_option maxHeartbeats 8000000 in
/-- **`BR.oDV`**: delete the value of the branch the key ends at, keeping `≥ 2` children. -/
theorem localOK_oDV {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oDV") = 1)
    (hklen : (keyOf (ev tr 2 r pub (Br.c "kid"))).length = ev tr 2 r pub (Br.c "d"))
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) (hnew : NewOK σ (brOut tr pub r) (brNew tr pub r))
    (hR : BrRanges tr pub r) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 0 := f0
  have eGn : (Br.c "gnew").eval tr 2 r pub = 1 := f1
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 1 := f1
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eSL : (Br.c "oSL").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 1 := f1
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have eUD : (Br.c "oUD").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 0 := f0
  have eDH : (Br.c "oDH").eval tr 2 r pub = 0 := f0
  have eDL : (Br.c "oDL").eval tr 2 r pub = 0 := f0
  have eDN : (Br.c "oDN").eval tr 2 r pub = 0 := f0
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 0 := f0
  have hD1 : ev tr 2 r pub (Br.c "oD1") = 0 := by omega
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 2 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  obtain ⟨href, hnm, hom⟩ := new_up (tr := tr) (pub := pub) (r := r) eGn (by evg; grind) (by evg; grind)
  have hrk : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).rk = RK_HB := by
    rw [br_uout]; exact ev_eq_nat (by evga; grind) (by decide)
  have hsel := br_sel_zero hc eAct (by evg; grind)
  have hkids := br_kids_same hc eGn eSL hD1 hsel
  have hmem := br_mem_dv hc eGn eSL eUV eDV hR
  have hhv : ev tr 2 r pub (Br.c "hasv") = 1 := by
    have := FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_dv1) h1
    have b := br_bool_hasv' hc (tr := tr) (pub := pub) (r := r)
    rw [ev_sub, ev_one] at this
    omega
  have hnhv : ev tr 2 r pub (Br.c "nhv") = 0 := FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_dvn) h1
  have hval : brVal tr pub r = some (.ref (brVlen tr pub r) (bytesOf ((pack2 fun b => Br.c "vh" b).map (bE tr pub r)))) := by
    unfold brVal; rw [if_pos hhv]
  -- at least two slots: `inv1·nkn = 1`, `inv2·(nkn − 1) = 1`
  have hcount := newKids_count hc (tr := tr) (pub := pub) (r := r)
  have hS : ((List.range 16).map fun i => ev tr 2 r pub (Br.c "nf" i)).sum ≤ 16 := by
    have := sum_le_length ((List.range 16).map fun i => ev tr 2 r pub (Br.c "nf" i))
      (by intro x hx; simp only [List.mem_map, List.mem_range] at hx; obtain ⟨i, hi, rfl⟩ := hx
          exact br_bool_nf hc i hi)
    simpa using this
  have hN : ev tr 2 r pub Br.nkn = ((List.range 16).map fun i => ev tr 2 r pub (Br.c "nf" i)).sum := by
    unfold Br.nkn; rw [ev_sumE, List.map_map]; exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hS (by decide))
  have i1 := fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_dvi1) h1)
  have i2 := fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_dvi2) h1)
  have n0 : ev tr 2 r pub Br.nkn ≠ 0 := by
    intro h0; have e0 := fp_of_ev0 h0; simp only [eval_sub, eval_mul, eval_lit] at i1; rw [e0] at i1; grind
  have n1 : ev tr 2 r pub Br.nkn ≠ 1 := by
    intro h0; have e0 := fp_of_ev1 h0; simp only [eval_sub, eval_mul, eval_lit] at i2; rw [e0] at i2; grind
  unfold LocalOK
  simp only [brRow]
  rw [if_neg (show ¬ brW.gdn.eval tr 2 r pub = 1 from fun h => fp_zero_ne_one (eGdn.symm.trans h))]
  dsimp only
  rw [br_din]
  simp only [Sem, hmode]
  rw [payOf_kid]
  unfold brOld at hold
  rw [hval] at hold
  refine step_brDelVal hold (drop_nil_of_len hklen) ?_ hrk ?_ hom ?_
  · rw [← hkids, hcount]; omega
  · rw [href]
    have hm : brMem tr pub r - valueMem (brVlen tr pub r) = brNMem tr pub r := by unfold valueMem; omega
    have hv : brNewVal tr pub r = none := by unfold brNewVal; rw [if_neg (by omega)]
    simp only [Slot.len]; rw [hm, ← hkids]
    unfold brNew at hnew; rw [hv] at hnew; exact hnew
  · rw [hnm]; show _ = brMem tr pub r - valueMem (brVlen tr pub r); unfold valueMem; omega

end

end StateM5a.RowBrV2
