import StateM5a.RowBrN

/-!
# StateM5a.RowBrU — `LocalOK` of the `BR` rows that rewrite one slot (`oUD`)

The rewritten branch of a descending row keeps the old value (`nhv = hasv`, `nvl = vl`,
`nvh = vh`), keeps every slot but the selected one (`nf = f`; no split sibling: `sr = 0`), and puts
the child's result ref in the selected slot (`nisn = nhf`, `newch = nh`): `br_new_desc`.  Its
memory is `mem + nm − om` (`RowBrN.br_mem_desc`).  With the published new node
(`NewOK σ brOut brNew`, a premise like `OldOK`) this is `BusWalk.step_brDesc`.
-/

namespace StateM5a.RowBrU

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

set_option maxHeartbeats 4000000 in
/-- No split sibling: `Σ sr = oD1 + oSL = 0` gives every `sr_i = 0`. -/
theorem br_sr_zero (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oD1") = 0) (h2 : ev tr 2 r pub (Br.c "oSL") = 0) :
    ∀ i, i < 16 → (Br.c "sr" i).eval tr 2 r pub = 0 := by
  have bs : ∀ i, i < 16 → ev tr 2 r pub (Br.c "sr" i) ≤ 1 := fun i hi => by
    apply bool_le; apply FieldRows2.br_hold hc
    unfold Br.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind
  have h := FieldRows2.br_hold hc (e := sumE ((List.range 16).map fun i => Br.c "sr" i) - Br.c "oD1" - Br.c "oSL")
    (by unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
        memfind)
  have h' := eq_of_sub h
  rw [ev_sub, h1] at h'
  simp only [h2, Nat.sub_zero, Nat.mod_self, Nat.add_zero] at h'
  rw [Nat.mod_eq_of_lt (ev_lt _), ev_sumE, List.map_map] at h'
  have hs16 : ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sr" i)).sum ≤ 16 := by
    have := sum_le_length ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sr" i))
      (by intro x hx; simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨j, hj, rfl⟩ := hx; exact bs j hj)
    simpa using this
  rw [Nat.mod_eq_of_lt (by omega)] at h'
  intro i hi
  apply fp_of_ev0
  have := le_sum_of_mem' (l := (List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sr" i))
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  simp only [Function.comp] at this
  omega

set_option maxHeartbeats 4000000 in
theorem br_nf_eq (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) (i : Nat) (hi : i < 16) :
    (Br.c "nf" i - Br.c "gnew" * Br.c "f" i - Br.c "sel" i * Br.c "oUN" + Br.c "sel" i * Br.c "oDN" -
       Br.c "oSL" * (Br.c "sel" i + Br.c "sr" i)).eval tr 2 r pub = 0 := by
  apply hc; unfold Br.table Br.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

set_option maxHeartbeats 4000000 in
/-- The kept value (`gnew` rows other than `oUV`/`oDV`). -/
theorem br_val_kept (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (eGn : (Br.c "gnew").eval tr 2 r pub = 1) (eUV : (Br.c "oUV").eval tr 2 r pub = 0)
    (eDV : (Br.c "oDV").eval tr 2 r pub = 0) : brNewVal tr pub r = brVal tr pub r := by
  have g : (Br.c "gnew" - Br.c "oUV" - Br.c "oDV").eval tr 2 r pub = 1 := by evg; grind
  have hv : ev tr 2 r pub (Br.c "nhv") = ev tr 2 r pub (Br.c "hasv") :=
    FieldVer.eq_of_gate (FieldRows.hold (L := Br.constraints) rfl hc (by
      unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
      memfind)) (eval_one_ev g)
  have hl : ∀ t, t < 4 → (Br.c "nvl" t).eval tr 2 r pub = (Br.c "vl" t).eval tr 2 r pub := fun t ht =>
    Fp.ext (FieldVer.eq_of_gate (FieldRows.hold (L := Br.constraints) rfl hc (by
      unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
      memfind)) (eval_one_ev g))
  have hh : ∀ t, t < 32 → (Br.c "nvh" t).eval tr 2 r pub = (Br.c "vh" t).eval tr 2 r pub := fun t ht =>
    Fp.ext (FieldVer.eq_of_gate (FieldRows.hold (L := Br.constraints) rfl hc (by
      unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
      memfind)) (eval_one_ev g))
  have hlen : brNVlen tr pub r = brVlen tr pub r := by
    unfold brNVlen brVlen
    simp only [bE, limb16, eval_add, eval_mul, eval_K]
    rw [hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide)]
  have hbytes : (pack2 fun b => Br.c "nvh" b).map (bE tr pub r) = (pack2 fun b => Br.c "vh" b).map (bE tr pub r) := by
    simp only [pack2, List.map_map]
    apply List.map_congr_left; intro i hi
    have h := List.mem_range.1 hi
    simp only [Function.comp, bE, eval_add, eval_mul]
    rw [hh (2 * i) (by omega), hh (2 * i + 1) (by omega)]
  unfold brNewVal brVal
  rw [hv, hlen, hbytes]

set_option maxHeartbeats 4000000 in
/-- **The rewritten slots of a descending row**: slot `n` takes the child's result ref. -/
theorem br_kids_desc (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (eGn : (Br.c "gnew").eval tr 2 r pub = 1) (eUN : (Br.c "oUN").eval tr 2 r pub = 0)
    (eDN : (Br.c "oDN").eval tr 2 r pub = 0) (eSL : (Br.c "oSL").eval tr 2 r pub = 0)
    (hD1 : ev tr 2 r pub (Br.c "oD1") = 0)
    {n : Nat} (hn : n < 16) (hs1 : ev tr 2 r pub (Br.c "sel" n) = 1)
    (hs0 : ∀ j, j < 16 → j ≠ n → ev tr 2 r pub (Br.c "sel" j) = 0) (hfn : ev tr 2 r pub (Br.c "f" n) = 1) :
    brNewKids tr pub r = (brKids tr pub r).put n
      (some (refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)))) := by
  have hsr := br_sr_zero hc hD1 (ev_of_eval eSL)
  have hnf : ∀ i, i < 16 → (Br.c "nf" i).eval tr 2 r pub = (Br.c "f" i).eval tr 2 r pub := fun i hi => by
    have := br_nf_eq hc i hi; evga; grind
  have es1 := fp_of_ev1 hs1
  unfold brNewKids brKids
  apply kidsFrom_put _ _ _ _ _ 16 0 n hn
  · intro j hj hjn
    simp only [Nat.zero_add]
    have e0 := fp_of_ev0 (hs0 j hj hjn)
    have e1 := hsr j hj
    refine ⟨ev_eq_of_eval (hnf j hj), fun _ => ?_⟩
    unfold brNewSlot brSlot
    congr 1
    · simp only [bE, Br.nisn]; evga; grind
    · exact pack2_eval fun b => by simp only [Br.newch]; evga; grind
  · intro y hy
    cases hy
    simp only [Nat.zero_add]
    have e1 := hsr n hn
    refine ⟨(ev_eq_of_eval (hnf n hn)).trans hfn, ?_⟩
    unfold brNewSlot
    congr 1
    · simp only [bE, Br.nisn]; evga; grind
    · exact pack2_eval fun b => by simp only [Br.newch]; evga; grind
  · intro h; cases h

theorem le4_lt (l : List Fp) (h : ∀ k, k < 4 → (l.getD k 0).toNat < 65536) : le4 l < 18446744073709551616 := by
  have := h 0 (by decide); have := h 1 (by decide); have := h 2 (by decide); have := h 3 (by decide)
  unfold le4; omega

theorem brNMem_lt (hR : BrRanges tr pub r) : brNMem tr pub r < 18446744073709551616 := by
  apply le4_lt
  intro k hk
  have := (hR.1 k hk).2.1
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simpa [Br.NM, memLimbs, bE, List.range, List.range.loop] using this

set_option maxHeartbeats 8000000 in
/-- **`BR.oUD`**: upsert descend through a branch. -/
theorem localOK_oUD {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oUD") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hd : ev tr 2 r pub (Br.c "d") + 1 < P)
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) (hnew : NewOK σ (brOut tr pub r) (brNew tr pub r))
    (hR : BrRanges tr pub r) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 1 := f1
  have eGn : (Br.c "gnew").eval tr 2 r pub = 1 := f1
  have eU : (Br.c "mU").eval tr 2 r pub = 1 := f1
  have eD : (Br.c "mD").eval tr 2 r pub = 0 := f0
  have eUD : (Br.c "oUD").eval tr 2 r pub = 1 := f1
  have eSL : (Br.c "oSL").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 0 := f0
  have eDH : (Br.c "oDH").eval tr 2 r pub = 0 := f0
  have eDN : (Br.c "oDN").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have hD1 : ev tr 2 r pub (Br.c "oD1") = 0 := by omega
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, hs1, hs0, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn1 : ev tr 2 r pub (Br.c "f" n) = 1 := hfn.trans (eval_one_ev eGdn)
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 1 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  -- the row's result and the child's
  have hres := br_uout (tr := tr) (pub := pub) (r := r)
  have hcres := br_uin (tr := tr) (pub := pub) (r := r)
  have href : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).ref = brOut tr pub r := by
    rw [hres]; show refOf _ _ = refOf _ _
    rw [map_zip_fst _ _ eGn (by evg; grind) _ _ (by simp [pack2])]
    have e1 : E tr 2 r pub (Br.c "gnew" * Br.c "nref" + Br.gSame * Br.c "oref") = bE tr pub r (Br.c "nref") := by
      simp only [E, bE]; evg; grind
    rw [e1]
  have hnm : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).nm = brNMem tr pub r := by
    rw [hres]; show le4 _ = le4 _; rw [map_gate' _ _ eGn]
  have hom : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).om = brMem tr pub r := by
    rw [hres]; show le4 _ = le4 _; rw [map_gate' _ _ (by evg; grind)]
  have cref : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).ref =
      refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)) := by
    rw [hcres]; dsimp only
    rw [map_zip_fst _ _ (by evg; grind) eDS _ _ (by simp [pack2])]
    have e1 : E tr 2 r pub ((Br.c "oUD" + Br.c "oDH") * Br.c "nhf" + Br.c "oDS" * Br.isnSel) =
        E tr 2 r pub (Br.c "nhf") := by
      simp only [E]; evg; grind
    rw [e1]
  have cnm : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).nm =
      le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)) := by
    rw [hcres]; show le4 _ = le4 _
    rw [map_gate (Br.c "oUD" + Br.c "oDH") (fun k => Br.c "nm" k) (by evg; grind), List.map_map]; rfl
  have com : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).om =
      le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) := by
    rw [hcres]
  have hmem := br_mem_desc hc eGn eSL eUV eDV hR
  have hrec : Rec.branch (brVal tr pub r) ((brKids tr pub r).put n (some (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).ref))
      (brMem tr pub r + (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).nm - (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).om) =
      brNew tr pub r := by
    unfold brNew
    rw [br_val_kept hc eGn eUV eDV, cref, ← br_kids_desc hc eGn eUN eDN eSL hD1 hn hs1 hs0 hfn1, cnm, com]
    have : brMem tr pub r + le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)) -
        le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) = brNMem tr pub r := by omega
    rw [this]
  unfold LocalOK
  simp only [brRow]
  rw [if_pos (show brW.gdn.eval tr 2 r pub = 1 from eGdn)]
  dsimp only
  rw [br_din, br_dout]
  simp only [Sem, hmode]
  rw [payOf_kid, ev_d1 hd]
  intro hch x hx1 hx2
  refine step_brDesc (n := n) hold ?_ ?_ ?_ hom ?_ ?_ (hch x hx1 hx2)
  · rw [kids_at n hn, if_pos hfn1, slot_sel hn hs1 hs0]
  · rw [← hnn]; exact drop_cons_of_get hnib
  · rw [href, hrec]; exact hnew
  · rw [hnm, cnm, com]; omega
  · rw [hnm]; exact brNMem_lt hR

end

end StateM5a.RowBrU
