import StateM5a.RowBrU

/-!
# StateM5a.RowBrK — `LocalOK` of the `BR` rows that keep the branch after a delete (`oDH`, `oDN`)

Via `BusWalk.step_brKeep`: the child's result (a rewritten node `HB`/`HE` under its ref, `oDH`;
nothing, `oDN`) replaces the selected slot; the branch keeps `≥ 1` child and (a value or `≥ 2`
children) — `FieldRows.br_keep` on the new slot flags, counted by `kidsFrom_count`.

Memory: the row checks `nmem + om = mem + nm` exactly (`RowBrN.br_mem_desc`); the spec's
`PTrie.del` computes `mem − om + nm` with truncated subtraction, so for `oDH` the lemma takes
`om ≤ mem` (the child's old memory is at most its parent's — true of every honest trie; the
spec's `wf` does not state it) as a premise (`hmono`).  For `oDN` (`nm = 0`) it follows.
-/

namespace StateM5a.RowBrK

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN
open StateM5a.RowBrU

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem kidsFrom_count (fl : Nat → Nat) (rf : Nat → Ref) (hb : ∀ j, fl j ≤ 1) :
    ∀ k i, (kidsFrom fl rf i k).count = ((List.range' i k).map fl).sum
  | 0, _ => rfl
  | k + 1, i => by
    simp only [RowBr.kidsFrom, List.range'_succ, List.map_cons, List.sum_cons]
    have ih := kidsFrom_count fl rf hb k (i + 1)
    have := hb i
    split
    · rename_i h; simp only [RKids.count, ih, h]; omega
    · rename_i h; simp only [RKids.count, ih]; omega

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

set_option maxHeartbeats 4000000 in
theorem br_bool_nf (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) (i : Nat) (hi : i < 16) :
    ev tr 2 r pub (Br.c "nf" i) ≤ 1 := by
  apply bool_le; apply FieldRows2.br_hold hc
  unfold Br.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

/-- The number of new slots is `Σ nf`. -/
theorem newKids_count (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) :
    (brNewKids tr pub r).count = ((List.range 16).map fun i => ev tr 2 r pub (Br.c "nf" i)).sum := by
  unfold brNewKids
  have hb : ∀ j, (fun i => ev tr 2 r pub (Br.c "nf" i)) j ≤ 1 ∨ 16 ≤ j := fun j => by
    rcases Nat.lt_or_ge j 16 with h | h
    · exact Or.inl (br_bool_nf hc j h)
    · exact Or.inr h
  -- only the first 16 indices matter
  have e : kidsFrom (fun i => ev tr 2 r pub (Br.c "nf" i)) (brNewSlot tr pub r) 0 16 =
      kidsFrom (fun i => if i < 16 then ev tr 2 r pub (Br.c "nf" i) else 0) (brNewSlot tr pub r) 0 16 :=
    (kidsFrom_congr _ _ _ _ 16 0 (fun j hj => by simp [hj])).symm
  rw [e, kidsFrom_count _ _ (fun j => by
      by_cases h : j < 16
      · simp only [if_pos h]; exact br_bool_nf hc j h
      · simp only [if_neg h]; omega) 16 0, List.range_eq_range']
  congr 1

theorem br_mem_rkdh : Br.c "oDH" * (Br.c "rk" - K RK_HB) * (Br.c "rk" - K RK_HE) ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem br_mem_rkdn : Br.c "oDN" * (Br.c "rk" - K RK_NONE) ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp

set_option maxHeartbeats 4000000 in
theorem br_bool_hasv' (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0) :
    ev tr 2 r pub (Br.c "hasv") ≤ 1 := bool_le (FieldRows.hold rfl hc br_bool_hasv)

/-- The child's `rk` of an `oDH` row: `HB` or `HE`. -/
theorem rk_dh (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oDH") = 1) :
    ev tr 2 r pub (Br.c "rk") = RK_HB ∨ ev tr 2 r pub (Br.c "rk") = RK_HE := by
  have h := FieldRows.hold rfl hc br_mem_rkdh
  change ev tr 2 r pub (Expr.mul (Expr.mul _ _) _) = 0 at h
  rcases ev_mul_eq_zero h with h | h
  · have := FieldVer.gate_zero h h1
    left; have e := eq_of_sub this; rw [e]; rfl
  · right; have e := eq_of_sub h; rw [e]; rfl

set_option maxHeartbeats 4000000 in
/-- The rewritten slots of `oDN`: slot `n` is removed. -/
theorem br_kids_del (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (eGn : (Br.c "gnew").eval tr 2 r pub = 1) (eUN : (Br.c "oUN").eval tr 2 r pub = 0)
    (eDN : (Br.c "oDN").eval tr 2 r pub = 1) (eSL : (Br.c "oSL").eval tr 2 r pub = 0)
    (hD1 : ev tr 2 r pub (Br.c "oD1") = 0)
    {n : Nat} (hn : n < 16) (hs1 : ev tr 2 r pub (Br.c "sel" n) = 1)
    (hs0 : ∀ j, j < 16 → j ≠ n → ev tr 2 r pub (Br.c "sel" j) = 0) (hfn : ev tr 2 r pub (Br.c "f" n) = 1) :
    brNewKids tr pub r = (brKids tr pub r).put n none := by
  have hsr := br_sr_zero hc hD1 (ev_of_eval eSL)
  have es1 := fp_of_ev1 hs1
  have ef1 := fp_of_ev1 hfn
  unfold brNewKids brKids
  apply kidsFrom_put _ _ _ _ _ 16 0 n hn
  · intro j hj hjn
    simp only [Nat.zero_add]
    have e0 := fp_of_ev0 (hs0 j hj hjn)
    have e1 := hsr j hj
    have hnf := br_nf_eq hc j hj
    refine ⟨ev_eq_of_eval (by evga; grind), fun _ => ?_⟩
    unfold brNewSlot brSlot
    congr 1
    · simp only [bE, Br.nisn]; evga; grind
    · exact pack2_eval fun b => by simp only [Br.newch]; evga; grind
  · intro y hy; cases hy
  · intro _
    simp only [Nat.zero_add]
    have e1 := hsr n hn
    have hnf := br_nf_eq hc n hn
    have : (Br.c "nf" n).eval tr 2 r pub = 0 := by evga; grind
    rw [show ev tr 2 r pub (Br.c "nf" n) = 0 from ev_of_eval this]; decide

theorem br_mem_dnnm (k : Nat) (hk : k < 4) : Br.c "oDN" * Br.c "nm" k ∈ Br.constraints := by
  unfold Br.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  memfind

/-- The `UP` result of a kept branch: kind `HB`, the new ref, new / old memory. -/
theorem keep_up (eGn : (Br.c "gnew").eval tr 2 r pub = 1) (eS : Br.gSame.eval tr 2 r pub = 0)
    (eK : Br.gKeep.eval tr 2 r pub = 1)
    (e1 : (Br.c "oUD").eval tr 2 r pub = 0) (e2 : (Br.c "oUN").eval tr 2 r pub = 0)
    (e3 : (Br.c "oUV").eval tr 2 r pub = 0) (e4 : (Br.c "oDV").eval tr 2 r pub = 0)
    (e5 : (Br.c "oD1").eval tr 2 r pub = 0)
    (eM : (Br.c "mU" + Br.c "mD").eval tr 2 r pub = 1) :
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).rk = RK_HB ∧
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).ref = brOut tr pub r ∧
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).nm = brNMem tr pub r ∧
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).om = brMem tr pub r := by
  rw [br_uout]
  refine ⟨ev_eq_nat (by evga; grind) (by decide), ?_, ?_, ?_⟩
  · show refOf _ _ = refOf _ _
    rw [map_zip_fst _ _ eGn eS _ _ (by simp [pack2])]
    have e1 : E tr 2 r pub (Br.c "gnew" * Br.c "nref" + Br.gSame * Br.c "oref") = bE tr pub r (Br.c "nref") := by
      simp only [E, bE]; evga; grind
    rw [e1]
  · show le4 _ = le4 _; rw [map_gate' _ _ eGn]
  · show le4 _ = le4 _; rw [map_gate' _ _ eM]

set_option maxHeartbeats 8000000 in
/-- **`BR.oDN`**: delete below a branch whose child vanished; the branch keeps. -/
theorem localOK_oDN {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oDN") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hd : ev tr 2 r pub (Br.c "d") + 1 < P)
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) (hnew : NewOK σ (brOut tr pub r) (brNew tr pub r))
    (hR : BrRanges tr pub r) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 1 := f1
  have eGn : (Br.c "gnew").eval tr 2 r pub = 1 := f1
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 1 := f1
  have eDN : (Br.c "oDN").eval tr 2 r pub = 1 := f1
  have eSL : (Br.c "oSL").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 0 := f0
  have eUD : (Br.c "oUD").eval tr 2 r pub = 0 := f0
  have eDH : (Br.c "oDH").eval tr 2 r pub = 0 := f0
  have eDL : (Br.c "oDL").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 0 := f0
  have hD1 : ev tr 2 r pub (Br.c "oD1") = 0 := by omega
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, hs1, hs0, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn1 : ev tr 2 r pub (Br.c "f" n) = 1 := hfn.trans (eval_one_ev eGdn)
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 2 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  obtain ⟨hrk, href, hnm, hom⟩ := keep_up (tr := tr) (pub := pub) (r := r) eGn (by evg; grind)
    (by evg; grind) eUD eUN eUV eDV eD1 (by evg; grind)
  have hrkc : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).rk = RK_NONE := by
    rw [br_uin]; show ev tr 2 r pub (Br.c "rk") = RK_NONE
    rw [FieldVer.eq_of_gate (FieldRows.hold rfl hc br_mem_rkdn) h1]; rfl
  have hmem := br_mem_desc hc eGn eSL eUV eDV hR
  have hnm0 : le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)) = 0 := by
    have z : ∀ k, k < 4 → (Br.c "nm" k).eval tr 2 r pub = 0 := fun k hk =>
      fp_of_ev0 (FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_dnnm k hk)) h1)
    simp only [le4, List.range, List.range.loop, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, E, z 0 (by decide), z 1 (by decide), z 2 (by decide), z 3 (by decide)]
    rfl
  have com : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).om =
      le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) := by
    rw [br_uin]
  have hkeep := FieldRows.br_keep hc (eval_one_ev (by evg; grind)) (br_bool_nf hc)
  have hcount := newKids_count hc (tr := tr) (pub := pub) (r := r)
  have hkd := br_kids_del hc eGn eUN eDN eSL hD1 hn hs1 hs0 hfn1
  unfold LocalOK
  simp only [brRow]
  rw [if_pos (show brW.gdn.eval tr 2 r pub = 1 from eGdn)]
  dsimp only
  rw [br_din, br_dout]
  simp only [Sem, hmode]
  rw [payOf_kid, ev_d1 hd]
  intro hch
  refine step_brKeep (n := n) hold ?_ ?_ (Or.inl hrkc) hrk ?_ ?_ ?_ hom ?_ ?_ hch
  · rw [kids_at n hn, if_pos hfn1, slot_sel hn hs1 hs0]
  · rw [← hnn]; exact drop_cons_of_get hnib
  · rw [if_pos hrkc, if_pos hrkc, href, com, ← hkd]
    have : brMem tr pub r - le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) + 0 =
        brNMem tr pub r := by omega
    unfold brNew at hnew
    rw [br_val_kept hc eGn eUV eDV] at hnew
    rw [this]; exact hnew
  · rw [if_pos hrkc, ← hkd, hcount]; omega
  · intro hv
    rw [if_pos hrkc, ← hkd, hcount]
    have : ev tr 2 r pub (Br.c "hasv") = 0 := by
      have hb := br_bool_hasv' hc
      unfold brVal at hv
      split at hv
      · cases hv
      · omega
    have := hkeep.2 this; omega
  · rw [if_pos hrkc, hnm, com]; omega
  · rw [hnm]; exact brNMem_lt hR

set_option maxHeartbeats 8000000 in
/-- **`BR.oDH`**: delete below a branch whose child is a rewritten node (`HB`/`HE`); the branch
keeps.  `hmono`: the child's old memory is at most the branch's (see the module note). -/
theorem localOK_oDH {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oDH") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hd : ev tr 2 r pub (Br.c "d") + 1 < P)
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) (hnew : NewOK σ (brOut tr pub r) (brNew tr pub r))
    (hR : BrRanges tr pub r)
    (hmono : le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) ≤ brMem tr pub r) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 1 := f1
  have eGn : (Br.c "gnew").eval tr 2 r pub = 1 := f1
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 1 := f1
  have eDH : (Br.c "oDH").eval tr 2 r pub = 1 := f1
  have eSL : (Br.c "oSL").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 0 := f0
  have eUD : (Br.c "oUD").eval tr 2 r pub = 0 := f0
  have eDN : (Br.c "oDN").eval tr 2 r pub = 0 := f0
  have eDL : (Br.c "oDL").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 0 := f0
  have hD1 : ev tr 2 r pub (Br.c "oD1") = 0 := by omega
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, hs1, hs0, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn1 : ev tr 2 r pub (Br.c "f" n) = 1 := hfn.trans (eval_one_ev eGdn)
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 2 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  obtain ⟨hrk, href, hnm, hom⟩ := keep_up (tr := tr) (pub := pub) (r := r) eGn (by evg; grind)
    (by evg; grind) eUD eUN eUV eDV eD1 (by evg; grind)
  have hrk2 : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).rk = RK_HB ∨
      (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).rk = RK_HE := by
    rw [br_uin]; exact rk_dh hc h1
  have hne : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).rk ≠ RK_NONE := by
    rcases hrk2 with e | e <;> rw [e] <;> decide
  have cref : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).ref =
      refOf (E tr 2 r pub (Br.c "nhf")) ((pack2 fun b => Br.c "nh" b).map (E tr 2 r pub)) := by
    rw [br_uin]; dsimp only
    rw [map_zip_fst _ _ (by evg; grind) eDS _ _ (by simp [pack2])]
    have e1 : E tr 2 r pub ((Br.c "oUD" + Br.c "oDH") * Br.c "nhf" + Br.c "oDS" * Br.isnSel) =
        E tr 2 r pub (Br.c "nhf") := by
      simp only [E]; evg; grind
    rw [e1]
  have cnm : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).nm =
      le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)) := by
    rw [br_uin]; show le4 _ = le4 _
    rw [map_gate (Br.c "oUD" + Br.c "oDH") (fun k => Br.c "nm" k) (by evg; grind), List.map_map]; rfl
  have com : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).om =
      le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) := by
    rw [br_uin]
  have hmem := br_mem_desc hc eGn eSL eUV eDV hR
  have hkeep := FieldRows.br_keep hc (eval_one_ev (by evg; grind)) (br_bool_nf hc)
  have hcount := newKids_count hc (tr := tr) (pub := pub) (r := r)
  have hkd := br_kids_desc hc eGn eUN eDN eSL hD1 hn hs1 hs0 hfn1
  unfold LocalOK
  simp only [brRow]
  rw [if_pos (show brW.gdn.eval tr 2 r pub = 1 from eGdn)]
  dsimp only
  rw [br_din, br_dout]
  simp only [Sem, hmode]
  rw [payOf_kid, ev_d1 hd]
  intro hch
  refine step_brKeep (n := n) hold ?_ ?_ (Or.inr (Or.inr hrk2)) hrk ?_ ?_ ?_ hom ?_ ?_ hch
  · rw [kids_at n hn, if_pos hfn1, slot_sel hn hs1 hs0]
  · rw [← hnn]; exact drop_cons_of_get hnib
  · rw [if_neg hne, if_neg hne, href, cref, cnm, com, ← hkd]
    have : brMem tr pub r - le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)) +
        le4 (((List.range 4).map fun k => Br.c "nm" k).map (E tr 2 r pub)) = brNMem tr pub r := by omega
    unfold brNew at hnew
    rw [br_val_kept hc eGn eUV eDV] at hnew
    rw [this]; exact hnew
  · rw [if_neg hne, cref, ← hkd, hcount]; omega
  · intro hv
    rw [if_neg hne, cref, ← hkd, hcount]
    have : ev tr 2 r pub (Br.c "hasv") = 0 := by
      have hb := br_bool_hasv' hc
      unfold brVal at hv
      split at hv
      · cases hv
      · omega
    have := hkeep.2 this; omega
  · rw [if_neg hne, hnm, cnm, com]; omega
  · rw [hnm]; exact brNMem_lt hR

end

end StateM5a.RowBrK
