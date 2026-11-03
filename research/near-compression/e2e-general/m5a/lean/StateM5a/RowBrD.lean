import StateM5a.RowBrF

/-!
# StateM5a.RowBrD — `LocalOK` of the `BR` delete rows with an unchanged result (`oDA`, `oDS`, `oDZ`)

`SAME` results: the row's `UP` repeats its own input ref (`gSame = 1`) and old memory; via
`BusWalk.step_brAbs` / `step_brSame` / `step_brValAbs`.  Premises as in `RowBrF`.
-/

namespace StateM5a.RowBrD

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

/-- A gated pair list `g·p + h·q` with `g = 0`, `h = 1` evaluates to the `q` list. -/
theorem map_zip_snd (g h : Expr) (hg : g.eval tr 2 r pub = 0) (hh : h.eval tr 2 r pub = 1) :
    ∀ (A y : List Expr), A.length = y.length →
      ((A.zip y).map (fun (p, q) => g * p + h * q)).map (E tr 2 r pub) = y.map (E tr 2 r pub)
  | [], y, hl => by cases y <;> simp_all
  | a :: A, [], hl => by simp at hl
  | a :: A, b :: y, hl => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    refine ⟨?_, map_zip_snd g h hg hh A y (by simpa using hl)⟩
    simp only [E, eval_add, eval_mul, hg, hh]; grind

/-- A gated pair list `g·p + h·q` with `g = 1`, `h = 0` evaluates to the `p` list. -/
theorem map_zip_fst (g h : Expr) (hg : g.eval tr 2 r pub = 1) (hh : h.eval tr 2 r pub = 0) :
    ∀ (A y : List Expr), A.length = y.length →
      ((A.zip y).map (fun (p, q) => g * p + h * q)).map (E tr 2 r pub) = A.map (E tr 2 r pub)
  | [], y, hl => by cases y <;> simp_all
  | a :: A, [], hl => by simp at hl
  | a :: A, b :: y, hl => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    refine ⟨?_, map_zip_fst g h hg hh A y (by simpa using hl)⟩
    simp only [E, eval_add, eval_mul, hg, hh]; grind

theorem ev_eq_nat {e : Expr} {n : Nat} (h : e.eval tr 2 r pub = (n : Fp)) (hn : n < P) :
    ev tr 2 r pub e = n := by
  unfold ev; rw [h]
  show (Fp.ofNat n).toNat = n
  rw [Fp.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

theorem br_mem_dsrk : Br.c "oDS" * (Br.c "rk" - K RK_SAME) ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem br_mem_dzv : Br.c "oDZ" * Br.c "hasv" ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp

/-- The `SAME` result: kind, ref and old memory of the row's `UP` send. -/
theorem same_up (eS : Br.gSame.eval tr 2 r pub = 1) (eN : (Br.c "gnew").eval tr 2 r pub = 0)
    (eK : (Br.c "oUD" + Br.c "oUN" + Br.c "oUV" + sm 2 (Br.gKeep + Br.c "oDV") + sm 4 (Br.c "oD1")).eval tr 2 r pub = 0)
    (eM : (Br.c "mU" + Br.c "mD").eval tr 2 r pub = 1) :
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).rk = RK_SAME ∧
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).ref = brIn tr pub r ∧
    (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).om = brMem tr pub r := by
  rw [br_uout]
  refine ⟨ev_eq_nat (by evga; grind) (by decide), ?_, ?_⟩
  · show refOf _ _ = refOf _ _
    rw [map_zip_snd _ _ eN eS _ _ (by simp [pack2])]
    congr 1; evga; grind
  · show le4 _ = le4 _
    rw [map_gate' _ _ eM]

set_option maxHeartbeats 4000000 in
/-- **`BR.oDA`**: absent delete at an empty slot. -/
theorem localOK_oDA {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oDA") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 0 := f0
  have eGn : (Br.c "gnew").eval tr 2 r pub = 0 := f0
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 1 := f1
  have eDA : (Br.c "oDA").eval tr 2 r pub = 1 := f1
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eUD : (Br.c "oUD").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 0 := f0
  have eDH : (Br.c "oDH").eval tr 2 r pub = 0 := f0
  have eDL : (Br.c "oDL").eval tr 2 r pub = 0 := f0
  have eDN : (Br.c "oDN").eval tr 2 r pub = 0 := f0
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 0 := f0
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, -, -, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn0 : ev tr 2 r pub (Br.c "f" n) = 0 := hfn.trans (ev_of_eval eGdn)
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 2 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  obtain ⟨hrk, href, hom⟩ := same_up (tr := tr) (pub := pub) (r := r) (by evg; grind) eGn
    (by evg; grind) (by evg; grind)
  unfold LocalOK
  simp only [brRow]
  rw [if_neg (show ¬ brW.gdn.eval tr 2 r pub = 1 from fun h => fp_zero_ne_one (eGdn.symm.trans h))]
  dsimp only
  rw [br_din]
  simp only [Sem, hmode]
  rw [payOf_kid]
  refine step_brAbs (n := n) hold ?_ ?_ hrk href hom
  · rw [kids_at n hn, if_neg (by omega)]
  · rw [← hnn]; exact drop_cons_of_get hnib

set_option maxHeartbeats 4000000 in
/-- **`BR.oDS`**: delete below a branch whose child is unchanged. -/
theorem localOK_oDS {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oDS") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hd : ev tr 2 r pub (Br.c "d") + 1 < P)
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 1 := f1
  have eGn : (Br.c "gnew").eval tr 2 r pub = 0 := f0
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 1 := f1
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 1 := f1
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eUD : (Br.c "oUD").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 0 := f0
  have eDH : (Br.c "oDH").eval tr 2 r pub = 0 := f0
  have eDL : (Br.c "oDL").eval tr 2 r pub = 0 := f0
  have eDN : (Br.c "oDN").eval tr 2 r pub = 0 := f0
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 0 := f0
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, hs1, hs0, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn1 : ev tr 2 r pub (Br.c "f" n) = 1 := hfn.trans (eval_one_ev eGdn)
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 2 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  have hrkc : ev tr 2 r pub (Br.c "rk") = RK_SAME := by
    rw [FieldVer.eq_of_gate (FieldRows.hold rfl hc br_mem_dsrk) h1]; rfl
  obtain ⟨hrk, href, hom⟩ := same_up (tr := tr) (pub := pub) (r := r) (by evg; grind) eGn
    (by evg; grind) (by evg; grind)
  unfold LocalOK
  simp only [brRow]
  rw [if_pos (show brW.gdn.eval tr 2 r pub = 1 from eGdn)]
  dsimp only
  rw [br_din, br_dout]
  simp only [Sem, hmode]
  rw [payOf_kid, ev_d1 hd]
  intro hch
  rw [br_uin] at hch
  refine step_brSame (n := n) hold ?_ ?_ hrkc hrk href hom hch
  · rw [kids_at n hn, if_pos hfn1, slot_sel hn hs1 hs0]
  · rw [← hnn]; exact drop_cons_of_get hnib

set_option maxHeartbeats 4000000 in
/-- **`BR.oDZ`**: absent value delete (the key ends at a branch without a value). -/
theorem localOK_oDZ {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oDZ") = 1)
    (hklen : (keyOf (ev tr 2 r pub (Br.c "kid"))).length = ev tr 2 r pub (Br.c "d"))
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 0 := f0
  have eGn : (Br.c "gnew").eval tr 2 r pub = 0 := f0
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 1 := f1
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 1 := f1
  have eUD : (Br.c "oUD").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDH : (Br.c "oDH").eval tr 2 r pub = 0 := f0
  have eDL : (Br.c "oDL").eval tr 2 r pub = 0 := f0
  have eDN : (Br.c "oDN").eval tr 2 r pub = 0 := f0
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 0 := f0
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 2 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  have hv0 : ev tr 2 r pub (Br.c "hasv") = 0 := FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_dzv) h1
  have hval : brVal tr pub r = none := by unfold brVal; rw [if_neg (by omega)]
  obtain ⟨hrk, href, hom⟩ := same_up (tr := tr) (pub := pub) (r := r) (by evg; grind) eGn
    (by evg; grind) (by evg; grind)
  unfold LocalOK
  simp only [brRow]
  rw [if_neg (show ¬ brW.gdn.eval tr 2 r pub = 1 from fun h => fp_zero_ne_one (eGdn.symm.trans h))]
  dsimp only
  rw [br_din]
  simp only [Sem, hmode]
  rw [payOf_kid]
  unfold brOld at hold
  rw [hval] at hold
  exact step_brValAbs hold (drop_nil_of_len hklen) hrk href hom

end

end StateM5a.RowBrD
