import StateM5a.RowBrMsg

/-!
# StateM5a.RowBrF — `LocalOK` of the `BR` find rows (`oFD`, `oFA`, `oFV`)

For a decoded `BR` walk row (`brRow`, the `WRow` that `DecodeWalk.rowsOf cDc brW` produces for
row `r`): from the table's constraints, the row's old record (`OldOK σ brIn brOld`, a premise:
`VER` / SHA-256), the `NIB` / `KLEN` lookups in interface form and the depth bound, the row's
`LocalOK (Sem σ keyOf)` — via `BusWalk.step_brFind` / `step_brEmpty` / `step_brVal`.
-/

namespace StateM5a.RowBrF

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- The decoded walk row of `BR` row `r` (as `rowsOf`). -/
def brRow (tr : Trace Fp) (pub : List Fp) (r : Nat) : WRow Ref Pay Res :=
  { din := cDc.down (vals tr 2 r pub brW.di),
    dout := if brW.gdn.eval tr 2 r pub = 1 then some (cDc.down (vals tr 2 r pub brW.dd)) else none,
    uin := cDc.dr ((vals tr 2 r pub brW.ui).drop 2),
    uout := cDc.dr ((vals tr 2 r pub brW.uo).drop 2) }

theorem mem_brRows {tr : Trace Fp} {pub : List Fp} {x : WRow Ref Pay Res}
    (hx : x ∈ rowsOf cDc brW tr 2 pub) :
    ∃ r, r < tr.height 2 ∧ Br.gold.eval tr 2 r pub = 1 ∧ x = brRow tr pub r :=
  DecodeShape.mem_rowsOf hx

theorem drop_cons_of_get {K : List Nat} {d n : Nat} (h : K[d]? = some n) :
    K.drop d = n :: K.drop (d + 1) := by
  have hl : d < K.length := by
    rcases Nat.lt_or_ge d K.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [List.drop_eq_getElem_cons hl]
  rw [List.getElem?_eq_getElem hl] at h
  cases h; rfl

theorem drop_nil_of_len {K : List Nat} {d : Nat} (h : K.length = d) : K.drop d = [] := by
  subst h; simp

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

set_option maxHeartbeats 4000000 in
/-- **The selected slot** (as `FieldRows2.br_sel`, without `gdn = 1`): one selector `sel_n`, the
looked-up nibble is `n`, and `f_n = gdn`. -/
theorem br_sel' (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hA : ev tr 2 r pub (Br.c "act") = 1) (hv : ev tr 2 r pub Br.gEnd = 0) :
    ∃ i, i < 16 ∧ ev tr 2 r pub (Br.c "sel" i) = 1 ∧
      (∀ j, j < 16 → j ≠ i → ev tr 2 r pub (Br.c "sel" j) = 0) ∧
      ev tr 2 r pub (Br.c "f" i) = ev tr 2 r pub (Br.c "gdn") ∧ ev tr 2 r pub Br.nib = i := by
  have bs := FieldRows2.br_bool_sel hc
  have h1 := FieldRows2.br_hold hc (e := sumE ((List.range 16).map fun i => Br.c "sel" i) -
      (Br.c "act" - Br.gEnd)) (by
        unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
        memfind)
  have h1' := eq_of_sub h1
  rw [ev_sumE, List.map_map] at h1'
  have hs16 : ((List.range 16).map fun i => ev tr 2 r pub (Br.c "sel" i)).sum ≤ 16 := by
    have := sum_le_length ((List.range 16).map fun i => ev tr 2 r pub (Br.c "sel" i))
      (by intro x hx; simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨j, hj, rfl⟩ := hx; exact bs j hj)
    simpa using this
  have hsum : ((List.range 16).map fun i => ev tr 2 r pub (Br.c "sel" i)).sum = 1 := by
    have e : ev tr 2 r pub (Br.c "act" - Br.gEnd) = 1 := by rw [ev_sub, hA, hv]; try simp
    rw [e, Function.comp_def, Nat.mod_eq_of_lt (by omega)] at h1'
    exact h1'
  obtain ⟨i, hi, h1i, hu⟩ := FieldRows2.sum_one (fun j => ev tr 2 r pub (Br.c "sel" j)) 16 bs hsum
  refine ⟨i, hi, h1i, hu, ?_, ?_⟩
  · have h2 := FieldRows2.br_hold hc (e := sumE ((List.range 16).map fun i => Br.c "sel" i * Br.c "f" i) -
        Br.c "gdn") (by
          unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
          memfind)
    have h2' := eq_of_sub h2
    rw [ev_sumE, List.map_map] at h2'
    have hF : ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sel" i * Br.c "f" i)).sum =
        ev tr 2 r pub (Br.c "f" i) := by
      rw [FieldRows2.sum_single _ i 16 hi (fun j hj hji => by
        simp only [Function.comp, ev_hmul, hu j hj hji, Nat.zero_mul, Nat.zero_mod])]
      simp only [Function.comp, ev_hmul, h1i, Nat.one_mul]
      exact Nat.mod_eq_of_lt (ev_lt _)
    rw [hF, Nat.mod_eq_of_lt (ev_lt _)] at h2'
    exact h2'
  · unfold Br.nib
    rw [ev_sumE, List.map_map]
    have hN : ((List.range 16).map (ev tr 2 r pub ∘ fun i => sm i (Br.c "sel" i))).sum = i := by
      rw [FieldRows2.sum_single _ i 16 hi (fun j hj hji => by
        simp only [Function.comp, sm, ev_mul, ev_const, hu j hj hji, Nat.mul_zero, Nat.zero_mod])]
      simp only [Function.comp, sm, ev_mul, ev_const, h1i, Nat.mul_one]
      have hP : i < 2013265921 := Nat.lt_of_lt_of_le hi (by decide)
      rw [Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt hP]
    rw [hN]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi (by decide))

/-- The selected slot's ref is the child ref of the `DOWN` send. -/
theorem slot_sel {n : Nat} (hn : n < 16) (h1 : ev tr 2 r pub (Br.c "sel" n) = 1)
    (h0 : ∀ j, j < 16 → j ≠ n → ev tr 2 r pub (Br.c "sel" j) = 0) :
    refOf (E tr 2 r pub Br.isnSel) ((pack2 Br.chSel).map (E tr 2 r pub)) = brSlot tr pub r n := by
  have h1' := fp_of_ev1 h1
  have h0' : ∀ j, j < 16 → j ≠ n → (Br.c "sel" j).eval tr 2 r pub = 0 := fun j a b => fp_of_ev0 (h0 j a b)
  have e1 : E tr 2 r pub Br.isnSel = E tr 2 r pub (Br.c "isn" n) :=
    eval_selsum (fun i => Br.c "sel" i) (fun i => Br.c "isn" i) n hn h1' h0'
  have e2 : (pack2 Br.chSel).map (E tr 2 r pub) = (pack2 fun b => Br.ch n b).map (E tr 2 r pub) :=
    pack2_eval fun b => eval_selsum (fun i => Br.c "sel" i) (fun i => Br.ch i b) n hn h1' h0'
  rw [e1, e2]; rfl

theorem kids_at (n : Nat) (hn : n < 16) :
    (brKids tr pub r).at n = if ev tr 2 r pub (Br.c "f" n) = 1 then some (brSlot tr pub r n) else none := by
  unfold brKids; rw [kidsFrom_at _ _ 16 0 n hn]; simp

/-- The child depth: `d + 1` with no wrap. -/
theorem ev_d1 (hd : ev tr 2 r pub (Br.c "d") + 1 < P) :
    ev tr 2 r pub (Br.c "d" + 1) = ev tr 2 r pub (Br.c "d") + 1 := by
  rw [ev_hadd, ev_one, Nat.mod_eq_of_lt hd]

end

/-! ## Find ops -/

/-- Field values of composite expressions, goal only. -/
macro "evg" : tactic => `(tactic| simp only [eval_add, eval_sub, eval_mul, eval_sm, eval_K, eval_lit,
  Br.gSame, Br.gKeep, Br.gEnd, Br.vlen, Br.mode, Br.gold, limb16, RK_SAME, RK_H, RK_HB, RK_HE, RK_LD, RK_NONE])
/-- `evg` at every hypothesis too. -/
macro "evga" : tactic => `(tactic| simp only [eval_add, eval_sub, eval_mul, eval_sm, eval_K, eval_lit,
  Br.gSame, Br.gKeep, Br.gEnd, Br.vlen, Br.mode, Br.gold, limb16, RK_SAME, RK_H, RK_HB, RK_HE, RK_LD, RK_NONE] at *)

/-- A flag's field value `0` / `1`, by `omega` from the op-bundle facts in context. -/
macro "f0" : term => `(fp_of_ev0 (by omega))
macro "f1" : term => `(fp_of_ev1 (by omega))

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem payOf_mode (m : Expr) (f : Expr → Fp) :
    (payOf ((payE (fun s j => Br.c s j) m).map f)).mode = (f m).toNat := rfl
theorem payOf_kid (m : Expr) (f : Expr → Fp) :
    (payOf ((payE (fun s j => Br.c s j) m).map f)).kid = (f (Br.c "kid")).toNat := rfl

set_option maxHeartbeats 4000000 in
/-- **`BR.oFD`**: find through a branch. -/
theorem localOK_oFD {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oFD") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hd : ev tr 2 r pub (Br.c "d") + 1 < P)
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eFD : (Br.c "oFD").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 1 := f1
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 0 := f0
  have eDL : (Br.c "oDL").eval tr 2 r pub = 0 := f0
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, hs1, hs0, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn1 : ev tr 2 r pub (Br.c "f" n) = 1 := hfn.trans (eval_one_ev eGdn)
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 0 := by
    rw [payOf_mode]; show (Br.mode.eval tr 2 r pub).toNat = 0
    rw [show Br.mode.eval tr 2 r pub = 0 by evg; grind]; rfl
  unfold LocalOK
  simp only [brRow]
  rw [if_pos (show brW.gdn.eval tr 2 r pub = 1 from eGdn)]
  dsimp only
  rw [br_din, br_dout, br_uin, br_uout]
  simp only [Sem, hmode]
  rw [payOf_kid, ev_d1 hd]
  intro hch
  refine step_brFind (n := n) hold ?_ ?_ ?_ ?_ ?_ hch
  · rw [kids_at n hn, if_pos hfn1, slot_sel hn hs1 hs0]
  · rw [← hnn]; exact drop_cons_of_get hnib
  · apply ev_eq_of_eval; evg; grind
  · apply ev_eq_of_eval; evg; grind
  · show bytesOf _ = bytesOf _
    rw [map_zip_left (Br.c "oFD" + Br.c "oD1") (Br.c "oFV") (fun i => Br.c "lvh" i) _
      (by evg; grind) eFV _ (by simp [pack2]),
      map_gate (Br.c "oFD" + Br.c "oDL") (fun i => Br.c "lvh" i) (by evg; grind)]

theorem fp_zero_ne_one : (0 : Fp) ≠ 1 := by decide

theorem br_bool_hasv : bool (Br.c "hasv") ∈ Br.constraints := by
  unfold Br.constraints
  simp only [List.mem_append, List.mem_map]
  repeat apply Or.inl
  exact ⟨"hasv", by simp, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`BR.oFA`**: find miss at an empty slot. -/
theorem localOK_oFA {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oFA") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eFD : (Br.c "oFD").eval tr 2 r pub = 0 := f0
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 0 := f0
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, -, -, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn0 : ev tr 2 r pub (Br.c "f" n) = 0 := hfn.trans (ev_of_eval eGdn)
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 0 := by
    rw [payOf_mode]; show (Br.mode.eval tr 2 r pub).toNat = 0
    rw [show Br.mode.eval tr 2 r pub = 0 by evg; grind]; rfl
  unfold LocalOK
  simp only [brRow]
  rw [if_neg (show ¬ brW.gdn.eval tr 2 r pub = 1 from fun h => fp_zero_ne_one (eGdn.symm.trans h))]
  dsimp only
  rw [br_din, br_uout]
  simp only [Sem, hmode]
  rw [payOf_kid]
  refine step_brEmpty (n := n) hold ?_ ?_ ?_
  · rw [kids_at n hn, if_neg (by omega)]
  · rw [← hnn]; exact drop_cons_of_get hnib
  · exact ev_of_eval (by evg; grind)

set_option maxHeartbeats 4000000 in
/-- **`BR.oFV`**: the key ends at the branch; the answer is its value (`KLEN`). -/
theorem localOK_oFV {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oFV") = 1)
    (hklen : (keyOf (ev tr 2 r pub (Br.c "kid"))).length = ev tr 2 r pub (Br.c "d"))
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r)) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eFD : (Br.c "oFD").eval tr 2 r pub = 0 := f0
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 0 := f0
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 1 := f1
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 0 := f0
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 0 := by
    rw [payOf_mode]; show (Br.mode.eval tr 2 r pub).toNat = 0
    rw [show Br.mode.eval tr 2 r pub = 0 by evg; grind]; rfl
  unfold LocalOK
  simp only [brRow]
  rw [if_neg (show ¬ brW.gdn.eval tr 2 r pub = 1 from fun h => fp_zero_ne_one (eGdn.symm.trans h))]
  dsimp only
  rw [br_din, br_uout]
  simp only [Sem, hmode]
  rw [payOf_kid]
  refine step_brVal hold (drop_nil_of_len hklen) ?_
  have hv := bool_le (FieldRows.hold rfl hc br_bool_hasv)
  unfold brVal
  rcases (by omega : ev tr 2 r pub (Br.c "hasv") = 0 ∨ ev tr 2 r pub (Br.c "hasv") = 1) with h0 | h1'
  · have eH := fp_of_ev0 h0
    left
    refine ⟨ev_of_eval (by evg; grind), by simp [h0]⟩
  · have eH := fp_of_ev1 h1'
    right
    refine ⟨eval_one_ev (by evg; grind), ?_⟩
    rw [if_pos h1']
    congr 2
    · apply ev_eq_of_eval; evg; grind
    · rw [map_zip_right (Br.c "oFD" + Br.c "oD1") (Br.c "oFV") (fun i => Br.c "lvh" i) _
        (by evg; grind) eFV _ (by simp [pack2])]

end

end StateM5a.RowBrF
