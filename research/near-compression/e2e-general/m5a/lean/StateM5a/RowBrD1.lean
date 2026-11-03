import StateM5a.RowBrUN

/-!
# StateM5a.RowBrD1 — `LocalOK` of `BR.oD1` (squash onto the one remaining leaf sibling)

From the constraints: the deleted child is slot `n` (`sel`), the sibling slot `i` (`sr`, one-hot,
`f_i = 1`, `i ≠ n`), no other slot (`Σ f = 2`, `sum_range_ge`), no value.  The sibling's leaf is
read on `SIBQ`/`SIBA` (`hsib`: the `SibRel` of the row's request / answer cells, as
`BusSplit.sib_reqresp` gives it; responders `SN.oLS`) and its key continues with nibble `i`
(`hnib2`: the `NIB(kid2, d, sib)` lookup).  Via `BusSplit.step_brOne`.
-/

namespace StateM5a.RowBrD1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrF StateM5a.RowBrD StateM5a.RowBrN
open StateM5a.RowBrU StateM5a.RowBrK StateM5a.RowBrV StateM5a.RowBrV2 StateM5a.RowBrUN

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem perm_sum_nat {l₁ l₂ : List Nat} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- A sum over `range k` bounds the sum over any duplicate-free list of indices `< k`. -/
theorem sum_range_ge (F : Nat → Nat) : ∀ (k : Nat) (s : List Nat), s.Nodup → (∀ x ∈ s, x < k) →
    (s.map F).sum ≤ ((List.range k).map F).sum
  | 0, s, _, h => by
    cases s with
    | nil => simp
    | cons a _ => exact absurd (h a (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | k + 1, s, nd, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hk : k ∈ s
    · have hp := List.perm_cons_erase hk
      have e : (s.map F).sum = F k + ((s.erase k).map F).sum := by
        rw [perm_sum_nat (hp.map F)]; simp
      have ih := sum_range_ge F k (s.erase k) (nd.erase k) (fun x hx => by
        have := h x (List.mem_of_mem_erase hx)
        have hne : x ≠ k := fun e => by subst e; exact (List.Nodup.not_mem_erase nd) hx
        omega)
      omega
    · have ih := sum_range_ge F k s nd (fun x hx => by
        have := h x hx
        have hne : x ≠ k := fun e => by subst e; exact hk hx
        omega)
      omega

theorem limbBytes_len : ∀ l : List Nat, (Tape.limbBytes l).length = 2 * l.length
  | [] => rfl
  | _ :: l => by simp only [Tape.limbBytes, List.length_cons, limbBytes_len l]; omega

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

set_option maxHeartbeats 4000000 in
/-- **The sibling slot** of an `oD1` row: one `sr_i`, the looked-up nibble `sib = i`. -/
theorem br_sr_one (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (h1 : ev tr 2 r pub (Br.c "oD1") = 1) (h2 : ev tr 2 r pub (Br.c "oSL") = 0) :
    ∃ i, i < 16 ∧ ev tr 2 r pub (Br.c "sr" i) = 1 ∧
      (∀ j, j < 16 → j ≠ i → ev tr 2 r pub (Br.c "sr" j) = 0) ∧ ev tr 2 r pub Br.sib = i := by
  have bs : ∀ i, i < 16 → ev tr 2 r pub (Br.c "sr" i) ≤ 1 := fun i hi => by
    apply bool_le; apply FieldRows2.br_hold hc
    unfold Br.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    memfind
  have h := FieldRows2.br_hold hc (e := sumE ((List.range 16).map fun i => Br.c "sr" i) - Br.c "oD1" - Br.c "oSL")
    (by unfold Br.constraints; simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
        memfind)
  have hA := eq_of_sub h
  rw [h2] at hA
  have h' := eq_of_sub hA
  rw [h1, ev_sumE, List.map_map] at h'
  have hs16 : ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sr" i)).sum ≤ 16 := by
    have := sum_le_length ((List.range 16).map (ev tr 2 r pub ∘ fun i => Br.c "sr" i))
      (by intro x hx; simp only [List.mem_map, List.mem_range] at hx
          obtain ⟨j, hj, rfl⟩ := hx; exact bs j hj)
    simpa using this
  rw [Nat.mod_eq_of_lt (by omega), Function.comp_def] at h'
  obtain ⟨i, hi, h1i, hu⟩ := FieldRows2.sum_one (fun j => ev tr 2 r pub (Br.c "sr" j)) 16 bs h'
  refine ⟨i, hi, h1i, hu, ?_⟩
  unfold Br.sib
  rw [ev_sumE, List.map_map]
  have hN : ((List.range 16).map (ev tr 2 r pub ∘ fun i => sm i (Br.c "sr" i))).sum = i := by
    rw [FieldRows2.sum_single _ i 16 hi (fun j hj hji => by
      simp only [Function.comp, sm, ev_mul, ev_const, hu j hj hji, Nat.mul_zero, Nat.zero_mod])]
    simp only [Function.comp, sm, ev_mul, ev_const, h1i, Nat.mul_one]
    have hP : i < 2013265921 := Nat.lt_of_lt_of_le hi (by decide)
    rw [Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt hP]
  rw [hN]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hi (by decide))

/-- The sibling's ref is the `SIBQ` request ref. -/
theorem slot_sib {i : Nat} (hi : i < 16) (h1 : ev tr 2 r pub (Br.c "sr" i) = 1)
    (h0 : ∀ j, j < 16 → j ≠ i → ev tr 2 r pub (Br.c "sr" j) = 0) :
    refOf (E tr 2 r pub Br.isnSib) ((pack2 Br.chSib).map (E tr 2 r pub)) = brSlot tr pub r i := by
  have h1' := fp_of_ev1 h1
  have h0' : ∀ j, j < 16 → j ≠ i → (Br.c "sr" j).eval tr 2 r pub = 0 := fun j a b => fp_of_ev0 (h0 j a b)
  have e1 : E tr 2 r pub Br.isnSib = E tr 2 r pub (Br.c "isn" i) :=
    eval_selsum (fun i => Br.c "sr" i) (fun i => Br.c "isn" i) i hi h1' h0'
  have e2 : (pack2 Br.chSib).map (E tr 2 r pub) = (pack2 fun b => Br.ch i b).map (E tr 2 r pub) :=
    pack2_eval fun b => eval_selsum (fun i => Br.c "sr" i) (fun i => Br.ch i b) i hi h1' h0'
  rw [e1, e2]; rfl

set_option maxHeartbeats 4000000 in
theorem br_mem_srf (i : Nat) (hi : i < 16) :
    Br.c "sr" i * (1 - Br.c "f" i - Br.c "oSL") ∈ Br.constraints := by brmem2
set_option maxHeartbeats 4000000 in
theorem br_mem_srsel (i : Nat) (hi : i < 16) : Br.c "sr" i * Br.c "sel" i ∈ Br.constraints := by brmem2
theorem br_mem_d1nk : Br.c "oD1" * (Br.nk - 2) ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem br_mem_d1v : Br.c "oD1" * Br.c "hasv" ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem br_mem_d1rk : Br.c "oD1" * (Br.c "rk" - K RK_NONE) ∈ Br.constraints := by
  unfold Br.constraints; simp only [List.mem_append, List.mem_cons]; simp

set_option maxHeartbeats 8000000 in
/-- **`BR.oD1`**: delete below a branch without a value whose child vanished and whose only other
child is a leaf: the result is that leaf's descriptor. -/
theorem localOK_oD1 {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Br.table.constraints, e.eval tr 2 r pub = 0)
    (hg : ev tr 2 r pub Br.gold = 1) (h1 : ev tr 2 r pub (Br.c "oD1") = 1)
    (hnib : (keyOf (ev tr 2 r pub (Br.c "kid")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.nib))
    (hnib2 : (keyOf (ev tr 2 r pub (Br.c "kid2")))[ev tr 2 r pub (Br.c "d")]? = some (ev tr 2 r pub Br.sib))
    (hd : ev tr 2 r pub (Br.c "d") + 1 < P)
    (hold : OldOK σ (brIn tr pub r) (brOld tr pub r))
    (hsib : SibRel σ keyOf (ev tr 2 r pub (Br.c "d") + 1)
      (refOf (E tr 2 r pub Br.isnSib) ((pack2 Br.chSib).map (E tr 2 r pub)))
      (ev tr 2 r pub (Br.c "kid2")) (ev tr 2 r pub (Br.c "lvlen"))
      (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub))))
    (hkey : (∀ y ∈ keyOf (ev tr 2 r pub (Br.c "kid2")), y < 16) ∧
      (keyOf (ev tr 2 r pub (Br.c "kid2"))).length ≤ 2 ^ 21) :
    LocalOK (Sem σ keyOf) (brRow tr pub r) := by
  brfacts hc hg
  have eAct : (Br.c "act").eval tr 2 r pub = 1 := f1
  have eGdn : (Br.c "gdn").eval tr 2 r pub = 1 := f1
  have eGn : (Br.c "gnew").eval tr 2 r pub = 0 := f0
  have eU : (Br.c "mU").eval tr 2 r pub = 0 := f0
  have eD : (Br.c "mD").eval tr 2 r pub = 1 := f1
  have eD1 : (Br.c "oD1").eval tr 2 r pub = 1 := f1
  have eSL : (Br.c "oSL").eval tr 2 r pub = 0 := f0
  have eFD : (Br.c "oFD").eval tr 2 r pub = 0 := f0
  have eFV : (Br.c "oFV").eval tr 2 r pub = 0 := f0
  have eUV : (Br.c "oUV").eval tr 2 r pub = 0 := f0
  have eDV : (Br.c "oDV").eval tr 2 r pub = 0 := f0
  have eDZ : (Br.c "oDZ").eval tr 2 r pub = 0 := f0
  have eDS : (Br.c "oDS").eval tr 2 r pub = 0 := f0
  have eDA : (Br.c "oDA").eval tr 2 r pub = 0 := f0
  have eUD : (Br.c "oUD").eval tr 2 r pub = 0 := f0
  have eUN : (Br.c "oUN").eval tr 2 r pub = 0 := f0
  have eDH : (Br.c "oDH").eval tr 2 r pub = 0 := f0
  have eDL : (Br.c "oDL").eval tr 2 r pub = 0 := f0
  have eDN : (Br.c "oDN").eval tr 2 r pub = 0 := f0
  have hA : ev tr 2 r pub (Br.c "act") = 1 := eval_one_ev eAct
  have hE : ev tr 2 r pub Br.gEnd = 0 := ev_of_eval (by evg; grind)
  obtain ⟨n, hn, hs1, hs0, hfn, hnn⟩ := br_sel' hc hA hE
  have hfn1 : ev tr 2 r pub (Br.c "f" n) = 1 := hfn.trans (eval_one_ev eGdn)
  obtain ⟨i, hi, hr1, hr0, hsibi⟩ := br_sr_one hc h1 (ev_of_eval eSL)
  have hfi : ev tr 2 r pub (Br.c "f" i) = 1 := by
    have e := fp_of_ev0 (FieldRows.hold rfl hc (br_mem_srf i hi))
    have := fp_of_ev1 hr1
    simp only [eval_mul, eval_sub, eval_lit] at e; rw [this, eSL] at e
    exact eval_one_ev (by grind)
  have hni : n ≠ i := by
    intro e; subst e
    have := FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_srsel n hn)) hr1
    omega
  -- exactly two slots
  have bf := FieldRows2.br_bool_f hc (tr := tr) (pub := pub) (r := r)
  have hnk : ev tr 2 r pub Br.nk = 2 := by
    have := FieldVer.eq_of_gate (FieldRows.hold rfl hc br_mem_d1nk) h1
    rw [this]; rfl
  have hsum : ((List.range 16).map fun j => ev tr 2 r pub (Br.c "f" j)).sum = 2 := by
    have hS : ((List.range 16).map fun j => ev tr 2 r pub (Br.c "f" j)).sum ≤ 16 := by
      have := sum_le_length ((List.range 16).map fun j => ev tr 2 r pub (Br.c "f" j))
        (by intro x hx; simp only [List.mem_map, List.mem_range] at hx; obtain ⟨j, hj, rfl⟩ := hx; exact bf j hj)
      simpa using this
    unfold Br.nk at hnk; rw [ev_sumE, List.map_map, Function.comp_def,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hS (by decide))] at hnk
    exact hnk
  have hoth : ∀ j, j ≠ n → j ≠ i → (brKids tr pub r).at j = none := by
    intro j hjn hji
    rcases Nat.lt_or_ge j 16 with hj | hj
    · rw [kids_at j hj, if_neg]
      intro hfj
      have := sum_range_ge (fun j => ev tr 2 r pub (Br.c "f" j)) 16 [n, i, j]
        (by simp [hni, Ne.symm hjn, Ne.symm hji]) (by intro x hx; simp at hx; omega)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
      omega
    · unfold brKids
      rw [show (16 : Nat) = 16 from rfl]
      have : ∀ k i' m, k ≤ m → (kidsFrom (fun i => ev tr 2 r pub (Br.c "f" i)) (brSlot tr pub r) i' k).at m = none := by
        intro k
        induction k with
        | zero => intro i' m _; rfl
        | succ k ih =>
          intro i' m hm
          simp only [RowBr.kidsFrom]
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          split <;> exact ih _ _ (by omega)
      exact this 16 0 j hj
  have hv0 : ev tr 2 r pub (Br.c "hasv") = 0 := FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_d1v) h1
  have hval : brVal tr pub r = none := by unfold brVal; rw [if_neg (by omega)]
  have hmode : (payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))).mode = 2 := by
    rw [payOf_mode]; exact ev_eq_nat (by evg; grind) (by decide)
  have hres := br_uout (tr := tr) (pub := pub) (r := r)
  have hrk : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).rk = RK_LD := by
    rw [hres]; exact ev_eq_nat (by evga; grind) (by decide)
  have hom : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).om = brMem tr pub r := by
    rw [hres]; show le4 _ = le4 _; rw [map_gate' _ _ (by evg; grind)]
  have hk2 : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).kid2 = ev tr 2 r pub (Br.c "kid2") := by
    rw [hres]; exact ev_eq_of_eval (by evg; grind)
  have hst : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).st2 = ev tr 2 r pub (Br.c "d") := by
    rw [hres]; exact ev_eq_of_eval (by evg; grind)
  have hal : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).alen = ev tr 2 r pub (Br.c "lvlen") := by
    rw [hres]; exact ev_eq_of_eval (by evg; grind)
  have hah : (cDc.dr ((vals tr 2 r pub brW.uo).drop 2)).avh =
      bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub)) := by
    rw [hres]; show bytesOf _ = bytesOf _
    rw [map_zip_left (Br.c "oFD" + Br.c "oD1") (Br.c "oFV") (fun i => Br.c "lvh" i) _
      (by evg; grind) eFV _ (by simp [pack2]), List.map_map]; rfl
  have hrkc : (cDc.dr ((vals tr 2 r pub brW.ui).drop 2)).rk = RK_NONE := by
    rw [br_uin]; show ev tr 2 r pub (Br.c "rk") = RK_NONE
    rw [FieldVer.eq_of_gate (FieldRows.hold rfl hc br_mem_d1rk) h1]; rfl
  unfold LocalOK
  simp only [brRow]
  rw [if_pos (show brW.gdn.eval tr 2 r pub = 1 from eGdn)]
  dsimp only
  rw [br_din, br_dout]
  simp only [Sem, hmode]
  rw [payOf_kid, ev_d1 hd]
  intro hch
  unfold brOld at hold
  rw [hval] at hold
  rw [slot_sib hi hr1 hr0] at hsib
  refine step_brOne (n := n) (i := i) hold ?_ ?_ hni hoth ?_ hrkc hrk hsib ?_ hk2 hst hal hah hom ?_ hch
  · rw [kids_at n hn, if_pos hfn1, slot_sel hn hs1 hs0]
  · rw [kids_at i hi, if_pos hfi]
  · rw [← hnn]; exact drop_cons_of_get hnib
  · rw [← hsibi]; exact drop_cons_of_get hnib2
  · -- the descriptor's leaf is well-formed
    have hp := hexPrefix_len ((keyOf (ev tr 2 r pub (Br.c "kid2"))).drop (ev tr 2 r pub (Br.c "d"))) true
    have hdl : ((keyOf (ev tr 2 r pub (Br.c "kid2"))).drop (ev tr 2 r pub (Br.c "d"))).length ≤ 2 ^ 21 := by
      rw [List.length_drop]; exact Nat.le_trans (Nat.sub_le _ _) hkey.2
    have hlen := ev_lt (tr := tr) (t := 2) (r := r) (pub := pub) (Br.c "lvlen")
    have hb : (bytesOf (((List.range 16).map fun i => Br.c "lvh" i).map (E tr 2 r pub))).length = 32 := by
      unfold bytesOf; rw [limbBytes_len]; simp
    simp only [PTrie.wf, nibblesOk, slotOk, leafMem, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, beq_iff_eq]
    refine ⟨⟨⟨fun y hy => hkey.1 y (List.mem_of_mem_drop hy), by omega, hb⟩, ?_⟩, by omega⟩
    first | omega | exact decide_eq_true (by omega)

end

end StateM5a.RowBrD1
