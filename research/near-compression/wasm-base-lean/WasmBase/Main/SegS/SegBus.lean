import WasmBase.Main.SegBus
import WasmBase.Main.SegS.SegSound
/-!
# WasmBase.Main.SegS.SegBus — `SegBus`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegBus.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- The HOST constraints hold on table 22 of a segment trace (HOST + gas register extends them). -/
theorem seg_host_conS {r : Nat} (hr : r < tr.height 22) :
    ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 := by
  intro e he
  have h := table_constrXS H (t := 22) (by simp [seg_air_len]) hr e
  rw [seg_t22] at h
  exact h (HostG.constraints_prefix.subset (HostR.constraints_prefix.subset he))

/-- **Every STATE/CH occurrence of a segment trace has count ≤ 1** (both directions). -/
theorem seg_occ_bitsS :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, (o.1 = busState ∨ o.1 = busStk) → o.2.2.2 ≤ 1 := by
  intro o ho hk
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hk ⊢
  by_cases hc : 1 ≤ t ∧ t ≤ 13
  · have : SegT t := ⟨by omega⟩
    have hT := seg_chipT nloc ngl t hc.1 hc.2
    have hcon := table_constr_eqXS H ht (chipT t) hT hr
    rw [hT] at hi
    obtain ⟨h1, h13⟩ := hc
    rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 ∨ t = 12 ∨ t = 13 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact add_counts_of hcon i hi
    · exact bit_counts_of hcon i hi
    · exact mul_counts_of hcon i hi
    · exact shift_counts_of hcon i hi
    · exact cmp_counts_of hcon i hi
    · exact const_counts_of hcon i hi
    · exact stack_counts_of hcon i hi
    · exact ctrl_counts_of hcon i hi
    · exact local_counts_of hcon i hi
    · exact div_counts_of hcon i hi
    · exact load_counts_of hcon i hi
    · exact store_counts_of hcon i hi
    · exact call_counts_of hcon i hi
  by_cases h14 : t = 14
  · subst h14
    have hcon : ∀ e ∈ Ret.table.constraints, e.eval (Local.natRow (rowNat tr 14 r) (tr.row pub 14 r)) = 0 :=
      table_constr_eqXS H ht RetT.table (seg_t14' nloc ngl) hr
    rw [seg_t14'] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ret_counts_of hcon i hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi; rcases hk with h | h <;> exact absurd h (by decide)
  by_cases h19 : t = 19
  · subst h19
    rw [seg_t19] at hi
    have hc := List.all_eq_true.mp memb_sc_shape i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · rcases hk with h | h
      · exact absurd h hc.1
      · exact absurd h hc.2
    · rw [hc]; exact (memb_kD_leS H hr).1
  by_cases h22 : t = 22
  · subst h22
    rw [seg_t22] at hi
    have hcon := seg_host_conS H hr
    change i ∈ HostG.inters at hi
    rw [hostG_inters_eq] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact host_inter_bound_of hcon i hi hk
    rcases List.mem_append.mp hi with hi | hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi; rcases hk with h | h <;> exact absurd h (by decide)
    have hc := List.all_eq_true.mp hostGExtra_sc i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · rcases hk with h | h
      · exact absurd h hc.1
      · exact absurd h hc.2
    · rw [hc]
      exact host_inter_bound_of hcon _ (List.mem_cons_self) (Or.inl rfl)
  · have hok := seg_scbits nloc ngl t ht (by omega) h19 h22
    have hc := List.all_eq_true.mp hok i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · rcases hk with h | h
      · exact absurd h hc.1
      · exact absurd h hc.2
    · by_cases h20 : t = 20
      · subst h20
        rcases hk with h | h <;> exact absurd h (seg_t20_noBus nloc ngl (by decide) hi)
      have : SegT t := ⟨h20⟩
      rcases bitS_soundS H ht hr _ hc with h | h <;> rw [h] <;> decide

/-- **The STATE and CH buses of a segment trace are permutations.** -/
theorem seg_msgs_permS (b : Nat) (hb : b = busState ∨ b = busStk) :
    (msgs (wasmBaseSegAir nloc ngl) tr pub b true).Perm (msgs (wasmBaseSegAir nloc ngl) tr pub b false) :=
  msgs_permXS H b (by rcases hb with rfl | rfl <;> decide)
    (fun o ho hk => seg_occ_bitsS H o ho (by rw [hk]; exact hb))

theorem seg_h0S : 1 ≤ tr.height 0 := by
  have := H.heightPos 0 (by simp [seg_air_len]); omega

/-- **The STATE bus of a segment trace.** -/
theorem seg_msgs_stateS :
    msgs (wasmBaseSegAir nloc ngl) tr pub busState true =
      segM0 tr pub :: (actListM2 tr pub).map (rowOutM tr pub) ∧
    msgs (wasmBaseSegAir nloc ngl) tr pub busState false =
      segMF tr pub :: (actListM2 tr pub).map (rowInM tr pub) := by
  have h0 := seg_h0S H
  have hAH_out : (actListHost tr pub).map (rowOutM tr pub) = (actListHost tr pub).map (rowOutH tr pub) :=
    List.map_congr_left fun ρ hρ => (actListHost_M_eq hρ).2.1
  have hAH_in : (actListHost tr pub).map (rowInM tr pub) = (actListHost tr pub).map (rowInH tr pub) :=
    List.map_congr_left fun ρ hρ => (actListHost_M_eq hρ).1
  obtain ⟨n15, n16, n17, n18, n19, n20, n21, n23, n24, n25, n27, n30, n31⟩ := seg_state_nil tr pub true
  obtain ⟨f15, f16, f17, f18, f19, f20, f21, f23, f24, f25, f27, f30, f31⟩ := seg_state_nil tr pub false
  have r14 : ∀ s, part RetT.table tr pub 14 busState s = part (chipT 14) tr pub 14 busState s :=
    fun s => part_congr_filter (retT_filter busState s (by decide))
  have h22 : ∀ s, part HostG.table tr pub 22 busState s = part Host.table tr pub 22 busState s :=
    fun s => part_congr_filter (hostG_filter_state s)
  constructor
  · rw [seg_msgs_air, (segb_state_parts tr pub h0).1, r14, h22, n15, n16, n17, n18, n19, n20, n21, n23, n24,
      n25, n27, n30, n31, host_part_state_T, ← hostActRows_rowOut, shape_part_true ifc_shape,
      shape_part_true conv_shape, shape_part_true unreach_shape]
    simp only [part, chip_part_true 1 (by omega) (by omega), chip_part_true 2 (by omega) (by omega),
      chip_part_true 3 (by omega) (by omega), chip_part_true 4 (by omega) (by omega),
      chip_part_true 5 (by omega) (by omega), chip_part_true 6 (by omega) (by omega),
      chip_part_true 7 (by omega) (by omega), chip_part_true 8 (by omega) (by omega),
      chip_part_true 9 (by omega) (by omega), chip_part_true 10 (by omega) (by omega),
      chip_part_true 11 (by omega) (by omega), chip_part_true 12 (by omega) (by omega),
      chip_part_true 13 (by omega) (by omega), chip_part_true 14 (by omega) (by omega)]
    unfold actListM2
    rw [List.map_append, hAH_out, actListHost_map_out, actList_map]
    have ht := tail_map tr pub (fun T t r => rowOut T tr pub t r)
    rw [show (tailActRows tr pub).map (rowOutM tr pub) =
      (tailActRows tr pub).map (fun ρ => rowOut (chipTM2 ρ.1) tr pub ρ.1 ρ.2) from rfl, ht]
    simp only [List.cons_append, List.nil_append, List.append_nil, List.append_assoc, actRows]
  · rw [seg_msgs_air, (segb_state_parts tr pub h0).2, r14, h22, f15, f16, f17, f18, f19, f20, f21, f23, f24,
      f25, f27, f30, f31, host_part_state_F, ← hostActRows_rowIn, shape_part_false ifc_shape,
      shape_part_false conv_shape, shape_part_false unreach_shape]
    simp only [part, chip_part_false 1 (by omega) (by omega), chip_part_false 2 (by omega) (by omega),
      chip_part_false 3 (by omega) (by omega), chip_part_false 4 (by omega) (by omega),
      chip_part_false 5 (by omega) (by omega), chip_part_false 6 (by omega) (by omega),
      chip_part_false 7 (by omega) (by omega), chip_part_false 8 (by omega) (by omega),
      chip_part_false 9 (by omega) (by omega), chip_part_false 10 (by omega) (by omega),
      chip_part_false 11 (by omega) (by omega), chip_part_false 12 (by omega) (by omega),
      chip_part_false 13 (by omega) (by omega), chip_part_false 14 (by omega) (by omega)]
    unfold actListM2
    rw [List.map_append, hAH_in, actListHost_map_in, actList_map]
    have ht := tail_map tr pub (fun T t r => rowIn T tr pub t r)
    rw [show (tailActRows tr pub).map (rowInM tr pub) =
      (tailActRows tr pub).map (fun ρ => rowIn (chipTM2 ρ.1) tr pub ρ.1 ρ.2) from rfl, ht]
    simp only [List.cons_append, List.nil_append, List.append_nil, List.append_assoc, actRows]

/-- **`hst` for the segment AIR, from `HoldsX`.** -/
theorem seg_hstS :
    (segM0 tr pub :: (actListM2 tr pub).map (rowOutM tr pub)).Perm
      (segMF tr pub :: (actListM2 tr pub).map (rowInM tr pub)) := by
  obtain ⟨e1, e2⟩ := seg_msgs_stateS H
  rw [← e1, ← e2]
  exact seg_msgs_permS H busState (Or.inl rfl)

end

theorem seg_base_holdsCS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr) :
    HoldsC (wasmBaseAir nloc ngl) pub (segBase tr) := by
  refine ⟨fun t ht r hr e he => ?_⟩
  have h22 : t < 22 := by rwa [air_len] at ht
  by_cases hg : baseGone t
  · simp [segBase, hg] at hr
  · rw [segBase_height hg] at hr
    rw [segBase_row hg]
    rw [seg_base_constraints nloc ngl t h22 hg] at he
    have : SegT t := ⟨by unfold baseGone at hg; omega⟩
    exact H.constr t _ r hr e he

/-- An inactive instruction-chip row of a segment trace emits nothing (`ChipFacts.inactive` through
`segBase`). -/
theorem seg_chip_inactiveS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (X : Ctx) (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) (r : Nat) (hr : r < tr.height t)
    (hna : ¬ rowAct (chipT t) tr pub t r) (b : Nat) (s : Bool) : rowMsgs (chipT t) tr pub t r b s = [] := by
  have hg : ¬ baseGone t := by unfold baseGone; omega
  have CF := chipFactsC X (seg_base_holdsCS H)
  rw [← segBase_rowMsgs hg]
  exact chip_ch_inactive CF t h1 h9 r (by rw [segBase_height hg]; exact hr)
    (by rw [segBase_rowAct hg]; exact hna) b s

theorem seg_chip_part_chS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (X : Ctx) (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) (s : Bool) :
    ((List.range (tr.height t)).flatMap fun r => rowMsgs (chipT t) tr pub t r busStk s) =
      (actRows tr pub t).flatMap fun r => rowMsgs (chipT t) tr pub t r busStk s := by
  rw [actRows, ← flatMap_filter_of_nil]
  intro r hr hna
  exact seg_chip_inactiveS H X t h1 h9 r (List.mem_range.mp hr) hna busStk s

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- `HostTraceOK` for a segment trace. -/
theorem seg_host_trace_okS : HostTraceOK tr pub := by
  intro r hr hneg
  have hcon := seg_host_conS H hr
  have hbA := hcon Host.cAct host_cAct_mem
  have hgR := hcon Host.cActNres host_cActNres_mem
  simp only [Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_col,
    Expr.eval_ofNat', natRow, Host.act, Host.nres, Host.cAct, Host.cActNres] at hbA hgR
  have hactNe : rowNat tr 22 r Host.act ≠ 1 := by
    intro hv
    exact hneg (by
      simp only [rowAct, Host.table, Host.inters, stateIn, List.cons_append, List.getD_cons_zero,
        Chips.v, Expr.eval_col, Trace.row, rowNat]
      exact hv)
  have hact0 : rowNat tr 22 r Host.act = 0 := by
    have hb := bool_nat (rowNat_lt tr 22 r Host.act) hbA
    rcases hb with h | h
    · exact h
    · exact absurd h hactNe
  have hactIdx : rowNat tr 22 r 5 = 0 := by simpa [Host.act] using hact0
  have hone : ((1 : Nat) : F) - (rowNat tr 22 r 5 : F) = 1 := by rw [hactIdx]; rfl
  have hnrF : (rowNat tr 22 r Host.nres : F) = 0 := by
    rw [hone, Lean.Grind.Semiring.one_mul] at hgR; exact hgR
  have hnr : rowNat tr 22 r Host.nres = 0 :=
    (cast_inj_iff (rowNat_lt tr 22 r Host.nres) (by decide : (0 : Nat) < P)).mp hnrF
  refine ⟨fun j hj => ?_, hnr⟩
  have h := hcon (Host.cActPf j) (host_cActPf_mem j hj)
  simp only [Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', natRow,
    Host.act, Host.cActPf] at h
  rw [hone, Lean.Grind.Semiring.one_mul] at h
  exact (cast_inj_iff (rowNat_lt tr 22 r (Host.pf j)) (by decide : (0 : Nat) < P)).mp h

/-- The HOST block of the CH bus, produced side: HOST's sends and the gas-register sends of the
active HOST rows. -/
theorem seg_host_ch_sendS :
    ((part HostG.table tr pub 22 busStk true).map decMsg).Perm
      ((hostActRows tr pub).flatMap (rowProdH tr pub) ++ (hostActRows tr pub).flatMap (fun ρ => gasProdOf tr pub ρ.2)) := by
  unfold part
  rw [List.map_flatMap]
  simp only [hostG_rowMsgs_stk, List.map_append]
  refine (perm_flatMap_append _ _ _).trans (List.Perm.of_eq ?_)
  congr 1
  · rw [show (hostActRows tr pub).flatMap (rowProdH tr pub) =
        (hostActRows tr pub).flatMap (fun ρ => rowProd Host.table tr pub 22 ρ.2) from
      flatMap_congr_on _ _ _ (fun ρ hρ => by
        obtain ⟨t, r⟩ := ρ
        obtain rfl : t = 22 := hostActRows_eq_host hρ
        exact rowProdH_host tr pub r)]
    rw [hostActRows_flatMap]
    refine flatMap_congr_on _ _ _ (fun r hr => ?_)
    by_cases ha : rowAct Host.table tr pub 22 r
    · rw [if_pos ha]; rfl
    · rw [if_neg ha]
      exact host_row_prod_inactive (pub := pub) (seg_host_trace_okS H r (List.mem_range.mp hr) ha).2
  · rw [hostActRows_flatMap]
    refine flatMap_congr_on _ _ _ (fun r hr => ?_)
    by_cases ha : rowAct Host.table tr pub 22 r
    · rw [if_pos ha]; rfl
    · rw [if_neg ha]; show (rowMsgs GasT tr pub 22 r busStk true).map decMsg = []; rw [gas_inactive_nil ha]; rfl

/-- The HOST block of the CH bus, consumed side. -/
theorem seg_host_ch_recvS :
    ((part HostG.table tr pub 22 busStk false).map decMsg).Perm
      ((hostActRows tr pub).flatMap (rowConsH tr pub) ++ (hostActRows tr pub).flatMap (fun ρ => gasConsOf tr pub ρ.2)) := by
  unfold part
  rw [List.map_flatMap]
  simp only [hostG_rowMsgs_stk, List.map_append]
  refine (perm_flatMap_append _ _ _).trans (List.Perm.of_eq ?_)
  congr 1
  · rw [show (hostActRows tr pub).flatMap (rowConsH tr pub) =
        (hostActRows tr pub).flatMap (fun ρ => rowCons Host.table tr pub 22 ρ.2) from
      flatMap_congr_on _ _ _ (fun ρ hρ => by
        obtain ⟨t, r⟩ := ρ
        obtain rfl : t = 22 := hostActRows_eq_host hρ
        exact rowConsH_host tr pub r)]
    rw [hostActRows_flatMap]
    refine flatMap_congr_on _ _ _ (fun r hr => ?_)
    by_cases ha : rowAct Host.table tr pub 22 r
    · rw [if_pos ha]; rfl
    · rw [if_neg ha]
      obtain ⟨h0, _⟩ := seg_host_trace_okS H r (List.mem_range.mp hr) ha
      exact host_row_cons_inactive (fun j hj => h0 j (argRange_lt hj))
  · rw [hostActRows_flatMap]
    refine flatMap_congr_on _ _ _ (fun r hr => ?_)
    by_cases ha : rowAct Host.table tr pub 22 r
    · rw [if_pos ha]; rfl
    · rw [if_neg ha]; show (rowMsgs GasT tr pub 22 r busStk false).map decMsg = []; rw [gas_inactive_nil ha]; rfl

theorem seg_regc_conS {r : Nat} (hr : r < tr.height 27) :
    ∀ e ∈ RegC.table.constraints, e.eval (natRow (rowNat tr 27 r) (tr.row pub 27 r)) = 0 :=
  table_constr_eqXS H (t := 27) (by simp [seg_air_len]) Seg.RegCK.table (seg_t27 nloc ngl) hr

theorem seg_regc_partS :
    ((part RegC.table tr pub 27 busStk true).map decMsg).Perm
        ((List.range (tr.height 27)).flatMap (regNetProd tr pub) ++
          (List.range (tr.height 27)).flatMap (regClr tr pub)) ∧
    ((part RegC.table tr pub 27 busStk false).map decMsg).Perm
        ((List.range (tr.height 27)).flatMap (regNetCons tr pub) ++
          (List.range (tr.height 27)).flatMap (regClr tr pub)) := by
  unfold part
  rw [List.map_flatMap, List.map_flatMap]
  constructor
  · refine List.Perm.trans (List.Perm.of_eq ?_) (perm_flatMap_append _ _ _)
    exact flatMap_congr_on _ _ _ (fun r hr => regc_prod_split (seg_regc_conS H (List.mem_range.mp hr)))
  · refine List.Perm.trans (List.Perm.of_eq ?_) (perm_flatMap_append _ _ _)
    exact flatMap_congr_on _ _ _ (fun r _ => regc_cons_split tr pub r)

/-- An instruction chip's CH block, decoded, is its active rows'. -/
theorem seg_chip_decS (X : Ctx) (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) (s : Bool) :
    (part (chipT t) tr pub t busStk s).map decMsg =
      (actRows tr pub t).flatMap (fun r => (rowMsgs (chipT t) tr pub t r busStk s).map decMsg) := by
  unfold part
  rw [seg_chip_part_chS H X t h1 h9 s, List.map_flatMap]

/-- The decoded CH block of the instruction chips. -/
theorem seg_chips_decS (X : Ctx) (s : Bool) :
    (chipsPart tr pub busStk s).map decMsg =
      (actList tr pub).flatMap (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk s).map decMsg) := by
  have r14 : part RetT.table tr pub 14 busStk s = part (chipT 14) tr pub 14 busStk s :=
    part_congr_filter (retT_filter busStk s (by decide))
  unfold chipsPart
  rw [r14]
  simp only [List.map_append]
  rw [seg_chip_decS H X 1 (by omega) (by omega), seg_chip_decS H X 2 (by omega) (by omega),
    seg_chip_decS H X 3 (by omega) (by omega), seg_chip_decS H X 4 (by omega) (by omega),
    seg_chip_decS H X 5 (by omega) (by omega), seg_chip_decS H X 6 (by omega) (by omega),
    seg_chip_decS H X 7 (by omega) (by omega), seg_chip_decS H X 8 (by omega) (by omega),
    seg_chip_decS H X 9 (by omega) (by omega), seg_chip_decS H X 10 (by omega) (by omega),
    seg_chip_decS H X 11 (by omega) (by omega), seg_chip_decS H X 12 (by omega) (by omega),
    seg_chip_decS H X 13 (by omega) (by omega), seg_chip_decS H X 14 (by omega) (by omega),
    actList_flatMap]

/-- The decoded CH bus of a segment trace, produced side, as blocks. -/
theorem seg_ch_dec_trueS (X : Ctx) :
    (msgs (wasmBaseSegAir nloc ngl) tr pub busStk true).map decMsg =
      (part Segb.table tr pub 0 busStk true).map decMsg ++
      ((actList tr pub).flatMap (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk true).map decMsg) ++
      ((part Memb.table tr pub 19 busStk true).map decMsg ++
      ((part HostG.table tr pub 22 busStk true).map decMsg ++
      ((part HostB.table tr pub 25 busStk true).map decMsg ++
      ((actRowsT IfC.table tr pub 26).flatMap (rowProd IfC.table tr pub 26) ++
      ((part RegC.table tr pub 27 busStk true).map decMsg ++
      ((actRowsT Conv.table tr pub 28).flatMap (rowProd Conv.table tr pub 28) ++
      ((actRowsT Unreach.table tr pub 29).flatMap (rowProd Unreach.table tr pub 29) ++
      (part Cut.In.table tr pub 30 busStk true).map decMsg)))))))) := by
  rw [seg_msgs_air2, List.map_append, List.map_append, seg_chips_decS H X, seg_rest_dec_true]

/-- The decoded CH bus of a segment trace, consumed side, as blocks. -/
theorem seg_ch_dec_falseS (X : Ctx) :
    (msgs (wasmBaseSegAir nloc ngl) tr pub busStk false).map decMsg =
      (part Segb.table tr pub 0 busStk false).map decMsg ++
      ((actList tr pub).flatMap (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk false).map decMsg) ++
      ((part Drop.table tr pub 18 busStk false).map decMsg ++
      ((part Memb.table tr pub 19 busStk false).map decMsg ++
      ((part HostG.table tr pub 22 busStk false).map decMsg ++
      ((part HostB.table tr pub 25 busStk false).map decMsg ++
      ((actRowsT IfC.table tr pub 26).flatMap (rowCons IfC.table tr pub 26) ++
      ((part RegC.table tr pub 27 busStk false).map decMsg ++
      ((actRowsT Conv.table tr pub 28).flatMap (rowCons Conv.table tr pub 28) ++
      ((actRowsT Unreach.table tr pub 29).flatMap (rowCons Unreach.table tr pub 29) ++
      (part Cut.Out.table tr pub 31 busStk false).map decMsg))))))))) := by
  rw [seg_msgs_air2, List.map_append, List.map_append, seg_chips_decS H X, seg_rest_dec_false]

end

/-- **`hch` for the segment AIR**, from `HoldsX`, `HostBLinked` and `RegCLinked`: the CH balance
with the segment's in-boundary block `initS` and out-boundary block `finS`. -/
theorem seg_hchS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    (X : Ctx) (hb : HostBLinked tr pub) (hg : RegCLinked tr pub) :
    (initS tr pub ++ (actListM2 tr pub).flatMap (prodCHS tr pub)).Perm
      (finS tr pub ++ (actListM2 tr pub).flatMap (consCHS tr pub)) := by
  have hbus := (seg_msgs_permS H busStk (Or.inr rfl)).map decMsg
  rw [seg_ch_dec_trueS H X, seg_ch_dec_falseS H X] at hbus
  have pBt := m2_hostb_partition hb true
  have pBf := m2_hostb_partition hb false
  obtain ⟨pRt, pRf⟩ := seg_regc_partS H
  have gRt := m2_reg_partition hb hg (regNetProd tr pub)
    (fun r' hr hna => (regc_inactive_nil (seg_regc_conS H hr) hna).1)
  have gRf := m2_reg_partition hb hg (regNetCons tr pub)
    (fun r' hr hna => (regc_inactive_nil (seg_regc_conS H hr) hna).2)
  have aT := actListM2_prod_perm tr pub
  have aF := actListM2_cons_perm tr pub
  have cT : ((actListM2 tr pub).flatMap (prodCHS tr pub)).Perm
      ((actListM2 tr pub).flatMap (prodCHM2 tr pub) ++ (hostActRows tr pub).flatMap (fun ρ => gasProdOf tr pub ρ.2)) := by
    rw [← actListM2_gas_prod]; exact perm_flatMap_append _ _ _
  have cF : ((actListM2 tr pub).flatMap (consCHS tr pub)).Perm
      ((actListM2 tr pub).flatMap (consCHM2 tr pub) ++ (hostActRows tr pub).flatMap (fun ρ => gasConsOf tr pub ρ.2)) := by
    rw [← actListM2_gas_cons]; exact perm_flatMap_append _ _ _
  exact seg_ch_assemble _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hbus (seg_host_ch_sendS H) (seg_host_ch_recvS H) pBt pBf pRt pRf gRt gRf aT aF cT cF

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- **The out-boundary block has `FinSplit`'s shape.** -/
theorem seg_finSplitS : FinSplit tr pub (finS tr pub) := by
  intro x hx
  simp only [finS, List.mem_append] at hx
  rcases hx with hx | hx | hx | hx <;> obtain ⟨r, hr, m, hm, rfl⟩ := mem_part_dec.mp hx
  · rw [rowMsgs_one cuto_recv_filter] at hm
    split at hm
    · rename_i hc
      have e := cuto_act_eval tr pub r
      change ((Cut.Out.c "act").eval (tr.row pub 31 r)).toNat = 1 at hc
      rw [e] at hc
      simp only [List.mem_singleton] at hm
      exact Or.inl ⟨r, hr, hc, by rw [hm]; rfl⟩
    · cases hm
  · exact Or.inr (Or.inl (rowMsgs_space memb_recv_space (by rw [P_val]; decide) hm))
  · exact Or.inr (Or.inr (Or.inl (rowMsgs_space segb_recv_space (by rw [P_val]; decide) hm)))
  · rw [rowMsgs_one drop_recv_filter] at hm
    split at hm
    · rename_i hc
      simp only [List.mem_singleton] at hm
      obtain ⟨b0, b1, -, -⟩ := drop_rowS H hr
      obtain ⟨i0, i1, -, -⟩ := drop_ix
      have e : ((Drop.c "act" * (1 - Drop.c "isT")).eval (tr.row pub 18 r)) =
          ((rowNat tr 18 r 0 : Nat) : F) * (1 - ((rowNat tr 18 r 1 : Nat) : F)) := by
        simp only [Drop.c, i0, i1, v, Expr.eval, Trace.row, rowNat, Fp.cast_toNat]; rfl
      have hc' : (((rowNat tr 18 r 0 : Nat) : F) * (1 - ((rowNat tr 18 r 1 : Nat) : F))).toNat = 1 := by
        rw [← e]; exact hc
      have hP := P_val
      refine Or.inr (Or.inr (Or.inr ⟨r, hr, ?_, ?_, by rw [hm]; rfl⟩)) <;>
        rcases (by omega : rowNat tr 18 r 0 = 0 ∨ rowNat tr 18 r 0 = 1) with h0 | h0 <;>
        rcases (by omega : rowNat tr 18 r 1 = 0 ∨ rowNat tr 18 r 1 = 1) with h1 | h1 <;>
        rw [h0, h1] at hc' <;> first | omega | (exfalso; revert hc'; decide)
    · cases hm

end

end WasmBase
