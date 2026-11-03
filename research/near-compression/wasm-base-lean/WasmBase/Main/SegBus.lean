import WasmBase.Main.M2Sound
import WasmBase.Main.SegSound

/-!
# WasmBase.Main.SegBus — the STATE/CH bus decomposition of `wasmBaseSegAir` (E2E M4b, S4)

WIP
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## The table split -/

theorem seg_msgs_air (nloc ngl : Nat) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) :
    msgs (wasmBaseSegAir nloc ngl) tr pub b s =
      part Segb.table tr pub 0 b s ++ (part (chipT 1) tr pub 1 b s ++ (part (chipT 2) tr pub 2 b s ++
      (part (chipT 3) tr pub 3 b s ++ (part (chipT 4) tr pub 4 b s ++ (part (chipT 5) tr pub 5 b s ++
      (part (chipT 6) tr pub 6 b s ++ (part (chipT 7) tr pub 7 b s ++ (part (chipT 8) tr pub 8 b s ++
      (part (chipT 9) tr pub 9 b s ++ (part (chipT 10) tr pub 10 b s ++ (part (chipT 11) tr pub 11 b s ++
      (part (chipT 12) tr pub 12 b s ++ (part (chipT 13) tr pub 13 b s ++ (part RetT.table tr pub 14 b s ++
      (part Range16.table tr pub 15 b s ++ (part Byte.table tr pub 16 b s ++ (part Code.table tr pub 17 b s ++
      (part Drop.table tr pub 18 b s ++ (part Memb.table tr pub 19 b s ++ (part Mpath.table tr pub 20 b s ++
      (part Func.table tr pub 21 b s ++ (part HostG.table tr pub 22 b s ++ (part HostO.table tr pub 23 b s ++
      (part HostTab.table tr pub 24 b s ++ (part HostB.table tr pub 25 b s ++ (part IfC.table tr pub 26 b s ++
      (part RegC.table tr pub 27 b s ++ (part Conv.table tr pub 28 b s ++ (part Unreach.table tr pub 29 b s ++
      (part Cut.In.table tr pub 30 b s ++ part Cut.Out.table tr pub 31 b s)))))))))))))))))))))))))))))) := by
  rw [msgs_flatMap]
  simp only [wasmBaseSegAir, List.zipIdx_cons, List.flatMap_cons, List.zipIdx_nil, List.flatMap_nil,
    List.append_nil, Nat.reduceAdd, part, chipT]

/-! ## Count bits on STATE and CH -/

/-- Every STATE/CH count of `T` passes `BitS`. -/
def SCBitS (T : Table) : Bool :=
  T.inters.all fun i => decide (i.bus ≠ busState ∧ i.bus ≠ busStk) || BitS (bcOf T) (beOf T) i.count

theorem seg_scbits (nloc ngl : Nat) :
    ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 19 → t ≠ 22 →
      SCBitS ((wasmBaseSegAir nloc ngl).tables[t]'ht) = true := by
  have e : (wasmBaseSegAir nloc ngl).tables = (wasmBaseSegAir 0 0).tables := rfl
  have h0 : ∀ t (ht : t < (wasmBaseSegAir 0 0).tables.length), ¬ (1 ≤ t ∧ t ≤ 14) → t ≠ 19 → t ≠ 22 →
      SCBitS ((wasmBaseSegAir 0 0).tables[t]'ht) = true := by
    decide +kernel
  simp only [e]; exact h0

theorem memb_sc_shape : Memb.table.inters.all (fun i => decide (i.bus ≠ busState ∧ i.bus ≠ busStk) ||
    decide (i.count = Memb.kD)) = true := by decide +kernel

/-- The interactions HOST + gas register adds to HOST' (gas receive, time check, gas send). -/
def hostGExtra : List Inter :=
  [chRecv (Expr.c spaceGas) 0 (v HostG.gS) (limbsOf HostG.gb) (v HostG.gtp) (v Host.act)] ++
  timeChk (v cTs) (v HostG.gtp) (v HostG.ghi) (v Host.act) ++
  [chSend (Expr.c spaceGas) 0 (v cS + v cFee) (limbsOf Host.ga) (v cTs) (v Host.act)]

theorem hostG_inters_eq : HostG.inters = Host.inters ++ ([⟨busRegRd, true, HostR.rrCnt, HostR.rrMsg⟩] ++ hostGExtra) := by
  simp only [HostG.inters, HostR.inters, hostGExtra, List.append_assoc]

theorem hostGExtra_sc : hostGExtra.all (fun i => decide (i.bus ≠ busState ∧ i.bus ≠ busStk) ||
    decide (i.count = v Host.act)) = true := by decide +kernel

theorem seg_t22 (nloc ngl : Nat) :
    (wasmBaseSegAir nloc ngl).tables[22]'(by simp [seg_air_len]) = HostG.table := rfl

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- The HOST constraints hold on table 22 of a segment trace (HOST + gas register extends them). -/
theorem seg_host_con {r : Nat} (hr : r < tr.height 22) :
    ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 := by
  intro e he
  have h := table_constrX H (t := 22) (by simp [seg_air_len]) hr e
  rw [seg_t22] at h
  exact h (HostR.constraints_prefix.subset he)

/-- **Every STATE/CH occurrence of a segment trace has count ≤ 1** (both directions). -/
theorem seg_occ_bits :
    ∀ o ∈ occs (wasmBaseSegAir nloc ngl) tr pub, (o.1 = busState ∨ o.1 = busStk) → o.2.2.2 ≤ 1 := by
  intro o ho hk
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hk ⊢
  by_cases hc : 1 ≤ t ∧ t ≤ 13
  · have hT := seg_chipT nloc ngl t hc.1 hc.2
    have hcon := table_constr_eqX H ht (chipT t) hT hr
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
      table_constr_eqX H ht RetT.table (seg_t14' nloc ngl) hr
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
    · rw [hc]; exact (memb_kD_le H hr).1
  by_cases h22 : t = 22
  · subst h22
    rw [seg_t22] at hi
    have hcon := seg_host_con H hr
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
    · rcases bitS_sound H.toC ht hr _ hc with h | h <;> rw [h] <;> decide

/-- **The STATE and CH buses of a segment trace are permutations.** -/
theorem seg_msgs_perm (b : Nat) (hb : b = busState ∨ b = busStk) :
    (msgs (wasmBaseSegAir nloc ngl) tr pub b true).Perm (msgs (wasmBaseSegAir nloc ngl) tr pub b false) :=
  msgs_permX H b (by rcases hb with rfl | rfl <;> decide)
    (fun o ho hk => seg_occ_bits H o ho (by rw [hk]; exact hb))

end

/-! ## Per-table parts on STATE and CH -/

theorem part_congr_filter {T T' : Table} {tr : Trace} {pub : List F} {t b : Nat} {s : Bool}
    (h : T.inters.filter (fun i => i.bus = b ∧ i.send = s) = T'.inters.filter (fun i => i.bus = b ∧ i.send = s)) :
    part T tr pub t b s = part T' tr pub t b s := by
  unfold part
  congr 1; funext r
  rw [rowMsgs_eq, rowMsgs_eq, h]

/-- Tables without STATE traffic. -/
theorem seg_state_nil (tr : Trace) (pub : List F) (s : Bool) :
    part Range16.table tr pub 15 busState s = [] ∧ part Byte.table tr pub 16 busState s = [] ∧
    part Code.table tr pub 17 busState s = [] ∧ part Drop.table tr pub 18 busState s = [] ∧
    part Memb.table tr pub 19 busState s = [] ∧ part Mpath.table tr pub 20 busState s = [] ∧
    part Func.table tr pub 21 busState s = [] ∧ part HostO.table tr pub 23 busState s = [] ∧
    part HostTab.table tr pub 24 busState s = [] ∧ part HostB.table tr pub 25 busState s = [] ∧
    part RegC.table tr pub 27 busState s = [] ∧ part Cut.In.table tr pub 30 busState s = [] ∧
    part Cut.Out.table tr pub 31 busState s = [] := by
  refine ⟨part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_,
    part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_,
    part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_,
    part_nil_of_filter ?_⟩ <;> cases s <;> decide +kernel

theorem retT_filter (b : Nat) (s : Bool) (hb : b ≠ busTomb) :
    RetT.table.inters.filter (fun i => i.bus = b ∧ i.send = s) =
      Ret.table.inters.filter (fun i => i.bus = b ∧ i.send = s) := by
  show (Ret.inters ++ _).filter _ = Ret.inters.filter _
  rw [List.filter_append]
  simp only [List.filter_cons, List.filter_nil]
  rw [if_neg (by simp only [decide_eq_true_eq, not_and]; intro h; exact absurd h.symm hb), List.append_nil]

theorem hostG_filter_state (s : Bool) :
    HostG.table.inters.filter (fun i => i.bus = busState ∧ i.send = s) =
      Host.table.inters.filter (fun i => i.bus = busState ∧ i.send = s) := by
  show HostG.inters.filter _ = Host.inters.filter _
  rw [hostG_inters_eq, List.filter_append]
  have : ([(⟨busRegRd, true, HostR.rrCnt, HostR.rrMsg⟩ : Inter)] ++ hostGExtra).filter
      (fun i => i.bus = busState ∧ i.send = s) = [] := by cases s <;> decide +kernel
  rw [this, List.append_nil]

/-- SEGB's STATE send (the in-boundary message) and receive (the out-boundary message). -/
def segM0 (tr : Trace) (pub : List F) : List F := (Segb.inters.getD 0 default).msg.map (·.eval (tr.row pub 0 0))
def segMF (tr : Trace) (pub : List F) : List F := (Segb.inters.getD 1 default).msg.map (·.eval (tr.row pub 0 0))

theorem segM0_eq (tr : Trace) (pub : List F) :
    segM0 tr pub = [pub.getD pubPcIn 0, pub.getD pubTIn 0 + 1, pub.getD pubSIn 0, 0, pub.getD pubSbIn 0,
      pub.getD pubCidIn 0] := by
  simp [segM0, Segb.inters, stateOut, pv, Expr.eval, Trace.row, one_cast, zero_cast]

theorem segMF_eq (tr : Trace) (pub : List F) :
    segMF tr pub = [pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0,
      pub.getD Boundary.pubStatus 0, pub.getD pubSbOut 0, tr.cell 0 0 (ix Segb.cols "cidf")] := by
  simp [segMF, Segb.inters, Segb.c, pv, v, Expr.eval, Trace.row, one_cast]

theorem rowMsgs_first {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {s : Bool} {i0 : Inter}
    (hf : T.inters.filter (fun i => i.bus = b ∧ i.send = s) = [i0]) (hc : i0.count = .first) :
    rowMsgs T tr pub t r b s = if r = 0 then [i0.msg.map (·.eval (tr.row pub t r))] else [] := by
  rw [rowMsgs_eq, hf]
  simp only [List.filterMap_cons, List.filterMap_nil, hc]
  by_cases h : r = 0
  · subst h; simp [Expr.eval, Trace.row]; rfl
  · simp [Expr.eval, Trace.row, h]; rfl

theorem part_first {T : Table} {tr : Trace} {pub : List F} {t b : Nat} {s : Bool} {i0 : Inter}
    (hf : T.inters.filter (fun i => i.bus = b ∧ i.send = s) = [i0]) (hc : i0.count = .first)
    (h0 : 1 ≤ tr.height t) :
    part T tr pub t b s = [i0.msg.map (·.eval (tr.row pub t 0))] := by
  unfold part
  rw [show (fun r => rowMsgs T tr pub t r b s) =
    (fun r => if r = 0 then [i0.msg.map (·.eval (tr.row pub t 0))] else []) from
    funext fun r => by rw [rowMsgs_first hf hc]; by_cases h : r = 0 <;> simp [h]]
  exact flatMap_range_first _ h0 _

theorem segb_state_parts (tr : Trace) (pub : List F) (h0 : 1 ≤ tr.height 0) :
    part Segb.table tr pub 0 busState true = [segM0 tr pub] ∧
      part Segb.table tr pub 0 busState false = [segMF tr pub] := by
  constructor
  · exact part_first (i0 := Segb.inters.getD 0 default) (by decide +kernel) rfl h0
  · exact part_first (i0 := Segb.inters.getD 1 default) (by decide +kernel) rfl h0

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

theorem seg_h0 : 1 ≤ tr.height 0 := by
  have := H.heightPos 0 (by simp [seg_air_len]); omega

/-- **The STATE bus of a segment trace.** -/
theorem seg_msgs_state :
    msgs (wasmBaseSegAir nloc ngl) tr pub busState true =
      segM0 tr pub :: (actListM2 tr pub).map (rowOutM tr pub) ∧
    msgs (wasmBaseSegAir nloc ngl) tr pub busState false =
      segMF tr pub :: (actListM2 tr pub).map (rowInM tr pub) := by
  have h0 := seg_h0 H
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
theorem seg_hst :
    (segM0 tr pub :: (actListM2 tr pub).map (rowOutM tr pub)).Perm
      (segMF tr pub :: (actListM2 tr pub).map (rowInM tr pub)) := by
  obtain ⟨e1, e2⟩ := seg_msgs_state H
  rw [← e1, ← e2]
  exact seg_msgs_perm H busState (Or.inl rfl)

end

/-! ## The base view of a segment trace

`segBase tr` is `tr` with the tables that differ from `wasmBaseAir`'s (BOUNDARY/SEGB 0, DRAIN/DROP 18,
MEMINIT/MEMB 19, DATA/MPATH 20) emptied.  Every other base table (the instruction chips 1–14, RANGE16,
BYTE, CODE, FUNC) is the segment AIR's at the same index (RET: same constraints), so a segment trace
satisfies the base AIR's **constraints** on `segBase tr` (`seg_base_holdsC`), and the base per-chip
facts (`chipFactsC`) apply to its rows, which are `tr`'s rows. -/

def baseGone (t : Nat) : Prop := t = 0 ∨ t = 18 ∨ t = 19 ∨ t = 20

instance (t : Nat) : Decidable (baseGone t) := by unfold baseGone; infer_instance

def segBase (tr : Trace) : Trace := ⟨fun t => if baseGone t then 0 else tr.height t, tr.cell⟩

theorem segBase_height {tr : Trace} {t : Nat} (h : ¬ baseGone t) : (segBase tr).height t = tr.height t := by
  simp [segBase, h]

theorem segBase_row {tr : Trace} {pub : List F} {t : Nat} (h : ¬ baseGone t) (r : Nat) :
    (segBase tr).row pub t r = tr.row pub t r := by
  simp only [Trace.row, segBase_height h]; rfl

theorem segBase_rowNat {tr : Trace} {t r : Nat} : rowNat (segBase tr) t r = rowNat tr t r := rfl

theorem segBase_rowMsgs {tr : Trace} {pub : List F} {T : Table} {t : Nat} (h : ¬ baseGone t) (r b : Nat) (s : Bool) :
    rowMsgs T (segBase tr) pub t r b s = rowMsgs T tr pub t r b s := by
  unfold rowMsgs rowOccs; rw [segBase_row h]

theorem segBase_rowAct {tr : Trace} {pub : List F} {T : Table} {t : Nat} (h : ¬ baseGone t) (r : Nat) :
    rowAct T (segBase tr) pub t r ↔ rowAct T tr pub t r := by
  unfold rowAct; rw [segBase_row h]

/-- The base AIR's tables that survive in the segment AIR, at the same index, with the same constraints. -/
theorem seg_base_constraints (nloc ngl t : Nat) (ht : t < 22) (hg : ¬ baseGone t) :
    ((wasmBaseAir nloc ngl).tables[t]'(by rw [air_len]; exact ht)).constraints =
      ((wasmBaseSegAir nloc ngl).tables[t]'(by simp [seg_air_len]; omega)).constraints := by
  unfold baseGone at hg
  rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
    t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 21 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem seg_base_holdsC {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) :
    HoldsC (wasmBaseAir nloc ngl) pub (segBase tr) := by
  refine ⟨fun t ht r hr e he => ?_⟩
  have h22 : t < 22 := by rwa [air_len] at ht
  by_cases hg : baseGone t
  · simp [segBase, hg] at hr
  · rw [segBase_height hg] at hr
    rw [segBase_row hg]
    rw [seg_base_constraints nloc ngl t h22 hg] at he
    exact H.constr t _ r hr e he

/-- An inactive instruction-chip row of a segment trace emits nothing (`ChipFacts.inactive` through
`segBase`). -/
theorem seg_chip_inactive {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (X : Ctx) (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) (r : Nat) (hr : r < tr.height t)
    (hna : ¬ rowAct (chipT t) tr pub t r) (b : Nat) (s : Bool) : rowMsgs (chipT t) tr pub t r b s = [] := by
  have hg : ¬ baseGone t := by unfold baseGone; omega
  have CF := chipFactsC X (seg_base_holdsC H)
  rw [← segBase_rowMsgs hg]
  exact chip_ch_inactive CF t h1 h9 r (by rw [segBase_height hg]; exact hr)
    (by rw [segBase_rowAct hg]; exact hna) b s

theorem seg_chip_part_ch {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (X : Ctx) (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) (s : Bool) :
    ((List.range (tr.height t)).flatMap fun r => rowMsgs (chipT t) tr pub t r busStk s) =
      (actRows tr pub t).flatMap fun r => rowMsgs (chipT t) tr pub t r busStk s := by
  rw [actRows, ← flatMap_filter_of_nil]
  intro r hr hna
  exact seg_chip_inactive H X t h1 h9 r (List.mem_range.mp hr) hna busStk s

/-! ## The gas register of a HOST row

HOST + gas register (table 22) is HOST' plus `hostGExtra`: a gas-register receive, a time check
(R16) and a gas-register send, all counted by `act`.  A HOST row's CH traffic is HOST's plus the
gas part (`GasT`); an inactive row has none. -/

/-- The gas-register interactions of HOST, as a table of their own (for the row accessors). -/
def GasT : Table := ⟨"HOSTGAS", HostG.cols, [], hostGExtra⟩

/-- The gas-register messages HOST row `r` produces / consumes. -/
def gasProdOf (tr : Trace) (pub : List F) (r : Nat) : List Msg := rowProd GasT tr pub 22 r
def gasConsOf (tr : Trace) (pub : List F) (r : Nat) : List Msg := rowCons GasT tr pub 22 r

def gasProdH (tr : Trace) (pub : List F) (ρ : Nat × Nat) : List Msg := if ρ.1 = 22 then gasProdOf tr pub ρ.2 else []
def gasConsH (tr : Trace) (pub : List F) (ρ : Nat × Nat) : List Msg := if ρ.1 = 22 then gasConsOf tr pub ρ.2 else []

/-- **The CH messages a segment action row produces**: the M2 ones (`HOSTB`, REG-C fused into HOST
rows) plus a HOST row's gas register. -/
def prodCHS (tr : Trace) (pub : List F) (ρ : Nat × Nat) : List Msg := prodCHM2 tr pub ρ ++ gasProdH tr pub ρ
/-- **The CH messages a segment action row consumes.** -/
def consCHS (tr : Trace) (pub : List F) (ρ : Nat × Nat) : List Msg := consCHM2 tr pub ρ ++ gasConsH tr pub ρ

theorem hostG_rowMsgs_stk (tr : Trace) (pub : List F) (r : Nat) (s : Bool) :
    rowMsgs HostG.table tr pub 22 r busStk s = rowMsgs Host.table tr pub 22 r busStk s ++ rowMsgs GasT tr pub 22 r busStk s := by
  rw [rowMsgs_eq, rowMsgs_eq, rowMsgs_eq]
  show (HostG.inters.filter _).filterMap _ = (Host.inters.filter _).filterMap _ ++ (hostGExtra.filter _).filterMap _
  rw [hostG_inters_eq, List.filter_append, List.filter_append]
  have : ([(⟨busRegRd, true, HostR.rrCnt, HostR.rrMsg⟩ : Inter)]).filter
      (fun i => i.bus = busStk ∧ i.send = s) = [] := by cases s <;> decide +kernel
  rw [this, List.nil_append, List.filterMap_append]

theorem gasT_stk_count (s : Bool) : ∀ i ∈ GasT.inters.filter (fun i => i.bus = busStk ∧ i.send = s), i.count = v Host.act := by
  intro i hi
  have hc := List.all_eq_true.mp hostGExtra_sc i (List.mem_filter.mp hi).1
  have hb := (List.mem_filter.mp hi).2
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hc hb
  rcases hc with hc | hc
  · exact absurd hb.1 hc.2
  · exact hc

theorem gas_inactive_nil {tr : Trace} {pub : List F} {r : Nat} (hna : ¬ rowAct Host.table tr pub 22 r) (s : Bool) :
    rowMsgs GasT tr pub 22 r busStk s = [] := by
  rw [rowMsgs_eq, List.filterMap_eq_nil_iff]
  intro i hi
  rw [gasT_stk_count s i hi]
  have : ¬ ((v Host.act).eval (tr.row pub 22 r)).toNat = 1 := hna
  simp [this]

theorem gasProdH_nil_of_ne {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 ≠ 22) : gasProdH tr pub ρ = [] := by
  simp [gasProdH, h]
theorem gasConsH_nil_of_ne {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 ≠ 22) : gasConsH tr pub ρ = [] := by
  simp [gasConsH, h]

theorem actListM2_gas_prod (tr : Trace) (pub : List F) :
    (actListM2 tr pub).flatMap (gasProdH tr pub) = (hostActRows tr pub).flatMap (fun ρ => gasProdOf tr pub ρ.2) := by
  unfold actListM2 actListHost
  rw [List.flatMap_append, List.flatMap_append,
    List.flatMap_eq_nil_iff.mpr (fun ρ hρ => gasProdH_nil_of_ne (actList_ne_host hρ)),
    tail_nil22 (gasProdH tr pub) (fun ρ h => gasProdH_nil_of_ne h), List.nil_append, List.append_nil]
  exact flatMap_congr_on _ _ _ (fun ρ hρ => by simp [gasProdH, hostActRows_eq_host hρ])

theorem actListM2_gas_cons (tr : Trace) (pub : List F) :
    (actListM2 tr pub).flatMap (gasConsH tr pub) = (hostActRows tr pub).flatMap (fun ρ => gasConsOf tr pub ρ.2) := by
  unfold actListM2 actListHost
  rw [List.flatMap_append, List.flatMap_append,
    List.flatMap_eq_nil_iff.mpr (fun ρ hρ => gasConsH_nil_of_ne (actList_ne_host hρ)),
    tail_nil22 (gasConsH tr pub) (fun ρ h => gasConsH_nil_of_ne h), List.nil_append, List.append_nil]
  exact flatMap_congr_on _ _ _ (fun ρ hρ => by simp [gasConsH, hostActRows_eq_host hρ])

/-! ## Tables without CH traffic (in one direction) -/

theorem seg_stk_nil (tr : Trace) (pub : List F) :
    (∀ s, part Range16.table tr pub 15 busStk s = [] ∧ part Byte.table tr pub 16 busStk s = [] ∧
      part Code.table tr pub 17 busStk s = [] ∧ part Mpath.table tr pub 20 busStk s = [] ∧
      part Func.table tr pub 21 busStk s = [] ∧ part HostO.table tr pub 23 busStk s = [] ∧
      part HostTab.table tr pub 24 busStk s = []) ∧
    part Drop.table tr pub 18 busStk true = [] ∧ part Cut.In.table tr pub 30 busStk false = [] ∧
    part Cut.Out.table tr pub 31 busStk true = [] := by
  refine ⟨fun s => ⟨part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_,
    part_nil_of_filter ?_, part_nil_of_filter ?_, part_nil_of_filter ?_⟩, part_nil_of_filter ?_,
    part_nil_of_filter ?_, part_nil_of_filter ?_⟩ <;> (try cases s) <;> decide +kernel

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- `HostTraceOK` for a segment trace. -/
theorem seg_host_trace_ok : HostTraceOK tr pub := by
  intro r hr hneg
  have hcon := seg_host_con H hr
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
theorem seg_host_ch_send :
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
      exact host_row_prod_inactive (pub := pub) (seg_host_trace_ok H r (List.mem_range.mp hr) ha).2
  · rw [hostActRows_flatMap]
    refine flatMap_congr_on _ _ _ (fun r hr => ?_)
    by_cases ha : rowAct Host.table tr pub 22 r
    · rw [if_pos ha]; rfl
    · rw [if_neg ha]; show (rowMsgs GasT tr pub 22 r busStk true).map decMsg = []; rw [gas_inactive_nil ha]; rfl

/-- The HOST block of the CH bus, consumed side. -/
theorem seg_host_ch_recv :
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
      obtain ⟨h0, _⟩ := seg_host_trace_ok H r (List.mem_range.mp hr) ha
      exact host_row_cons_inactive (fun j hj => h0 j (argRange_lt hj))
  · rw [hostActRows_flatMap]
    refine flatMap_congr_on _ _ _ (fun r hr => ?_)
    by_cases ha : rowAct Host.table tr pub 22 r
    · rw [if_pos ha]; rfl
    · rw [if_neg ha]; show (rowMsgs GasT tr pub 22 r busStk false).map decMsg = []; rw [gas_inactive_nil ha]; rfl

theorem seg_regc_con {r : Nat} (hr : r < tr.height 27) :
    ∀ e ∈ RegC.table.constraints, e.eval (natRow (rowNat tr 27 r) (tr.row pub 27 r)) = 0 :=
  table_constr_eqX H (t := 27) (by simp [seg_air_len]) RegC.table (seg_t27 nloc ngl) hr

theorem seg_regc_part :
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
    exact flatMap_congr_on _ _ _ (fun r hr => regc_prod_split (seg_regc_con H (List.mem_range.mp hr)))
  · refine List.Perm.trans (List.Perm.of_eq ?_) (perm_flatMap_append _ _ _)
    exact flatMap_congr_on _ _ _ (fun r _ => regc_cons_split tr pub r)

/-- An instruction chip's CH block, decoded, is its active rows'. -/
theorem seg_chip_dec (X : Ctx) (t : Nat) (h1 : 1 ≤ t) (h9 : t ≤ 14) (s : Bool) :
    (part (chipT t) tr pub t busStk s).map decMsg =
      (actRows tr pub t).flatMap (fun r => (rowMsgs (chipT t) tr pub t r busStk s).map decMsg) := by
  unfold part
  rw [seg_chip_part_ch H X t h1 h9 s, List.map_flatMap]

/-- The instruction chips' parts (tables 1–14). -/
def chipsPart (tr : Trace) (pub : List F) (b : Nat) (s : Bool) : List (List F) :=
  part (chipT 1) tr pub 1 b s ++ (part (chipT 2) tr pub 2 b s ++
      (part (chipT 3) tr pub 3 b s ++ (part (chipT 4) tr pub 4 b s ++ (part (chipT 5) tr pub 5 b s ++
      (part (chipT 6) tr pub 6 b s ++ (part (chipT 7) tr pub 7 b s ++ (part (chipT 8) tr pub 8 b s ++
      (part (chipT 9) tr pub 9 b s ++ (part (chipT 10) tr pub 10 b s ++ (part (chipT 11) tr pub 11 b s ++
      (part (chipT 12) tr pub 12 b s ++ (part (chipT 13) tr pub 13 b s ++ part RetT.table tr pub 14 b s))))))))))))

/-- The parts of tables 15–31. -/
def restPart (tr : Trace) (pub : List F) (b : Nat) (s : Bool) : List (List F) :=
      part Range16.table tr pub 15 b s ++ (part Byte.table tr pub 16 b s ++ (part Code.table tr pub 17 b s ++
      (part Drop.table tr pub 18 b s ++ (part Memb.table tr pub 19 b s ++ (part Mpath.table tr pub 20 b s ++
      (part Func.table tr pub 21 b s ++ (part HostG.table tr pub 22 b s ++ (part HostO.table tr pub 23 b s ++
      (part HostTab.table tr pub 24 b s ++ (part HostB.table tr pub 25 b s ++ (part IfC.table tr pub 26 b s ++
      (part RegC.table tr pub 27 b s ++ (part Conv.table tr pub 28 b s ++ (part Unreach.table tr pub 29 b s ++
      (part Cut.In.table tr pub 30 b s ++ part Cut.Out.table tr pub 31 b s)))))))))))))))

omit H in
theorem seg_msgs_air2 (b : Nat) (s : Bool) :
    msgs (wasmBaseSegAir nloc ngl) tr pub b s =
      part Segb.table tr pub 0 b s ++ (chipsPart tr pub b s ++ restPart tr pub b s) := by
  rw [seg_msgs_air]; simp only [chipsPart, restPart, List.append_assoc]

/-- The decoded CH block of the instruction chips. -/
theorem seg_chips_dec (X : Ctx) (s : Bool) :
    (chipsPart tr pub busStk s).map decMsg =
      (actList tr pub).flatMap (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk s).map decMsg) := by
  have r14 : part RetT.table tr pub 14 busStk s = part (chipT 14) tr pub 14 busStk s :=
    part_congr_filter (retT_filter busStk s (by decide))
  unfold chipsPart
  rw [r14]
  simp only [List.map_append]
  rw [seg_chip_dec H X 1 (by omega) (by omega), seg_chip_dec H X 2 (by omega) (by omega),
    seg_chip_dec H X 3 (by omega) (by omega), seg_chip_dec H X 4 (by omega) (by omega),
    seg_chip_dec H X 5 (by omega) (by omega), seg_chip_dec H X 6 (by omega) (by omega),
    seg_chip_dec H X 7 (by omega) (by omega), seg_chip_dec H X 8 (by omega) (by omega),
    seg_chip_dec H X 9 (by omega) (by omega), seg_chip_dec H X 10 (by omega) (by omega),
    seg_chip_dec H X 11 (by omega) (by omega), seg_chip_dec H X 12 (by omega) (by omega),
    seg_chip_dec H X 13 (by omega) (by omega), seg_chip_dec H X 14 (by omega) (by omega),
    actList_flatMap]

omit H in
theorem seg_rest_dec_true :
    (restPart tr pub busStk true).map decMsg =
      (part Memb.table tr pub 19 busStk true).map decMsg ++
      ((part HostG.table tr pub 22 busStk true).map decMsg ++
      ((part HostB.table tr pub 25 busStk true).map decMsg ++
      ((actRowsT IfC.table tr pub 26).flatMap (rowProd IfC.table tr pub 26) ++
      ((part RegC.table tr pub 27 busStk true).map decMsg ++
      ((actRowsT Conv.table tr pub 28).flatMap (rowProd Conv.table tr pub 28) ++
      ((actRowsT Unreach.table tr pub 29).flatMap (rowProd Unreach.table tr pub 29) ++
      (part Cut.In.table tr pub 30 busStk true).map decMsg)))))) := by
  obtain ⟨hn, n18, -, n31⟩ := seg_stk_nil tr pub
  obtain ⟨n15, n16, n17, n20, n21, n23, n24⟩ := hn true
  unfold restPart
  rw [n15, n16, n17, n18, n20, n21, n23, n24, n31]
  simp only [List.map_append, List.map_nil, List.nil_append, List.append_nil]
  rw [(uniform_part_dec ifc_uniform tr pub 26).1, (uniform_part_dec conv_uniform tr pub 28).1,
    (uniform_part_dec unreach_uniform tr pub 29).1]

omit H in
theorem seg_rest_dec_false :
    (restPart tr pub busStk false).map decMsg =
      (part Drop.table tr pub 18 busStk false).map decMsg ++
      ((part Memb.table tr pub 19 busStk false).map decMsg ++
      ((part HostG.table tr pub 22 busStk false).map decMsg ++
      ((part HostB.table tr pub 25 busStk false).map decMsg ++
      ((actRowsT IfC.table tr pub 26).flatMap (rowCons IfC.table tr pub 26) ++
      ((part RegC.table tr pub 27 busStk false).map decMsg ++
      ((actRowsT Conv.table tr pub 28).flatMap (rowCons Conv.table tr pub 28) ++
      ((actRowsT Unreach.table tr pub 29).flatMap (rowCons Unreach.table tr pub 29) ++
      (part Cut.Out.table tr pub 31 busStk false).map decMsg))))))) := by
  obtain ⟨hn, -, n30, -⟩ := seg_stk_nil tr pub
  obtain ⟨n15, n16, n17, n20, n21, n23, n24⟩ := hn false
  unfold restPart
  rw [n15, n16, n17, n20, n21, n23, n24, n30]
  simp only [List.map_append]
  rw [(uniform_part_dec ifc_uniform tr pub 26).2, (uniform_part_dec conv_uniform tr pub 28).2,
    (uniform_part_dec unreach_uniform tr pub 29).2]
  generalize (part Drop.table tr pub 18 busStk false).map decMsg = A1
  generalize (part Memb.table tr pub 19 busStk false).map decMsg = A2
  generalize (part HostG.table tr pub 22 busStk false).map decMsg = A3
  generalize (part HostB.table tr pub 25 busStk false).map decMsg = A4
  generalize (actRowsT IfC.table tr pub 26).flatMap (rowCons IfC.table tr pub 26) = A5
  generalize (part RegC.table tr pub 27 busStk false).map decMsg = A6
  generalize (actRowsT Conv.table tr pub 28).flatMap (rowCons Conv.table tr pub 28) = A7
  generalize (actRowsT Unreach.table tr pub 29).flatMap (rowCons Unreach.table tr pub 29) = A8
  generalize (part Cut.Out.table tr pub 31 busStk false).map decMsg = A9
  simp only [List.map_nil, List.nil_append, List.append_nil]

/-- The decoded CH bus of a segment trace, produced side, as blocks. -/
theorem seg_ch_dec_true (X : Ctx) :
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
  rw [seg_msgs_air2, List.map_append, List.map_append, seg_chips_dec H X, seg_rest_dec_true]

/-- The decoded CH bus of a segment trace, consumed side, as blocks. -/
theorem seg_ch_dec_false (X : Ctx) :
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
  rw [seg_msgs_air2, List.map_append, List.map_append, seg_chips_dec H X, seg_rest_dec_false]

end

/-! ## The segment's boundary blocks of the CH bus -/

/-- **The in-boundary block** (`init`): CUTI's productions (the previous segment's live
non-memory messages), MEMB's (the touched memory bytes) and SEGB's gas register, all at `t_in`. -/
def initS (tr : Trace) (pub : List F) : List Msg :=
  (part Cut.In.table tr pub 30 busStk true).map decMsg ++
    ((part Memb.table tr pub 19 busStk true).map decMsg ++ (part Segb.table tr pub 0 busStk true).map decMsg)

/-- **The out-boundary block** (`fin`): CUTO's, MEMB's, SEGB's and DROP's consumptions. -/
def finS (tr : Trace) (pub : List F) : List Msg :=
  (part Cut.Out.table tr pub 31 busStk false).map decMsg ++
    ((part Memb.table tr pub 19 busStk false).map decMsg ++
      ((part Segb.table tr pub 0 busStk false).map decMsg ++ (part Drop.table tr pub 18 busStk false).map decMsg))

/-- The CH block bookkeeping of the segment AIR, over abstract lists. -/
theorem seg_ch_assemble {α : Type} [DecidableEq α]
    (Sgt Acht Mbt HGt HBt Ift RGt Cvt Urt Cit Sgf Achf Drf Mbf HGf HBf Iff RGf Cvf Urf Cof
      Hht Gst Hhf Gsf HBt' HBf' Rnt Cl Rnf RGnt RGnf P Q PS QS : List α)
    (hbus : (Sgt ++ (Acht ++ (Mbt ++ (HGt ++ (HBt ++ (Ift ++ (RGt ++ (Cvt ++ (Urt ++ Cit))))))))).Perm
      (Sgf ++ (Achf ++ (Drf ++ (Mbf ++ (HGf ++ (HBf ++ (Iff ++ (RGf ++ (Cvf ++ (Urf ++ Cof)))))))))))
    (pHt : HGt.Perm (Hht ++ Gst)) (pHf : HGf.Perm (Hhf ++ Gsf))
    (pBt : HBt'.Perm HBt) (pBf : HBf'.Perm HBf)
    (pRt : RGt.Perm (Rnt ++ Cl)) (pRf : RGf.Perm (Rnf ++ Cl))
    (gRt : RGnt.Perm Rnt) (gRf : RGnf.Perm Rnf)
    (aT : P.Perm ((((Acht ++ Hht) ++ (Ift ++ (Cvt ++ Urt))) ++ HBt') ++ RGnt))
    (aF : Q.Perm ((((Achf ++ Hhf) ++ (Iff ++ (Cvf ++ Urf))) ++ HBf') ++ RGnf))
    (cT : PS.Perm (P ++ Gst)) (cF : QS.Perm (Q ++ Gsf)) :
    ((Cit ++ (Mbt ++ Sgt)) ++ PS).Perm ((Cof ++ (Mbf ++ (Sgf ++ Drf))) ++ QS) := by
  rw [List.perm_iff_count] at *
  intro a
  have c0 := hbus a
  have c1 := pHt a
  have c2 := pHf a
  have c3 := pBt a
  have c4 := pBf a
  have c5 := pRt a
  have c6 := pRf a
  have c7 := gRt a
  have c8 := gRf a
  have c9 := aT a
  have c10 := aF a
  have c11 := cT a
  have c12 := cF a
  simp only [List.count_append] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 ⊢
  omega

/-- **`hch` for the segment AIR**, from `HoldsX`, `HostBLinked` and `RegCLinked`: the CH balance
with the segment's in-boundary block `initS` and out-boundary block `finS`. -/
theorem seg_hch {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (X : Ctx) (hb : HostBLinked tr pub) (hg : RegCLinked tr pub) :
    (initS tr pub ++ (actListM2 tr pub).flatMap (prodCHS tr pub)).Perm
      (finS tr pub ++ (actListM2 tr pub).flatMap (consCHS tr pub)) := by
  have hbus := (seg_msgs_perm H busStk (Or.inr rfl)).map decMsg
  rw [seg_ch_dec_true H X, seg_ch_dec_false H X] at hbus
  have pBt := m2_hostb_partition hb true
  have pBf := m2_hostb_partition hb false
  obtain ⟨pRt, pRf⟩ := seg_regc_part H
  have gRt := m2_reg_partition hb hg (regNetProd tr pub)
    (fun r' hr hna => (regc_inactive_nil (seg_regc_con H hr) hna).1)
  have gRf := m2_reg_partition hb hg (regNetCons tr pub)
    (fun r' hr hna => (regc_inactive_nil (seg_regc_con H hr) hna).2)
  have aT := actListM2_prod_perm tr pub
  have aF := actListM2_cons_perm tr pub
  have cT : ((actListM2 tr pub).flatMap (prodCHS tr pub)).Perm
      ((actListM2 tr pub).flatMap (prodCHM2 tr pub) ++ (hostActRows tr pub).flatMap (fun ρ => gasProdOf tr pub ρ.2)) := by
    rw [← actListM2_gas_prod]; exact perm_flatMap_append _ _ _
  have cF : ((actListM2 tr pub).flatMap (consCHS tr pub)).Perm
      ((actListM2 tr pub).flatMap (consCHM2 tr pub) ++ (hostActRows tr pub).flatMap (fun ρ => gasConsOf tr pub ρ.2)) := by
    rw [← actListM2_gas_cons]; exact perm_flatMap_append _ _ _
  exact seg_ch_assemble _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hbus (seg_host_ch_send H) (seg_host_ch_recv H) pBt pBf pRt pRf gRt gRf aT aF cT cF

/-! ## The boundary blocks: what they contain

* `finS` is exactly `FinSplit`'s shape (CUTO's consumptions of active rows, memory = space 3, the gas
  register = space 7, DROP's consumptions of active non-tomb rows): `seg_finSplit`; every active CUTO
  row's message is in it: `seg_cuto_in_fin`.  These are the hypotheses `FinSplit`/`hin` of
  `seg_sound_cut_pub`, now theorems.
* every message of `initS` is produced at `t_in` (`seg_initS_tp`). -/

theorem mem_part_dec {T : Table} {tr : Trace} {pub : List F} {t b : Nat} {s : Bool} {x : Msg} :
    x ∈ (part T tr pub t b s).map decMsg ↔
      ∃ r, r < tr.height t ∧ ∃ m ∈ rowMsgs T tr pub t r b s, x = decMsg m := by
  unfold part
  simp only [List.mem_map, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨m, ⟨r, hr, hm⟩, rfl⟩; exact ⟨r, hr, m, hm, rfl⟩
  · rintro ⟨r, hr, m, hm, rfl⟩; exact ⟨m, ⟨r, hr, hm⟩, rfl⟩

theorem rowMsgs_one {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {s : Bool} {i0 : Inter}
    (hf : T.inters.filter (fun i => i.bus = b ∧ i.send = s) = [i0]) :
    rowMsgs T tr pub t r b s =
      if (i0.count.eval (tr.row pub t r)).toNat = 1 then [i0.msg.map (·.eval (tr.row pub t r))] else [] := by
  rw [rowMsgs_eq, hf]
  simp only [List.filterMap_cons, List.filterMap_nil]
  by_cases h : (i0.count.eval (tr.row pub t r)).toNat = 1 <;> simp [h]

/-- Every message of `rowMsgs` comes from a filtered interaction. -/
theorem mem_rowMsgs {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {s : Bool} {m : List F}
    (hm : m ∈ rowMsgs T tr pub t r b s) :
    ∃ i ∈ T.inters.filter (fun i => i.bus = b ∧ i.send = s), m = i.msg.map (·.eval (tr.row pub t r)) := by
  rw [rowMsgs_eq] at hm
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hm
  split at he
  · cases he; exact ⟨i, hi, rfl⟩
  · cases he

/-- A message whose space expression is the constant `k` decodes to space `k`. -/
theorem rowMsgs_space {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {s : Bool} {k : Nat}
    (h : ∀ i ∈ T.inters.filter (fun i => i.bus = b ∧ i.send = s), i.msg.head? = some (Expr.c k)) (hk : k < P)
    {m : List F} (hm : m ∈ rowMsgs T tr pub t r b s) : (decMsg m).space = k := by
  obtain ⟨i, hi, rfl⟩ := mem_rowMsgs hm
  have h0 := h i hi
  cases hmsg : i.msg with
  | nil => rw [hmsg] at h0; cases h0
  | cons e es =>
    rw [hmsg] at h0
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    simp only [decMsg, List.map_cons, List.getD_cons_zero, Expr.eval]
    exact Fp.toNat_cast_of_lt hk

/-- A message whose producer-time expression is the public `t_in` decodes to producer time `t_in`. -/
theorem rowMsgs_tp {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {s : Bool}
    (h : ∀ i ∈ T.inters.filter (fun i => i.bus = b ∧ i.send = s), i.msg[7]? = some (pv pubTIn))
    {m : List F} (hm : m ∈ rowMsgs T tr pub t r b s) : (decMsg m).tp = (pub.getD pubTIn 0).toNat := by
  obtain ⟨i, hi, rfl⟩ := mem_rowMsgs hm
  have h0 := h i hi
  simp only [decMsg, List.getD_eq_getElem?_getD, List.getElem?_map, h0, Option.map_some, Option.getD_some,
    pv, Expr.eval, Trace.row]

theorem memb_recv_space : ∀ i ∈ Memb.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false),
    i.msg.head? = some (Expr.c 3) := by decide +kernel
theorem segb_recv_space : ∀ i ∈ Segb.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false),
    i.msg.head? = some (Expr.c 7) := by decide +kernel
theorem cuti_send_tp : ∀ i ∈ Cut.In.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true),
    i.msg[7]? = some (pv pubTIn) := by decide +kernel
theorem memb_send_tp : ∀ i ∈ Memb.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true),
    i.msg[7]? = some (pv pubTIn) := by decide +kernel
theorem segb_send_tp : ∀ i ∈ Segb.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true),
    i.msg[7]? = some (pv pubTIn) := by decide +kernel

theorem cuto_recv_filter : Cut.Out.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
    [chRecv (Cut.Out.c "space") (Cut.Out.c "slot") (Cut.Out.F 2)
      [Cut.Out.F 3, Cut.Out.F 4, Cut.Out.c "x2", Cut.Out.F 6] (Cut.Out.c "tp") (Cut.Out.c "act")] := by
  decide +kernel

theorem drop_recv_filter : Drop.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
    [chRecv (16 + Drop.c "c") (Drop.c "slot") (Drop.c "tag")
      [Drop.c "x0", Drop.c "x1", Drop.c "x2", Drop.c "x3"] (Drop.c "tp") (Drop.c "act" * (1 - Drop.c "isT"))] := by
  decide +kernel

theorem cuto_act_eval (tr : Trace) (pub : List F) (r : Nat) :
    ((Cut.Out.c "act").eval (tr.row pub 31 r)).toNat = rowNat tr 31 r 0 := by
  have : ix Cut.Out.cols "act" = 0 := by decide
  simp only [Cut.Out.c, Cut.c, this, v, Expr.eval, Trace.row, rowNat]

/-- The `initS` messages are produced at `t_in`. -/
theorem seg_initS_tp (tr : Trace) (pub : List F) : ∀ x ∈ initS tr pub, x.tp = (pub.getD pubTIn 0).toNat := by
  intro x hx
  simp only [initS, List.mem_append] at hx
  rcases hx with hx | hx | hx <;> obtain ⟨r, -, m, hm, rfl⟩ := mem_part_dec.mp hx
  · exact rowMsgs_tp cuti_send_tp hm
  · exact rowMsgs_tp memb_send_tp hm
  · exact rowMsgs_tp segb_send_tp hm

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

omit H in
/-- **Every active CUTO row's consumed message is in the out-boundary block** (`hin`). -/
theorem seg_cuto_in_fin : ∀ r, r < tr.height 31 → rowNat tr 31 r 0 = 1 → cutoMsg tr pub r ∈ finS tr pub := by
  intro r hr ha
  refine List.mem_append_left _ (mem_part_dec.mpr ⟨r, hr, _, ?_, cutoMsg_recv tr pub r⟩)
  have hc := cuto_act_eval tr pub r
  rw [ha] at hc
  rw [rowMsgs_one cuto_recv_filter]
  split
  · exact List.mem_singleton_self _
  · rename_i h; exact absurd hc h

/-- **The out-boundary block has `FinSplit`'s shape.** -/
theorem seg_finSplit : FinSplit tr pub (finS tr pub) := by
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
      obtain ⟨b0, b1, -, -⟩ := drop_row H hr
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

#print axioms seg_occ_bits
#print axioms seg_hst
#print axioms seg_hch
#print axioms seg_finSplit
#print axioms seg_cuto_in_fin
#print axioms seg_initS_tp
end WasmBase
