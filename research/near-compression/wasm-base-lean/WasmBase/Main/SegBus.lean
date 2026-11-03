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

#print axioms seg_occ_bits
#print axioms seg_hst
end WasmBase
