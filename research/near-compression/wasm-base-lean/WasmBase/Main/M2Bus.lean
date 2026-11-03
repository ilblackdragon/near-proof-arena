import WasmBase.Main.M2Dispatch
import WasmBase.Main.SoundHost
/-!
# WasmBase.Main.M2Bus — the STATE/CH bus decomposition of `wasmBaseM2Air`

(header: see the end of the development)
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The table split -/

/-- Every bus of the M2 AIR is the base AIR's plus the parts of tables 22–29. -/
theorem m2_msgs_air (nloc ngl : Nat) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) :
    msgs (wasmBaseM2Air nloc ngl) tr pub b s =
      msgs (wasmBaseAir nloc ngl) tr pub b s ++
      (part HostR.table tr pub 22 b s ++ (part HostO.table tr pub 23 b s ++
        (part HostTab.table tr pub 24 b s ++ (part HostB.table tr pub 25 b s ++
        (part IfC.table tr pub 26 b s ++ (part RegC.table tr pub 27 b s ++
        (part Conv.table tr pub 28 b s ++ part Unreach.table tr pub 29 b s))))))) := by
  rw [msgs_flatMap, msgs_flatMap]
  have e : (wasmBaseM2Air nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [HostR.table, HostO.table, HostTab.table, HostB.table,
        IfC.table, RegC.table, Conv.table, Unreach.table] := rfl
  rw [e, List.zipIdx_append]
  simp only [List.flatMap_append, List.length_map, air_len, Nat.zero_add, part, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.zipIdx_cons, Nat.reduceAdd]
  rw [show ([].zipIdx 30 : List (Table × Nat)) = [] from rfl]
  simp only [List.flatMap_nil, List.append_nil]

/-! ## HOST' is HOST on the STATE and CH buses -/

theorem hostR_filter_eq (b : Nat) (s : Bool) (hb : b ≠ busRegRd) :
    HostR.table.inters.filter (fun i => i.bus = b ∧ i.send = s) =
      Host.table.inters.filter (fun i => i.bus = b ∧ i.send = s) := by
  simp only [HostR.table, HostR.inters, List.filter_append, List.filter_cons, List.filter_nil]
  rw [if_neg (by simp only [decide_eq_true_eq, not_and]; intro h; exact absurd h.symm hb)]
  rw [List.append_nil]; rfl

theorem hostR_rowMsgs (tr : Trace) (pub : List F) (t r b : Nat) (s : Bool) (hb : b ≠ busRegRd) :
    rowMsgs HostR.table tr pub t r b s = rowMsgs Host.table tr pub t r b s := by
  rw [rowMsgs_eq, rowMsgs_eq, hostR_filter_eq b s hb]

theorem hostR_part (tr : Trace) (pub : List F) (b : Nat) (s : Bool) (hb : b ≠ busRegRd) :
    part HostR.table tr pub 22 b s = part Host.table tr pub 22 b s := by
  unfold part
  exact flatMap_congr_on _ _ _ (fun r _ => hostR_rowMsgs tr pub 22 r b s hb)

theorem hostR_rowAct (tr : Trace) (pub : List F) (r : Nat) :
    rowAct HostR.table tr pub 22 r ↔ rowAct Host.table tr pub 22 r := Iff.rfl

theorem busState_ne_regRd : busState ≠ busRegRd := by decide
theorem busStk_ne_regRd : busStk ≠ busRegRd := by decide

/-! ## Tables without STATE (or CH) traffic -/

theorem part_nil_of_filter {T : Table} {tr : Trace} {pub : List F} {t b : Nat} {s : Bool}
    (h : T.inters.filter (fun i => i.bus = b ∧ i.send = s) = []) : part T tr pub t b s = [] := by
  unfold part; rw [List.flatMap_eq_nil_iff]; intro r _
  rw [rowMsgs_eq, h]; rfl

theorem m2_env_nil (tr : Trace) (pub : List F) (b : Nat) (s : Bool) (hb : b = busState ∨ b = busStk) :
    part HostO.table tr pub 23 b s = [] ∧ part HostTab.table tr pub 24 b s = [] := by
  refine ⟨part_nil_of_filter ?_, part_nil_of_filter ?_⟩ <;>
    rcases hb with rfl | rfl <;> cases s <;> decide

theorem m2_state_nil (tr : Trace) (pub : List F) (s : Bool) :
    part HostB.table tr pub 25 busState s = [] ∧ part RegC.table tr pub 27 busState s = [] := by
  refine ⟨part_nil_of_filter ?_, part_nil_of_filter ?_⟩ <;> cases s <;> decide

/-! ## Single-flag chips (IF, CONV, UNREACH): every STATE/CH count is the STATE-receive count

`UniformSC T` says (decidably) that each STATE/CH interaction of `T` is counted by the expression
that counts `T`'s first interaction (its STATE receive).  Then an inactive row (`¬ rowAct`, i.e. that
count is not 1) emits nothing on STATE or CH, with no constraint needed. -/

def UniformSC (T : Table) : Bool :=
  T.inters.all fun i => decide (i.bus ≠ busState ∧ i.bus ≠ busStk) ||
    decide (i.count = (T.inters.getD 0 default).count)

theorem ifc_uniform : UniformSC IfC.table = true := by decide
theorem conv_uniform : UniformSC Conv.table = true := by decide
theorem unreach_uniform : UniformSC Unreach.table = true := by decide

theorem uniform_inactive_nil {T : Table} (hU : UniformSC T = true) {tr : Trace} {pub : List F}
    {t r : Nat} (hna : ¬ rowAct T tr pub t r) (b : Nat) (hb : b = busState ∨ b = busStk) (s : Bool) :
    rowMsgs T tr pub t r b s = [] := by
  rw [rowMsgs_eq, List.filterMap_eq_nil_iff]
  intro i hi
  rw [List.mem_filter] at hi
  have hc := List.all_eq_true.mp hU i hi.1
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
  have hib : i.bus = b := by simp only [decide_eq_true_eq] at hi; exact hi.2.1
  rcases hc with hc | hc
  · exfalso; rcases hb with rfl | rfl
    · exact hc.1 hib
    · exact hc.2 hib
  · rw [hc]; unfold rowAct at hna; simp only [hna, ite_false]

/-- The STATE shape of a chip: one receive (interaction 0), one send (interaction 1), same count. -/
structure StateShape (T : Table) : Prop where
  f : T.inters.filter (fun i => i.bus = busState ∧ i.send = false) = [T.inters.getD 0 default]
  t : T.inters.filter (fun i => i.bus = busState ∧ i.send = true) = [T.inters.getD 1 default]
  c : (T.inters.getD 1 default).count = (T.inters.getD 0 default).count

theorem ifc_shape : StateShape IfC.table := ⟨by decide, by decide, by decide⟩
theorem conv_shape : StateShape Conv.table := ⟨by decide, by decide, by decide⟩
theorem unreach_shape : StateShape Unreach.table := ⟨by decide, by decide, by decide⟩

theorem shape_state_true {T : Table} (hS : StateShape T) (tr : Trace) (pub : List F) (t r : Nat) :
    rowMsgs T tr pub t r busState true =
      if rowAct T tr pub t r then [rowOut T tr pub t r] else [] := by
  rw [rowMsgs_eq, hS.t]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [hS.c]
  unfold rowAct rowOut
  split <;> simp_all

theorem shape_state_false {T : Table} (hS : StateShape T) (tr : Trace) (pub : List F) (t r : Nat) :
    rowMsgs T tr pub t r busState false =
      if rowAct T tr pub t r then [rowIn T tr pub t r] else [] := by
  rw [rowMsgs_eq, hS.f]
  simp only [List.filterMap_cons, List.filterMap_nil]
  unfold rowAct rowIn
  split <;> simp_all

/-- The active rows of table `t` read as `T`. -/
def actRowsT (T : Table) (tr : Trace) (pub : List F) (t : Nat) : List Nat :=
  (List.range (tr.height t)).filter fun r => decide (rowAct T tr pub t r)

theorem shape_part_true {T : Table} (hS : StateShape T) (tr : Trace) (pub : List F) (t : Nat) :
    part T tr pub t busState true = (actRowsT T tr pub t).map (rowOut T tr pub t) := by
  unfold part
  rw [show (fun r => rowMsgs T tr pub t r busState true) =
    (fun r => if rowAct T tr pub t r then [rowOut T tr pub t r] else []) from
    funext (shape_state_true hS tr pub t), flatMap_ite_single]
  rfl

theorem shape_part_false {T : Table} (hS : StateShape T) (tr : Trace) (pub : List F) (t : Nat) :
    part T tr pub t busState false = (actRowsT T tr pub t).map (rowIn T tr pub t) := by
  unfold part
  rw [show (fun r => rowMsgs T tr pub t r busState false) =
    (fun r => if rowAct T tr pub t r then [rowIn T tr pub t r] else []) from
    funext (shape_state_false hS tr pub t), flatMap_ite_single]
  rfl

theorem uniform_part_ch {T : Table} (hU : UniformSC T = true) (tr : Trace) (pub : List F) (t : Nat)
    (s : Bool) :
    part T tr pub t busStk s = (actRowsT T tr pub t).flatMap fun r => rowMsgs T tr pub t r busStk s := by
  unfold part
  rw [actRowsT, ← flatMap_filter_of_nil]
  intro r _ hna
  exact uniform_inactive_nil hU hna busStk (Or.inr rfl) s

/-! ## Count bits on STATE and CH (both directions) -/

theorem m2_t22 (nloc ngl : Nat) :
    (wasmBaseM2Air nloc ngl).tables[22]'(by rw [m2_air_len]; decide) = HostR.table := by
  simp [wasmBaseM2Air, wasmBaseAir]
theorem m2_t25 (nloc ngl : Nat) :
    (wasmBaseM2Air nloc ngl).tables[25]'(by rw [m2_air_len]; decide) = HostB.table := by
  simp [wasmBaseM2Air, wasmBaseAir]
theorem m2_t27 (nloc ngl : Nat) :
    (wasmBaseM2Air nloc ngl).tables[27]'(by rw [m2_air_len]; decide) = RegC.table := by
  simp [wasmBaseM2Air, wasmBaseAir]

/-- The HOST constraints hold on table 22 of an M2 trace (HOST' extends them). -/
theorem m2_host_con {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22) :
    ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0 := by
  intro e he
  have h := table_constr H (t := 22) (by rw [m2_air_len]; decide) hr e
  rw [m2_t22] at h
  exact h (HostR.constraints_prefix.subset he)

/-- Each of HOST's STATE/CH counts is a bit, from the HOST constraints alone. -/
theorem host_inter_bound_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ Host.table.constraints, e.eval (natRow (rowNat tr 22 r) (tr.row pub 22 r)) = 0) :
    ∀ i ∈ Host.table.inters, (i.bus = busState ∨ i.bus = busStk) →
      (i.count.eval (tr.row pub 22 r)).toNat ≤ 1 := by
  intro i hi hb
  have hmem : i ∈ Host.table.inters.filter (fun j => j.bus = busState ∨ j.bus = busStk) :=
    List.mem_filter.mpr ⟨hi, by simpa using hb⟩
  have hcount : i.count ∈ (Expr.col Host.act :: Expr.col Host.act ::
      (Host.argRange.map (fun j => Expr.col (Host.pf j)) ++ [Expr.col Host.nres])) := by
    have := List.mem_map_of_mem (f := (·.count)) hmem
    rwa [host_state_ch_count_list] at this
  have hact : rowNat tr 22 r Host.act ≤ 1 := by
    show rowNat tr 22 r 5 ≤ 1
    have hb := hcon Host.cAct host_cAct_mem
    simp only [Host.cAct, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
      Expr.eval_ofNat', Host.act, natRow] at hb
    have hb' : (rowNat tr 22 r 5 : F) * ((rowNat tr 22 r 5 : F) - 1) = 0 := hb
    rcases bool_nat (rowNat_lt tr 22 r 5) hb' with h | h <;> omega
  have hpf : ∀ j, j < Host.nArgs → rowNat tr 22 r (Host.pf j) ≤ 1 := by
    intro j hj
    show rowNat tr 22 r (19 + j) ≤ 1
    have hb := hcon (Host.cP j) (host_cP_mem j hj)
    simp only [Host.cP, Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
      Expr.eval_ofNat', Host.pf, natRow] at hb
    rcases bool_nat (rowNat_lt tr 22 r (19 + j)) hb with h | h <;> omega
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_singleton,
    Host.argRange, List.mem_range, or_false, List.not_mem_nil] at hcount
  rcases hcount with h | h | ⟨j, hj, h⟩ | h
  · rw [h, col_eval]; exact hact
  · rw [h, col_eval]; exact hact
  · rw [← h, col_eval]; exact hpf j (by simpa [Host.argRange] using hj)
  · rw [h, col_eval]; rcases host_nres_bit_of hcon with h' | h' <;> omega

/-- Every STATE/CH count of `T` is a `BitE bs` expression. -/
def SCBitOk (T : Table) (bs : List Expr) : Bool :=
  BitsOk T bs && T.inters.all (fun i => decide (i.bus ≠ busState ∧ i.bus ≠ busStk) || BitE bs i.count)

theorem sc_le_of_ok {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {t : Nat}
    (ht : t < A.tables.length) {bs : List Expr} (hok : SCBitOk (A.tables[t]'ht) bs = true) {r : Nat}
    (hr : r < tr.height t) {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters)
    (hb : i.bus = busState ∨ i.bus = busStk) :
    (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  simp only [SCBitOk, Bool.and_eq_true] at hok
  obtain ⟨hbits, hcnt⟩ := hok
  apply toNat_le_one_of_bit
  refine bitE_sound bs _ ?_ i.count ?_
  · intro b' hb'
    have hc := List.all_eq_true.mp hbits b' hb'
    obtain ⟨c, hcm, hce⟩ := List.any_eq_true.mp hc
    rw [decide_eq_true_eq] at hce
    subst hce
    have h0 := H.constr t ht r hr _ hcm
    simp only [Chips.bool, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', cast_one] at h0
    exact bool_cases h0
  · have hc := List.all_eq_true.mp hcnt i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · exfalso; rcases hb with h | h
      · exact hc.1 h
      · exact hc.2 h
    · exact hc

theorem hostB_scok : SCBitOk HostB.table [v HostB.act, v HostB.dir, v HostB.reg] = true := by
  decide +kernel
theorem ifc_scok : SCBitOk IfC.table [v IfC.fIf] = true := by decide +kernel
theorem regc_scok :
    SCBitOk RegC.table [v Reg.act, v Reg.kind, v Reg.fresh, v RegW.wr, v RegC.clr] = true := by
  decide +kernel
theorem conv_scok : SCBitOk Conv.table [Conv.act, v Conv.fExtS] = true := by decide +kernel
theorem unreach_scok : SCBitOk Unreach.table [v Unreach.act] = true := by decide +kernel
theorem hostO_scok : SCBitOk HostO.table [] = true := by decide +kernel
theorem hostTab_scok : SCBitOk HostTab.table [] = true := by decide +kernel

/-- **Every STATE/CH occurrence of an M2 trace has count ≤ 1** (both directions). -/
theorem m2_occ_bits {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, (o.1 = busState ∨ o.1 = busStk) → o.2.2.2 ≤ 1 := by
  intro o ho hk
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hk ⊢
  rcases Nat.lt_or_ge t 22 with h22 | h22
  · have HC := m2_holdsC H
    have CF := chipFactsC X HC
    have hocc : (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)),
        (i.count.eval (tr.row pub t r)).toNat) ∈ occs (wasmBaseAir nloc ngl) tr pub :=
      mem_occs.mpr ⟨t, by rw [air_len]; exact h22, r, hr, i,
        by rw [← m2_get_base nloc ngl t h22]; exact hi, rfl⟩
    exact occ_bits_of hpub CF.counts (fun t ht r hr => table_constrC HC ht hr) _ hocc (Or.inr hk)
  · have hlt : t < 30 := by rw [m2_air_len] at ht; exact ht
    rcases (show t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [m2_t22] at hi
      have hb' : i.bus ≠ busRegRd := by
        rcases hk with h | h <;> rw [h] <;> decide
      have hi' : i ∈ Host.table.inters := by
        simp only [HostR.table, HostR.inters, List.mem_append, List.mem_singleton] at hi
        rcases hi with h | h
        · exact h
        · exact absurd (by rw [h]) hb'
      exact host_inter_bound_of (m2_host_con H hr) i hi' hk
    · exact sc_le_of_ok H ht (by simp [wasmBaseM2Air, wasmBaseAir]; exact hostO_scok) hr hi hk
    · exact sc_le_of_ok H ht (by simp [wasmBaseM2Air, wasmBaseAir]; exact hostTab_scok) hr hi hk
    · exact sc_le_of_ok H ht (by rw [m2_t25]; exact hostB_scok) hr hi hk
    · exact sc_le_of_ok H ht (by rw [m2_t26]; exact ifc_scok) hr hi hk
    · exact sc_le_of_ok H ht (by rw [m2_t27]; exact regc_scok) hr hi hk
    · exact sc_le_of_ok H ht (by rw [m2_t28]; exact conv_scok) hr hi hk
    · exact sc_le_of_ok H ht (by rw [m2_t29]; exact unreach_scok) hr hi hk

/-- **The STATE and CH buses of an M2 trace are permutations.** -/
theorem m2_msgs_perm {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) (b : Nat)
    (hb : b = busState ∨ b = busStk) :
    (msgs (wasmBaseM2Air nloc ngl) tr pub b true).Perm (msgs (wasmBaseM2Air nloc ngl) tr pub b false) :=
  msgs_perm H b (fun o ho hk => m2_occ_bits H hpub o ho (by rw [hk]; exact hb))

/-! ## The base tables' STATE/CH blocks, from the row constraints only

`Exec.msgs_state`/`msgs_ch` take the base AIR's `Holds` but use it only for `1 ≤ height 0`; these are
the same statements with that fact as the premise (an M2 trace's base tables are not a base trace). -/

theorem msgs_state_of {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (h0 : 1 ≤ tr.height 0) (hpub : PubOK X nloc ncode pub) :
    msgs (wasmBaseAir nloc ncode) tr pub busState true =
      stMsg 0 1 0 0 0 0 :: (actList tr pub).map (fun ρ => rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) ∧
    msgs (wasmBaseAir nloc ncode) tr pub busState false =
      [tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0, pub.getD Boundary.pubStatus 0,
        tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
        (actList tr pub).map (fun ρ => rowIn (chipT ρ.1) tr pub ρ.1 ρ.2) := by
  obtain ⟨n1, n2, n1', nd1, nf1⟩ := part_fixed tr pub busState (Or.inl rfl) true
  obtain ⟨n3, n4, n3', nd2, nf2⟩ := part_fixed tr pub busState (Or.inl rfl) false
  have d1 := part_drain_nil tr pub busState true (Or.inl rfl)
  have d2 := part_drain_nil tr pub busState false (Or.inl rfl)
  have m1 := part_meminit_nil tr pub busState true (Or.inl rfl)
  have m2 := part_meminit_nil tr pub busState false (Or.inl rfl)
  constructor
  · rw [msgs_air, n1, n2, n1', d1, m1, nd1, nf1, actList_map]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busState true = [stMsg 0 1 0 0 0 0] := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState true) =
        (fun r => if r = 0 then [stMsg 0 1 0 0 0 0] else []) from funext fun r => (bnd_msgs hpub r).1]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_true 1 (by omega) (by omega), chip_part_true 2 (by omega) (by omega), chip_part_true 3 (by omega) (by omega), chip_part_true 4 (by omega) (by omega), chip_part_true 5 (by omega) (by omega), chip_part_true 6 (by omega) (by omega), chip_part_true 7 (by omega) (by omega), chip_part_true 8 (by omega) (by omega), chip_part_true 9 (by omega) (by omega), chip_part_true 10 (by omega) (by omega), chip_part_true 11 (by omega) (by omega), chip_part_true 12 (by omega) (by omega), chip_part_true 13 (by omega) (by omega), chip_part_true 14 (by omega) (by omega), List.append_nil, List.cons_append, List.nil_append]
  · rw [msgs_air, n3, n4, n3', d2, m2, nd2, nf2, actList_map]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busState false =
        [[tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
          pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf]] := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busState false) =
        (fun r => if r = 0 then [[tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
          pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf]] else [])
          from funext fun r => (bnd_msgs hpub r).2.1]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_false 1 (by omega) (by omega), chip_part_false 2 (by omega) (by omega), chip_part_false 3 (by omega) (by omega), chip_part_false 4 (by omega) (by omega), chip_part_false 5 (by omega) (by omega), chip_part_false 6 (by omega) (by omega), chip_part_false 7 (by omega) (by omega), chip_part_false 8 (by omega) (by omega), chip_part_false 9 (by omega) (by omega), chip_part_false 10 (by omega) (by omega), chip_part_false 11 (by omega) (by omega), chip_part_false 12 (by omega) (by omega), chip_part_false 13 (by omega) (by omega), chip_part_false 14 (by omega) (by omega), List.append_nil, List.cons_append, List.nil_append]

theorem msgs_ch_of {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace}
    (h0 : 1 ≤ tr.height 0) (hpub : PubOK X nloc ncode pub) (CF : ChipFacts X nloc ncode pub tr) :
    msgs (wasmBaseAir nloc ncode) tr pub busStk true =
      initRaw nloc pub ++ (globRaw nloc ncode pub ++ (budRaw nloc ncode pub ++ (actList tr pub).flatMap (fun ρ => rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk true) ++
        memRaw tr pub)) ∧
    msgs (wasmBaseAir nloc ncode) tr pub busStk false =
      (((if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then [resRaw pub tr] else []) ++
        finRaw nloc tr) ++
        (actList tr pub).flatMap (fun ρ => rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk false)) ++ drainRaw tr pub := by
  obtain ⟨n1, n2, n1', nd1, nf1⟩ := part_fixed tr pub busStk (Or.inr rfl) true
  obtain ⟨n3, n4, n3', nd2, nf2⟩ := part_fixed tr pub busStk (Or.inr rfl) false
  have d1 := part_drain_nil tr pub busStk true (Or.inr rfl)
  have m2 := part_meminit_nil tr pub busStk false (Or.inr rfl)
  constructor
  · rw [msgs_air, n1, n2, n1', d1, nd1, nf1, actList_flatMap]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busStk true =
        initRaw nloc pub ++ globRaw nloc ncode pub ++ budRaw nloc ncode pub := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk true) =
        (fun r => if r = 0 then initRaw nloc pub ++ globRaw nloc ncode pub ++ budRaw nloc ncode pub else []) from
          funext fun r => (bnd_msgs hpub r).2.2.1]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_ch CF 1 (by omega) (by omega), chip_part_ch CF 2 (by omega) (by omega), chip_part_ch CF 3 (by omega) (by omega), chip_part_ch CF 4 (by omega) (by omega), chip_part_ch CF 5 (by omega) (by omega), chip_part_ch CF 6 (by omega) (by omega), chip_part_ch CF 7 (by omega) (by omega), chip_part_ch CF 8 (by omega) (by omega), chip_part_ch CF 9 (by omega) (by omega), chip_part_ch CF 10 (by omega) (by omega), chip_part_ch CF 11 (by omega) (by omega), chip_part_ch CF 12 (by omega) (by omega), chip_part_ch CF 13 (by omega) (by omega), chip_part_ch CF 14 (by omega) (by omega), List.append_nil, List.nil_append, memRaw, List.append_assoc]
  · rw [msgs_air, n3, n4, n3', m2, nd2, nf2, actList_flatMap]
    have hb : part (Boundary.table nloc ncode) tr pub 0 busStk false =
        (if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then [resRaw pub tr] else []) ++
          finRaw nloc tr := by
      unfold part
      rw [show (fun r => rowMsgs (Boundary.table nloc ncode) tr pub 0 r busStk false) =
        (fun r => if r = 0 then (if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then
          [resRaw pub tr] else []) ++ finRaw nloc tr else []) from funext fun r => (bnd_msgs hpub r).2.2.2]
      exact flatMap_range_first _ h0 _
    rw [hb]
    simp only [part, chip_part_ch CF 1 (by omega) (by omega), chip_part_ch CF 2 (by omega) (by omega), chip_part_ch CF 3 (by omega) (by omega), chip_part_ch CF 4 (by omega) (by omega), chip_part_ch CF 5 (by omega) (by omega), chip_part_ch CF 6 (by omega) (by omega), chip_part_ch CF 7 (by omega) (by omega), chip_part_ch CF 8 (by omega) (by omega), chip_part_ch CF 9 (by omega) (by omega), chip_part_ch CF 10 (by omega) (by omega), chip_part_ch CF 11 (by omega) (by omega), chip_part_ch CF 12 (by omega) (by omega), chip_part_ch CF 13 (by omega) (by omega), chip_part_ch CF 14 (by omega) (by omega), List.append_nil, List.nil_append, drainRaw, List.append_assoc]

/-! ## REG-C on the CH bus: the net messages and the clear pairs

A REG-C row's CH traffic is REG' 's (`RegW.inters`) plus, on a **clear** row (`clr = 1`), two extra
receives of exactly the space-6 messages the row itself sends at `ts` (`regc_clear_cancels`).  We
split each row as

* `regNetProd` / `regNetCons` — its *net* traffic: REG' 's receives, and REG' 's sends unless the row
  is a clear row (whose sends are all cancelled);
* `regClr` — the clear receives,

so that `rowProd = regNetProd ++ regClr` and `rowCons = regNetCons ++ regClr` (`regc_prod_split`,
`regc_cons_split`).  The clear block cancels from the CH balance; only the net traffic is folded into
host calls.  This matters: a clear receive has `tp = ts`, so if it were kept as a consumed message of
the host step, the step's `consT` (every consumed message is strictly older) would fail on every
honest refill. -/

/-- REG-C's clear receives, as a table of their own (for the `rowCons` accessor). -/
def RegClrT : Table := ⟨"REGCLR", RegC.cols, [], RegC.newInters⟩

/-- The clear receives of REG-C row `r`. -/
def regClr (tr : Trace) (pub : List F) (r : Nat) : List Msg := rowCons RegClrT tr pub 27 r
/-- The net consumed CH messages of REG-C row `r`: REG' 's receives. -/
def regNetCons (tr : Trace) (pub : List F) (r : Nat) : List Msg := rowCons RegW.table tr pub 27 r
/-- The net produced CH messages of REG-C row `r`: REG' 's sends, none on a clear row. -/
def regNetProd (tr : Trace) (pub : List F) (r : Nat) : List Msg :=
  if rowNat tr 27 r RegC.clr = 1 then [] else rowProd RegW.table tr pub 27 r

theorem regc_cons_split (tr : Trace) (pub : List F) (r : Nat) :
    rowCons RegC.table tr pub 27 r = regNetCons tr pub r ++ regClr tr pub r := by
  unfold regNetCons regClr rowCons
  simp only [rowMsgs_eq]
  show (((RegW.inters ++ RegC.newInters).filter _).filterMap _).map _ = _
  rw [List.filter_append, List.filterMap_append, List.map_append]; rfl

theorem regc_prod_eq (tr : Trace) (pub : List F) (r : Nat) :
    rowProd RegC.table tr pub 27 r = rowProd RegW.table tr pub 27 r := by
  unfold rowProd
  simp only [rowMsgs_eq]
  show (((RegW.inters ++ RegC.newInters).filter _).filterMap _).map _ = _
  rw [List.filter_append]
  rw [show RegC.newInters.filter (fun i => i.bus = busStk ∧ i.send = true) = [] by decide,
    List.append_nil]; rfl

open Reg in
theorem regw_stk_send :
    RegW.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
      [chSend (Expr.c Register.space) byteSlotE (Expr.c Register.byteTag) [v bv, 0, 0, 0] (v ts)
         (v act * isB),
       chSend (Expr.c Register.space) lenSlotE (Expr.c Register.lenTag) [v blen, 0, 0, 0] (v ts)
         (v act * isL),
       chSend 3 RegW.addr 0 [v bv, 0, 0, 0] (v ts) RegW.wcnt] := by decide

open Reg in
theorem regw_stk_recv :
    RegW.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
      [chRecv (Expr.c Register.space) byteSlotE (Expr.c Register.byteTag) [v bv, 0, 0, 0] (v tp)
         (v act * isB * v fresh),
       chRecv (Expr.c Register.space) lenSlotE (Expr.c Register.lenTag) [v blen, 0, 0, 0] (v tp)
         (v act * isL * v fresh),
       chRecv 3 RegW.addr 0 [v RegW.ob, 0, 0, 0] (v RegW.mtp) RegW.wcnt] := by decide

theorem regclr_stk_recv :
    RegC.newInters.filter (fun i => i.bus = busStk ∧ i.send = false) = RegC.newInters := by decide

/-- The REG-C constraints on a row of table 27 of an M2 trace. -/
theorem m2_regc_con {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 27) :
    ∀ e ∈ RegC.table.constraints, e.eval (natRow (rowNat tr 27 r) (tr.row pub 27 r)) = 0 := by
  intro e he
  have h := table_constr H (t := 27) (by rw [m2_air_len]; decide) hr e
  rw [m2_t27] at h
  exact h he

theorem toNat_zero' : Fp.toNat (0 : F) = 0 := rfl

theorem regc_cClr_mem : RegC.cClr ∈ RegC.table.constraints :=
  List.mem_append_right _ List.mem_cons_self
theorem regc_cClrWr_mem : RegC.cClrWr ∈ RegC.table.constraints :=
  List.mem_append_right _ (by simp [RegC.newConstraints])
theorem regc_cAct_mem : Reg.cAct ∈ RegC.table.constraints :=
  List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)

theorem regc_bool_of {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ RegC.table.constraints, e.eval (natRow (rowNat tr 27 r) (tr.row pub 27 r)) = 0)
    {c : Nat} (hc : Chips.bool (v c) ∈ RegC.table.constraints) :
    rowNat tr 27 r c = 0 ∨ rowNat tr 27 r c = 1 := by
  have h := hcon _ hc
  simp only [Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat',
    natRow] at h
  exact bool_nat (rowNat_lt tr 27 r c) h

theorem regc_col_eval (tr : Trace) (pub : List F) (r c : Nat) :
    (v c).eval (tr.row pub 27 r) = ((rowNat tr 27 r c : Nat) : F) := by
  simp only [Chips.v, Expr.eval_col, Trace.row, cell_cast]

/-- **The produced split.**  On every row satisfying the REG-C constraints,
`rowProd = regNetProd ++ regClr`. -/
theorem regc_prod_split {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ RegC.table.constraints, e.eval (natRow (rowNat tr 27 r) (tr.row pub 27 r)) = 0) :
    rowProd RegC.table tr pub 27 r = regNetProd tr pub r ++ regClr tr pub r := by
  rw [regc_prod_eq]
  have hclr := regc_bool_of hcon (c := RegC.clr) regc_cClr_mem
  unfold regNetProd regClr rowProd rowCons
  simp only [rowMsgs_eq]
  rw [show RegW.table.inters = RegW.inters from rfl, regw_stk_send]
  show _ = _ ++ ((RegC.newInters.filter _).filterMap _).map _
  rw [regclr_stk_recv]
  rcases hclr with h0 | h1
  · rw [if_neg (by omega)]
    have hz : ∀ e : Expr, (e * v RegC.clr).eval (tr.row pub 27 r) = 0 := by
      intro e; rw [Expr.eval_mul', regc_col_eval, h0]; exact Lean.Grind.Semiring.mul_zero _
    simp only [RegC.newInters, chRecv, List.filterMap_cons, List.filterMap_nil, hz, toNat_zero']
    simp
  · rw [if_pos h1, List.nil_append]
    -- `clr = 1` forces `wr = 0` (`cClrWr`)
    have hw : rowNat tr 27 r RegW.wr = 0 := by
      have h := hcon RegC.cClrWr regc_cClrWr_mem
      simp only [RegC.cClrWr, Chips.v, Expr.eval_mul', Expr.eval_col, natRow] at h
      rw [h1, one_cast, Lean.Grind.Semiring.one_mul] at h
      exact (cast_inj_iff (rowNat_lt tr 27 r RegW.wr) (by decide : (0 : Nat) < P)).mp
        (h.trans zero_cast.symm)
    have hwc : RegW.wcnt.eval (tr.row pub 27 r) = 0 := by
      simp only [RegW.wcnt, Expr.eval_mul', regc_col_eval, hw]
      exact Lean.Grind.Semiring.mul_zero _
    have h1' : ∀ e : Expr, (e * v RegC.clr).eval (tr.row pub 27 r) = e.eval (tr.row pub 27 r) := by
      intro e; rw [Expr.eval_mul', regc_col_eval, h1]; exact Lean.Grind.Semiring.mul_one _
    simp only [RegC.newInters, chRecv, chSend, List.filterMap_cons, List.filterMap_nil, hwc, h1',
      toNat_zero']
    simp

/-- **An inactive REG-C row has no net CH traffic.** -/
theorem regc_inactive_nil {pub : List F} {tr : Trace} {r : Nat}
    (hcon : ∀ e ∈ RegC.table.constraints, e.eval (natRow (rowNat tr 27 r) (tr.row pub 27 r)) = 0)
    (hna : rowNat tr 27 r Reg.act ≠ 1) :
    regNetProd tr pub r = [] ∧ regNetCons tr pub r = [] := by
  have ha : rowNat tr 27 r Reg.act = 0 := by
    rcases regc_bool_of hcon (c := Reg.act) regc_cAct_mem with h | h
    · exact h
    · exact absurd h hna
  have hz : ∀ e : Expr, (v Reg.act * e).eval (tr.row pub 27 r) = 0 := by
    intro e; rw [Expr.eval_mul', regc_col_eval, ha]; exact Lean.Grind.Semiring.zero_mul _
  have hz2 : ∀ e e' : Expr, (v Reg.act * e * e').eval (tr.row pub 27 r) = 0 := by
    intro e e'; rw [Expr.eval_mul', hz]; exact Lean.Grind.Semiring.zero_mul _
  have hwc : RegW.wcnt.eval (tr.row pub 27 r) = 0 := hz2 _ _
  constructor
  · unfold regNetProd
    split
    · rfl
    · unfold rowProd
      rw [rowMsgs_eq, show RegW.table.inters = RegW.inters from rfl, regw_stk_send]
      simp only [chSend, List.filterMap_cons, List.filterMap_nil, hz, hwc, toNat_zero']
      simp
  · unfold regNetCons rowCons
    rw [rowMsgs_eq, show RegW.table.inters = RegW.inters from rfl, regw_stk_recv]
    simp only [chRecv, List.filterMap_cons, List.filterMap_nil, hz2, hwc, toNat_zero']
    simp

/-! ## Grouping non-action rows by host call

`HOSTB` and REG-C rows are not action rows (they never advance STATE time); they belong to the host
call whose `(ts, hid)` they carry.  `key_partition` is the generic fact behind `hostb_partition`
(`Main/MemIOBus`): if every row with traffic carries the key of some call, and the calls' keys are
distinct, then grouping the rows by call is a permutation of the whole table's traffic. -/

theorem key_partition {K β : Type} [DecidableEq K] (calls : List Nat) (hnd : calls.Nodup)
    (keyH : Nat → K) (h : Nat) (keyB : Nat → K) (M : Nat → List β)
    (hlink : ∀ r', r' < h → M r' ≠ [] → ∃ c ∈ calls, keyB r' = keyH c)
    (huniq : ∀ c ∈ calls, ∀ c' ∈ calls, keyH c = keyH c' → c = c') :
    (calls.flatMap fun c =>
        ((List.range h).filter fun r' => decide (keyB r' = keyH c)).flatMap M).Perm
      ((List.range h).flatMap M) := by
  have e1 : (calls.flatMap fun c =>
        ((List.range h).filter fun r' => decide (keyB r' = keyH c)).flatMap M) =
      calls.flatMap (fun c => (List.range h).flatMap
        (fun r' => if decide (keyB r' = keyH c) = true then M r' else [])) := by
    refine flatMap_congr_on _ _ _ (fun c _ => ?_)
    rw [filter_flatMap_ite]
  rw [e1]
  refine (perm_flatMap_swap calls (List.range h)
    (fun c r' => if decide (keyB r' = keyH c) = true then M r' else [])).symm.trans ?_
  refine List.Perm.of_eq (flatMap_congr_on _ _ _ (fun r' hr' => ?_))
  by_cases hM : M r' = []
  · rw [hM]
    exact List.flatMap_eq_nil_iff.mpr (fun c _ => by simp)
  · obtain ⟨c, hc, hk⟩ := hlink r' (List.mem_range.mp hr') hM
    exact flatMap_key_unique calls (fun c => decide (keyB r' = keyH c)) (fun _ => M r') hnd hc
      (fun y hy hp => huniq y hy c hc (by
        simp only [decide_eq_true_eq] at hp; rw [← hp, hk]))
      (by simp only [decide_eq_true_eq]; exact hk)

/-- The key of a host call: its STATE time and host id. -/
def hostKey (tr : Trace) (r : Nat) : Nat × Nat := (rowNat tr 22 r cTs, rowNat tr 22 r Host.hid)
/-- The call key a `HOSTB` row carries. -/
def hostbKey (tr : Trace) (r : Nat) : Nat × Nat := (rowNat tr 25 r HostB.ts, rowNat tr 25 r HostB.hid)
/-- The call key a REG-C row carries. -/
def regKey (tr : Trace) (r : Nat) : Nat × Nat := (rowNat tr 27 r Reg.ts, rowNat tr 27 r Reg.hid)

theorem hostbOf_key (tr : Trace) (pub : List F) (r : Nat) :
    hostbOf tr pub r = (List.range (tr.height 25)).filter fun r' => decide (hostbKey tr r' = hostKey tr r) := by
  unfold hostbOf
  congr 1
  funext r'
  simp only [hostbKey, hostKey, Prod.mk.injEq]

/-- The REG-C rows whose call key is host row `r`'s. -/
def regOf (tr : Trace) (r : Nat) : List Nat :=
  (List.range (tr.height 27)).filter fun r' => decide (regKey tr r' = hostKey tr r)

/-- The net CH messages the REG-C rows of host call `r` produce. -/
def regProdOf (tr : Trace) (pub : List F) (r : Nat) : List Msg := (regOf tr r).flatMap (regNetProd tr pub)
/-- The net CH messages the REG-C rows of host call `r` consume. -/
def regConsOf (tr : Trace) (pub : List F) (r : Nat) : List Msg := (regOf tr r).flatMap (regNetCons tr pub)

/-- **The REG-C grouping premise** (the register analogue of `HostBLinked.linked`): every active
REG-C row carries the `(ts, hid)` key of an active HOST row.  Uniqueness of the HOST keys is
`HostBLinked.unique`.  Like `HostBLinked`, this is a statement about the trace that the bus balance
does not give: REG-C talks to `HOSTB` (bus `busHostB`, fills) and to HOST' (bus `busRegRd`, the
`read_register` memory write) but its `(ts, hid)` columns are not themselves looked up against a
HOST row.  A trace generated from a real run satisfies it (every register group is emitted by the
host call that reads or writes the register). -/
structure RegCLinked (tr : Trace) (pub : List F) : Prop where
  linked : ∀ r', r' < tr.height 27 → rowNat tr 27 r' Reg.act = 1 →
    ∃ r, r < tr.height 22 ∧ rowAct Host.table tr pub 22 r ∧
      rowNat tr 27 r' Reg.ts = rowNat tr 22 r cTs ∧ rowNat tr 27 r' Reg.hid = rowNat tr 22 r Host.hid

theorem hostActRows_eq (tr : Trace) (pub : List F) :
    hostActRows tr pub = (actRowsT Host.table tr pub 22).map (fun r => (22, r)) := rfl

theorem actRowsT_nodup (T : Table) (tr : Trace) (pub : List F) (t : Nat) :
    (actRowsT T tr pub t).Nodup := List.nodup_range.filter _

theorem mem_actRowsT {T : Table} {tr : Trace} {pub : List F} {t r : Nat} :
    r ∈ actRowsT T tr pub t ↔ r < tr.height t ∧ rowAct T tr pub t r := by
  simp only [actRowsT, List.mem_filter, List.mem_range, decide_eq_true_eq]

theorem host_key_uniq {tr : Trace} {pub : List F} (hb : HostBLinked tr pub) :
    ∀ c ∈ actRowsT Host.table tr pub 22, ∀ c' ∈ actRowsT Host.table tr pub 22,
      hostKey tr c = hostKey tr c' → c = c' := by
  intro c hc c' hc' hk
  rw [mem_actRowsT] at hc hc'
  simp only [hostKey, Prod.mk.injEq] at hk
  exact hb.unique c c' hc.1 hc.2 hc'.1 hc'.2 hk.1 hk.2

/-- A `HOSTB` row with CH traffic is active (`memCnt = 1`). -/
theorem hostb_act_of_ne {tr : Trace} {pub : List F} {r : Nat} {s : Bool}
    (h : rowMsgs HostB.table tr pub 25 r busStk s ≠ []) : rowAct HostB.table tr pub 25 r := by
  rw [hostb_rowAct_iff]
  by_cases hne : (HostB.memCnt.eval (tr.row pub 25 r)).toNat = 1
  · exact hne
  exfalso
  apply h
  cases s
  · rw [rowMsgs_eq, hostb_inters_stk.1]
    simp only [List.filterMap_cons, List.filterMap_nil, chRecv, hne, ite_false]
  · rw [rowMsgs_eq, hostb_inters_stk.2]
    simp only [List.filterMap_cons, List.filterMap_nil, chSend, hne, ite_false]

/-- **The `HOSTB` block, grouped by host call** (the M2 form of `hostb_partition`). -/
theorem m2_hostb_partition {tr : Trace} {pub : List F} (hb : HostBLinked tr pub) (s : Bool) :
    ((hostActRows tr pub).flatMap (fun ρ => (hostbOf tr pub ρ.2).flatMap
        fun r' => (rowMsgs HostB.table tr pub 25 r' busStk s).map decMsg)).Perm
      ((part HostB.table tr pub 25 busStk s).map decMsg) := by
  rw [hostActRows_eq, List.flatMap_map]
  simp only [hostbOf_key]
  unfold part
  rw [List.map_flatMap]
  refine key_partition _ (actRowsT_nodup _ _ _ _) (hostKey tr) _ (hostbKey tr) _ ?_ (host_key_uniq hb)
  intro r' hr' hM
  have hne : rowMsgs HostB.table tr pub 25 r' busStk s ≠ [] := by
    intro h0; apply hM; rw [h0]; rfl
  obtain ⟨r, hr, hra, hts, hhid⟩ := hb.linked r' hr' (hostb_act_of_ne hne)
  exact ⟨r, mem_actRowsT.mpr ⟨hr, hra⟩, by simp only [hostbKey, hostKey, hts, hhid]⟩

/-- **The REG-C net block, grouped by host call.** -/
theorem m2_reg_partition {tr : Trace} {pub : List F} (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    (M : Nat → List Msg) (hM0 : ∀ r', r' < tr.height 27 → rowNat tr 27 r' Reg.act ≠ 1 → M r' = []) :
    ((hostActRows tr pub).flatMap (fun ρ => (regOf tr ρ.2).flatMap M)).Perm
      ((List.range (tr.height 27)).flatMap M) := by
  rw [hostActRows_eq, List.flatMap_map]
  refine key_partition _ (actRowsT_nodup _ _ _ _) (hostKey tr) _ (regKey tr) _ ?_ (host_key_uniq hb)
  intro r' hr' hM
  have ha : rowNat tr 27 r' Reg.act = 1 := by
    by_cases hna : rowNat tr 27 r' Reg.act = 1
    · exact hna
    · exact absurd (hM0 r' hr' hna) hM
  obtain ⟨r, hr, hra, hts, hhid⟩ := hg.linked r' hr' ha
  exact ⟨r, mem_actRowsT.mpr ⟨hr, hra⟩, by simp only [regKey, hostKey, hts, hhid]⟩

end WasmBase
