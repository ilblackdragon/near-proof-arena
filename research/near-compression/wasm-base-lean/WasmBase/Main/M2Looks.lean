import WasmBase.Main.RegSendM2
import WasmBase.Main.M2Rows
/-!
# WasmBase.Main.M2Looks — the lookups of a `wasmBaseM2Air` trace, as the base row lemmas use them

The base row lemmas (`Main/Row*.lean`) take `HoldsC (wasmBaseAir …)` (the base tables' row
constraints) and `Looks X …` (the FETCH / R16 / BYTE / FUNC answers of the base tables'
occurrences).  This file derives both from `Holds (wasmBaseM2Air …)`, for the M2 context
`X.toCtx`:

* `m2_holdsC`: tables 0–21 of the M2 AIR are the base AIR's, so their constraints hold;
* `bus_le_of_ok` / `hsend_bus_of_tail`: the per-bus send bound (`RegSendM2.lean`'s R16 argument,
  for any bus): base tables by `occ_bits_of`, tail tables by a decidable "every send count is a
  product of bool-constrained columns" check;
* **`m2_hsend_fetch`** (`hsendF`), `m2_hsend_byte`, `m2_hsend_func`: the FETCH, BYTE and FUNC send
  bounds of `wasmBaseM2Air`;
* `m2_recv_only_byte`, `m2_recv_only_func`: only BYTE (16) / FUNC (21) receive on those buses;
* **`looks_m2`**: `Looks X.toCtx nloc ngl pub tr` from `Holds (wasmBaseM2Air …)`, `PubOK`,
  `CodeOK`, `FuncOK`.
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## Base constraints from the M2 AIR -/

theorem m2_holdsC {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) : HoldsC (wasmBaseAir nloc ngl) pub tr := by
  refine ⟨fun t ht r hr e he => ?_⟩
  have h22 : t < 22 := by rwa [air_len] at ht
  have ht' : t < (wasmBaseM2Air nloc ngl).tables.length := by rw [m2_air_len]; omega
  exact H.constr t ht' r hr e (by rw [m2_get_base nloc ngl t h22]; exact he)

/-- Base-AIR occurrences are M2-AIR occurrences. -/
theorem occs_base_sub_m2 {nloc ngl : Nat} {tr : Trace} {pub : List F} {o : Occ}
    (ho : o ∈ occs (wasmBaseAir nloc ngl) tr pub) : o ∈ occs (wasmBaseM2Air nloc ngl) tr pub := by
  unfold occs at ho ⊢
  simp only [wasmBaseM2Air, List.zipIdx_append, List.flatMap_append]
  exact List.mem_append_left _ ho

/-! ## Per-bus send bounds -/

/-- Every send of `T` on bus `b` is counted by a `BitE bs` expression. -/
def BusCountsOk (b : Nat) (T : Table) (bs : List Expr) : Bool :=
  T.inters.all (fun i => decide (i.bus ≠ b) || !i.send || BitE bs i.count)

/-- **A table whose sends on bus `b` are syntactically bits.** -/
def BusOk (b : Nat) (T : Table) : Prop := ∃ bs, BitsOk T bs = true ∧ BusCountsOk b T bs = true

theorem bus_le_of_ok {A : Air} {pub : List F} {tr : Trace} (H : Holds A pub tr) {b t : Nat}
    (ht : t < A.tables.length) (hok : BusOk b (A.tables[t]'ht)) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters) (hb : i.bus = b) (hs : i.send = true) :
    (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  obtain ⟨bs, hbits, hcnt⟩ := hok
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
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    rcases hc with (hc | hc) | hc
    · exact absurd hb hc
    · rw [hs] at hc; exact absurd hc (by decide)
    · exact hc

/-- **The send bound on bus `b`** for any `wasmBaseAir ++ tail` AIR whose tail tables are `BusOk b`. -/
theorem hsend_bus_of_tail {X : Ctx} {A : Air} {nloc ngl : Nat} {tail : List Table} {b : Nat}
    {pub : List F} {tr : Trace}
    (hA : A.tables = (wasmBaseAir nloc ngl).tables ++ tail) (htail : ∀ T ∈ tail, BusOk b T)
    (H : Holds A pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs A tr pub, o.1 = b → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hb hs
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs ⊢
  rcases Nat.lt_or_ge t 22 with h22 | h22
  · exact base_send_le_of_prefix hA H hpub ht h22 hr hi hs
  · refine bus_le_of_ok H ht ?_ hr hi hb hs
    apply htail
    have hl : (wasmBaseAir nloc ngl).tables.length ≤ t := by rw [air_len]; exact h22
    have e : A.tables[t]'ht = tail[t - (wasmBaseAir nloc ngl).tables.length]'(by
        have := ht; rw [hA, List.length_append] at this; omega) := by
      simp only [hA]
      rw [List.getElem_append_right hl]
    rw [e]
    exact List.getElem_mem _

/-! ## The M2 tail tables, per bus -/

theorem hostR_busok (b : Nat) (hb : b = busFetch ∨ b = busByte ∨ b = busFunc) : BusOk b HostR.table := by
  refine ⟨v Host.act :: (List.range Host.nArgs).map (fun j => v (Host.pf j)), by decide +kernel, ?_⟩
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem hostO_busok (b : Nat) (hb : b = busFetch ∨ b = busByte ∨ b = busFunc) : BusOk b HostO.table := by
  refine ⟨[], by decide +kernel, ?_⟩
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem hostTab_busok (b : Nat) (hb : b = busFetch ∨ b = busByte ∨ b = busFunc) : BusOk b HostTab.table := by
  refine ⟨[], by decide +kernel, ?_⟩
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem hostB_busok (b : Nat) (hb : b = busFetch ∨ b = busByte ∨ b = busFunc) : BusOk b HostB.table := by
  refine ⟨[v HostB.act, v HostB.dir, v HostB.reg], by decide +kernel, ?_⟩
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem ifc_busok (b : Nat) (hb : b = busFetch ∨ b = busByte ∨ b = busFunc) : BusOk b IfC.table := by
  refine ⟨[v IfC.fIf], by decide +kernel, ?_⟩
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem regc_busok (b : Nat) (hb : b = busFetch ∨ b = busByte ∨ b = busFunc) : BusOk b RegC.table := by
  refine ⟨[v Reg.act, v Reg.kind, v Reg.fresh, v RegW.wr], by decide +kernel, ?_⟩
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem conv_busok (b : Nat) (hb : b = busFetch ∨ b = busByte ∨ b = busFunc) : BusOk b Conv.table := by
  refine ⟨[Conv.act, v Conv.fExtS], by decide +kernel, ?_⟩
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem unreach_busok (b : Nat) (hb : b = busFetch ∨ b = busByte ∨ b = busFunc) : BusOk b Unreach.table := by
  refine ⟨[v Unreach.act], by decide +kernel, ?_⟩
  rcases hb with rfl | rfl | rfl <;> decide +kernel

/-- **The FETCH / BYTE / FUNC send bound of `wasmBaseM2Air`.**  For `b = busFetch` this is
`hsendF`. -/
theorem m2_hsend_bus {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace} {b : Nat}
    (hb : b = busFetch ∨ b = busByte ∨ b = busFunc)
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = b → o.2.1 = true → o.2.2.2 ≤ 1 :=
  hsend_bus_of_tail (tail := [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table,
      RegC.table, Conv.table, Unreach.table]) rfl
    (by
      intro T hT
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hostR_busok b hb
      · exact hostO_busok b hb
      · exact hostTab_busok b hb
      · exact hostB_busok b hb
      · exact ifc_busok b hb
      · exact regc_busok b hb
      · exact conv_busok b hb
      · exact unreach_busok b hb)
    H hpub

/-- **`hsendF`**: FETCH send counts of `wasmBaseM2Air` are at most 1. -/
theorem m2_hsend_fetch {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 ≤ 1 :=
  m2_hsend_bus (Or.inl rfl) H hpub

#print axioms m2_holdsC
#print axioms m2_hsend_bus
#print axioms m2_hsend_fetch

/-! ## `Looks` for an M2 trace -/

theorem table_bus_of_all {T : Table} {b : Nat}
    (h : T.inters.all (fun i => i.bus != b || i.send) = true) :
    ∀ i ∈ T.inters, i.bus = b → i.send = true :=
  recv_only_gen (L := [T]) (by simpa using h) T (by simp)

theorem new_tables_byte :
    [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table, RegC.table, Conv.table,
      Unreach.table].all (fun T => T.inters.all (fun i => i.bus != busByte || i.send)) = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, Bool.true_and]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem new_tables_func :
    [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table, RegC.table, Conv.table,
      Unreach.table].all (fun T => T.inters.all (fun i => i.bus != busFunc || i.send)) = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, Bool.true_and]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem instr_tables_byte' :
    instrTables.all (fun T => T.inters.all (fun i => i.bus != busByte || i.send)) = true := by
  simp only [instrTables, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.true_and]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem instr_tables_func' :
    instrTables.all (fun T => T.inters.all (fun i => i.bus != busFunc || i.send)) = true := by
  simp only [instrTables, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.true_and]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-- **The base row lemmas' lookups, for an M2 trace and the M2 context.** -/
theorem looks_m2 (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X.toCtx nloc ngl pub)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr) :
    Looks X.toCtx nloc ngl pub tr := by
  have hP' := P_val
  have hR16 := m2_hsend_r16 H hpub
  refine ⟨fun o ho hb hs hc => ?_, fun o ho hb hs hc => ?_, fun o ho hb hs hc => ?_, fun o ho hb hs hc => ?_⟩
  · exact m2_fetch X H hcode (m2_hsend_fetch H hpub) (occs_base_sub_m2 ho) hb hs hc
  · exact m2_r16 H hR16 (occs_base_sub_m2 ho) hb hs hc
  · refine lookup_sound H busByte (fun m => ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
      m = [((k : Nat) : F), ((x : Nat) : F), ((y : Nat) : F), ((byteF k x y : Nat) : F)]) ?_
      (m2_hsend_bus (Or.inr (Or.inl rfl)) H hpub) (occs_base_sub_m2 ho) hb hs hc
    intro o' ho' hb' hs' _
    obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
    simp only at hb' hs' ⊢
    have ht30 : t < 30 := by rw [m2_air_len] at ht; exact ht
    by_cases h22 : t < 22
    · have hi0 := hi
      rw [m2_get_base nloc ngl t h22] at hi
      rcases table_class nloc ngl t h22 with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
        ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨_, _, hT⟩
      · rw [hT] at hi; exact absurd hb' (boundary_lookups nloc ngl i hi).2.1
      · rw [hT] at hi; exact absurd (recv_only_byte _ (by simp) i hi hb') (by simp [hs'])
      · rw [hT] at hi; exact absurd (recv_only_byte _ (by simp) i hi hb') (by simp [hs'])
      · rw [hT] at hi; exact absurd (recv_only_byte _ (by simp) i hi hb') (by simp [hs'])
      · have hT' : (wasmBaseM2Air nloc ngl).tables[16]'ht = Byte.table := by
          rw [m2_get_base nloc ngl 16 (by decide)]; exact hT
        exact byte_row_msgs H ht hT' hr i (by rw [hT'] at hi0; exact hi0)
      all_goals first
        | (rw [hT] at hi; exact absurd (recv_only_byte _ (by simp) i hi hb') (by simp [hs']))
        | exact absurd (recv_only_gen instr_tables_byte' _ hT i hi hb') (by simp [hs'])
    · have hmem := m2_get_new nloc ngl t (by omega) ht30
      exact absurd (recv_only_gen new_tables_byte _ hmem i hi hb') (by simp [hs'])
  · refine lookup_sound H busFunc (fun m => ∃ k, k < X.toCtx.nf ∧ m = funcRec X.toCtx k) ?_
      (m2_hsend_bus (Or.inr (Or.inr rfl)) H hpub) (occs_base_sub_m2 ho) hb hs hc
    intro o' ho' hb' hs' _
    obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
    simp only at hb' hs' ⊢
    have ht30 : t < 30 := by rw [m2_air_len] at ht; exact ht
    by_cases h22 : t < 22
    · rw [m2_get_base nloc ngl t h22] at hi
      rcases table_class nloc ngl t h22 with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
        ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨_, _, hT⟩
      · rw [hT] at hi; exact absurd hb' (boundary_lookups nloc ngl i hi).2.2.2.2
      · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
      · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
      · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
      · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
      · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
      · rw [hT] at hi; exact absurd (recv_only_func _ (by simp) i hi hb') (by simp [hs'])
      · rw [hT] at hi
        simp only [Func.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
        subst hi
        obtain ⟨k, hk, he⟩ := hfunc r hr
        refine ⟨k, hk, ?_⟩
        rw [← he]
        simp [List.map_map, Function.comp, v, Expr.eval_col, Trace.row]
      · exact absurd (recv_only_gen instr_tables_func' _ hT i hi hb') (by simp [hs'])
    · have hmem := m2_get_new nloc ngl t (by omega) ht30
      exact absurd (recv_only_gen new_tables_func _ hmem i hi hb') (by simp [hs'])

#print axioms looks_m2

end WasmBase
