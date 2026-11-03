import WasmBase.Main.M2RegAbsentFacts
import WasmBase.M3Check
/-!
# WasmBase.Main.M3Facts — row facts and the R16 send bound of `wasmBaseM3Air`

Proved (standard axioms only) for a satisfied trace of `wasmBaseM3Air` (`WasmBase/M3Air.lean`):

* `regAt_m3`: REG-A at index 27 still satisfies the group walk's interface; **`m3_hsend_r16`**: the
  per-bus R16 send bound (`hsend_r16_of_tail`: HOST-W, MEMG, MSZ, GINIT are `R16Ok`), hence
  `m3_regLenAgree_group` without `hsend`.
* **HOST-W** (`m3_host_arg_tag`, `m3_host_arg_i32`, `m3_host_res_i32`): a present argument's tag
  is `1 − ti j`; an `i32` argument and an `i32` result have zero upper limbs; `ri ≤ ar`.
* **MEMG** (`m3_grow_ok`, `m3_grow_fail`): on a `memory.grow` row, with the R16 answers,
  `ok = 1 → old + n + d = 2048` (so `old + n ≤ 2048`) and `ok = 0 → old + n = 2049 + e` (so
  `old + n > 2048`), with `n = n0 + 2^16·n1` — exactly the spec's `old + n ≤ cfg.maxMemoryPages`
  test (`pv86_maxPages`); `m3_grow_gm`: only a successful grow offers a range.
* **MSZ** (`m3_msz_only_first`, `m3_msz_pages`): only row 0 is active, and it carries
  `65536·pg = pubMem`.
* **GINIT** (`m3_ginit_range`, `m3_ginit_step`): a row's address lies in `[65536·old, 65536·new)`
  of the range it queries (for `old, new ≤ 2048`, what a successful MEMG row offers by
  `m3_grow_ok`), and active addresses are strictly increasing.

Every `hi` limb checked as `r16 (32·hi)` is also checked as `r16 hi`: `32·x ≡ s (mod P)` with
`s < 2^16` has solutions `x ≈ P/32`, so `r16 (32·x)` alone bounds only `65536·x mod P`, not `x`
(`m3_col32_lt` takes the 16-bit premise).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## Walk interface and R16 send bound -/

theorem hostW_table_r16 : HostW.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by
  decide
theorem memg_table_r16 : MemG.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by
  decide
theorem msz_table_r16 : MSz.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by
  decide
theorem ginit_table_r16 : GInit.table.inters.all (fun i => i.bus != busR16 || i.send) = true := by
  decide

theorem m3_recv_only_range16 (nloc ngl : Nat) :
    ∀ T ∈ (wasmBaseM3Air nloc ngl).tables, T ≠ Range16.table → ∀ i ∈ T.inters, i.bus = busR16 →
      i.send = true := by
  intro T hT hne i hi hb
  have hsplit : (wasmBaseM3Air nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [HostW.table, HostO.table, HostTab.table, HostB.table, IfC.table,
        RegA.table, Conv.table, Unreach.table, RInit.table, MemG.table, MSz.table, GInit.table] := rfl
  rw [hsplit, List.mem_append] at hT
  rcases hT with h | h
  · exact base_recv_only_r16 nloc ngl T h hne i hi hb
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact table_r16_of_all hostW_table_r16 i hi hb
    · exact table_r16_of_all hostO_table_r16 i hi hb
    · exact table_r16_of_all hostTab_table_r16 i hi hb
    · exact table_r16_of_all hostB_table_r16 i hi hb
    · exact table_r16_of_all ifc_table_r16 i hi hb
    · exact table_r16_of_all regA_table_r16 i hi hb
    · exact table_r16_of_all conv_table_r16 i hi hb
    · exact table_r16_of_all unreach_table_r16 i hi hb
    · exact table_r16_of_all rinit_table_r16 i hi hb
    · exact table_r16_of_all memg_table_r16 i hi hb
    · exact table_r16_of_all msz_table_r16 i hi hb
    · exact table_r16_of_all ginit_table_r16 i hi hb

/-- **REG-A at index 27 of `wasmBaseM3Air` satisfies the walk's interface.** -/
theorem regAt_m3 (nloc ngl : Nat) : RegAt (wasmBaseM3Air nloc ngl) 27 where
  lt := by rw [m3_air_len]; decide
  cons := fun e he => by
    rw [m3_air_27]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he))
  inters := fun i hi => by
    rw [m3_air_27]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hi))
  r16only := m3_recv_only_range16 nloc ngl

theorem hostW_r16ok : R16Ok HostW.table :=
  ⟨v Host.act :: (List.range Host.nArgs).map (fun j => v (Host.pf j)), by decide +kernel,
    by decide +kernel⟩
theorem memg_r16ok : R16Ok MemG.table := ⟨[v MemG.fGrow, MemG.act], by decide +kernel, by decide +kernel⟩
theorem msz_r16ok : R16Ok MSz.table := ⟨[v MSz.act], by decide +kernel, by decide +kernel⟩
theorem ginit_r16ok : R16Ok GInit.table := ⟨[v GInit.act], by decide +kernel, by decide +kernel⟩

/-- **The R16 send-side bound for `wasmBaseM3Air`.** -/
theorem m3_hsend_r16 {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    ∀ o ∈ occs (wasmBaseM3Air nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1 :=
  hsend_r16_of_tail (tail := [HostW.table, HostO.table, HostTab.table, HostB.table, IfC.table,
      RegA.table, Conv.table, Unreach.table, RInit.table, MemG.table, MSz.table, GInit.table]) rfl
    (by
      intro T hT
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hostW_r16ok
      · exact hostO_r16ok
      · exact hostTab_r16ok
      · exact hostB_r16ok
      · exact ifc_r16ok
      · exact regA_r16ok
      · exact conv_r16ok
      · exact unreach_r16ok
      · exact rinit_r16ok
      · exact memg_r16ok
      · exact msz_r16ok
      · exact ginit_r16ok)
    H hpub

/-- **`regLenAgree_groupG` at REG-A of `wasmBaseM3Air`, without `hsend`.** -/
theorem m3_regLenAgree_group {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r0 : Nat} (hr0 : r0 < tr.height 27)
    (hf : rowNat tr 27 r0 Reg.f = 1) (hk : rowNat tr 27 r0 Reg.kind = 0)
    (hrid0 : rowNat tr 27 r0 Reg.rid ≤ 99) (hpos0 : rowNat tr 27 r0 Reg.pos < 16777216)
    (hactL' : ∀ n, n ≤ rowNat tr 27 r0 Reg.blen → r0 + n < tr.height 27 →
      rowNat tr 27 (r0 + n) Reg.kind = 1 → rowNat tr 27 (r0 + n) Reg.act = 1) :
    let L := rowNat tr 27 r0 Reg.blen
    r0 + L < tr.height 27 ∧
      rowNat tr 27 (r0 + L) Reg.kind = 1 ∧
      rowProd Reg.table tr pub 27 (r0 + L) =
        [Register.lenMsg (rowNat tr 27 r0 Reg.rid) L (rowNat tr 27 r0 Reg.ts)] ∧
      (∀ i, i < L → rowProd Reg.table tr pub 27 (r0 + i) =
        [Register.byteMsg (rowNat tr 27 r0 Reg.rid) i (rowNat tr 27 (r0 + i) Reg.bv)
          (rowNat tr 27 r0 Reg.ts)]) :=
  regLenAgree_groupG (regAt_m3 nloc ngl) H (m3_hsend_r16 H hpub) hr0 hf hk hrid0 hpos0 hactL'

/-! ## Generic helpers -/

theorem m3_lt (nloc ngl t : Nat) (ht : t < 34) : t < (wasmBaseM3Air nloc ngl).tables.length := by
  rw [m3_air_len]; exact ht

/-- A constraint of table `t` (given by its known table) vanishes on row `r`, as a field equation
over the row's naturals. -/
theorem m3_constr {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) {t : Nat} (ht : t < 34) {T : Table}
    (hT : (wasmBaseM3Air nloc ngl).tables[t]'(m3_lt nloc ngl t ht) = T) {r : Nat} (hr : r < tr.height t)
    {e : Expr} (he : e ∈ T.constraints) : e.eval (tr.row pub t r) = 0 :=
  H.constr t (m3_lt nloc ngl t ht) r hr e (by rw [hT]; exact he)

/-- An R16 query of table `t` with count 1 is `< 2^16`. -/
theorem m3_r16_lt {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {t : Nat} (ht : t < 34) {T : Table} (hT : (wasmBaseM3Air nloc ngl).tables[t]'(m3_lt nloc ngl t ht) = T)
    {r : Nat} (hr : r < tr.height t) {e c : Expr} (hi : r16 e c ∈ T.inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) :
    (e.eval (tr.row pub t r)).toNat < 65536 := by
  have hocc := occ_of_inter (m3_lt nloc ngl t ht) hr (by rw [hT]; exact hi) hc
  obtain ⟨x, hx, hxl⟩ := lookup_r16G H (m3_hsend_r16 H hpub)
    (regG_r16_recv (regAt_m3 nloc ngl) H) hocc rfl rfl rfl
  simp only [r16, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
  rw [hx]; exact hxl

/-- A column whose R16 query (count 1) is answered is `< 2^16`. -/
theorem m3_col_lt {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {t : Nat} (ht : t < 34) {T : Table} (hT : (wasmBaseM3Air nloc ngl).tables[t]'(m3_lt nloc ngl t ht) = T)
    {r : Nat} (hr : r < tr.height t) {k : Nat} {c : Expr} (hi : r16 (v k) c ∈ T.inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) : rowNat tr t r k < 65536 := by
  have h := m3_r16_lt H hpub ht hT hr hi hc
  rwa [col_eval_nat, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] at h


/-- A column whose `32·x` R16 query (count 1) is answered, and which is itself 16-bit, is `< 2^11`.
(The 16-bit premise is needed: `32·x ≡ s (mod P)` with `s < 2^16` holds for some `x ≈ P/32`.) -/
theorem m3_col32_lt {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {t : Nat} (ht : t < 34) {T : Table} (hT : (wasmBaseM3Air nloc ngl).tables[t]'(m3_lt nloc ngl t ht) = T)
    {r : Nat} (hr : r < tr.height t) {k : Nat} {c : Expr} (hx : rowNat tr t r k < 65536)
    (hi : r16 (32 * v k) c ∈ T.inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) : rowNat tr t r k < 2048 := by
  have h := m3_r16_lt H hpub ht hT hr hi hc
  simp only [Expr.eval_mul', Expr.eval_ofNat', col_eval_nat] at h
  have hP := P_val
  rw [← Lean.Grind.Semiring.natCast_mul, Fp.toNat_cast_of_lt (by omega)] at h
  omega

theorem cast_zero_nat {x : Nat} (hx : x < P) (h : ((x : Nat) : F) = 0) : x = 0 :=
  natEq (R := 0) (by rw [h]; rfl) hx (by rw [P_val]; decide)

theorem cast_one_nat {x : Nat} (hx : x < P) (h : ((x : Nat) : F) = 1) : x = 1 :=
  natEq (R := 1) (by rw [h]; rfl) hx (by rw [P_val]; decide)

/-! ## HOST-W -/

/-- The per-argument constraints of HOST-W are constraints of the table. -/
theorem hostW_mem_pad (j : Nat) (hj : j < Host.nArgs) {e : Expr}
    (he : e ∈ [Host.cPad j, HostW.cTagW j] ++ Host.cPadL j ++ HostW.cI32Hi j ++ [HostW.cTi j, HostW.cTiPf j]) :
    e ∈ HostW.table.constraints := by
  show e ∈ HostW.constraints
  unfold HostW.constraints
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ ?_)))))
  exact List.mem_flatMap.mpr ⟨j, by simpa [Host.argRange] using hj, he⟩

/-- **A present argument's tag is `1 − ti j`** (`i64` = 1, `i32` = 0) on a HOST-W row. -/
theorem m3_host_arg_tag {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    {j : Nat} (hj : j < Host.nArgs) (hp : rowNat tr 22 r (Host.pf j) = 1) :
    ((rowNat tr 22 r (Host.tagP j) : Nat) : F) = 1 - ((rowNat tr 22 r (HostW.ti j) : Nat) : F) := by
  have h := m3_constr H (t := 22) (by decide) (m3_air_22 nloc ngl) hr (e := HostW.cTagW j)
    (hostW_mem_pad j hj (by simp))
  simp only [HostW.cTagW, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', col_eval_nat, hp,
    cast_one] at h
  grind

/-- **An `i32` argument has zero upper limbs.** -/
theorem m3_host_arg_i32 {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    {j : Nat} (hj : j < Host.nArgs) (hti : rowNat tr 22 r (HostW.ti j) = 1) :
    rowNat tr 22 r (Host.P j + 2) = 0 ∧ rowNat tr 22 r (Host.P j + 3) = 0 := by
  have h2 := m3_constr H (t := 22) (by decide) (m3_air_22 nloc ngl) hr
    (e := v (HostW.ti j) * v (Host.P j + 2)) (hostW_mem_pad j hj (by simp [HostW.cI32Hi]))
  have h3 := m3_constr H (t := 22) (by decide) (m3_air_22 nloc ngl) hr
    (e := v (HostW.ti j) * v (Host.P j + 3)) (hostW_mem_pad j hj (by simp [HostW.cI32Hi]))
  simp only [Expr.eval_mul', col_eval_nat, hti, cast_one] at h2 h3
  exact ⟨cast_zero_nat (rowNat_lt _ _ _ _) (by grind), cast_zero_nat (rowNat_lt _ _ _ _) (by grind)⟩

/-- **An `i32` result has zero upper limbs, and only a function with a result has one.** -/
theorem m3_host_res_i32 {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 22)
    (hri : rowNat tr 22 r HostW.ri = 1) :
    rowNat tr 22 r (Host.rb + 2) = 0 ∧ rowNat tr 22 r (Host.rb + 3) = 0 ∧
      rowNat tr 22 r Host.ar = 1 := by
  have mAr : HostW.cRiAr ∈ HostW.table.constraints := by
    show _ ∈ HostW.constraints
    unfold HostW.constraints
    exact List.mem_append_left _ (List.mem_append_right _ (by simp))
  have mHi : ∀ e ∈ HostW.cRiHi, e ∈ HostW.table.constraints := by
    intro e he
    show _ ∈ HostW.constraints
    unfold HostW.constraints
    exact List.mem_append_right _ he
  have ha := m3_constr H (t := 22) (by decide) (m3_air_22 nloc ngl) hr mAr
  have h2 := m3_constr H (t := 22) (by decide) (m3_air_22 nloc ngl) hr
    (mHi (v HostW.ri * v (Host.rb + 2)) (by simp [HostW.cRiHi]))
  have h3 := m3_constr H (t := 22) (by decide) (m3_air_22 nloc ngl) hr
    (mHi (v HostW.ri * v (Host.rb + 3)) (by simp [HostW.cRiHi]))
  simp only [HostW.cRiAr, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', col_eval_nat, hri,
    cast_one] at ha h2 h3
  exact ⟨cast_zero_nat (rowNat_lt _ _ _ _) (by grind), cast_zero_nat (rowNat_lt _ _ _ _) (by grind),
    cast_one_nat (rowNat_lt _ _ _ _) (by grind)⟩

/-! ## MEMG -/

/-- The count `f_grow` is 1 on a grow row. -/
theorem memg_fgrow_cnt {tr : Trace} {pub : List F} {r : Nat} (hg : rowNat tr 31 r MemG.fGrow = 1) :
    ((v MemG.fGrow).eval (tr.row pub 31 r)).toNat = 1 := by
  rw [col_eval_nat, hg]; decide

/-- The count `act = f_grow + f_size` is 1 on a grow row (`f_size = 0` by `bool act`). -/
theorem memg_act_cnt {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 31)
    (hg : rowNat tr 31 r MemG.fGrow = 1) : (MemG.act.eval (tr.row pub 31 r)).toNat = 1 := by
  have hb := m3_constr H (t := 31) (by decide) (m3_air_31 nloc ngl) hr
    (e := bool MemG.act) (by simp [MemG.table, MemG.constraints])
  have hs := m3_constr H (t := 31) (by decide) (m3_air_31 nloc ngl) hr
    (e := bool (v MemG.fSize)) (by simp [MemG.table, MemG.constraints])
  simp only [Chips.bool, MemG.act, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat',
    col_eval_nat, hg] at hb hs ⊢
  rcases bool_nat (rowNat_lt tr 31 r MemG.fSize) hs with h0 | h1
  · rw [h0]; decide
  · rw [h1] at hb; exact absurd hb (by decide)

/-- **A successful `memory.grow`: `old + n + d = 2048`**, so `old + n ≤ maxMemoryPages`, with
`n = n0 + 2^16·n1` the popped page count. -/
theorem m3_grow_ok {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 31)
    (hg : rowNat tr 31 r MemG.fGrow = 1) (hok : rowNat tr 31 r MemG.ok = 1) :
    rowNat tr 31 r MemG.old + (rowNat tr 31 r MemG.n0 + 65536 * rowNat tr 31 r MemG.n1) +
      rowNat tr 31 r MemG.d = maxPagesM3 := by
  have hT := m3_air_31 nloc ngl
  have hc := memg_fgrow_cnt (pub := pub) hg
  have ha := memg_act_cnt H hr hg
  have hn0 := m3_col_lt H hpub (by decide) hT hr (k := MemG.n0) (by simp [MemG.table, MemG.inters]) hc
  have hn1' := m3_col_lt H hpub (by decide) hT hr (k := MemG.n1) (by simp [MemG.table, MemG.inters]) hc
  have hn1 := m3_col32_lt H hpub (by decide) hT hr (k := MemG.n1) hn1'
    (by simp [MemG.table, MemG.inters]) hc
  have hold := m3_col_lt H hpub (by decide) hT hr (k := MemG.old) (by simp [MemG.table, MemG.inters]) ha
  have hd := m3_col_lt H hpub (by decide) hT hr (k := MemG.d) (by simp [MemG.table, MemG.inters]) ha
  have h := m3_constr H (t := 31) (by decide) hT hr (e := MemG.cOk)
    (by simp [MemG.table, MemG.constraints])
  simp only [MemG.cOk, MemG.nE, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat',
    Expr.eval_c, col_eval_nat, hok, cast_one] at h
  have hP := P_val
  refine natEq ?_ (by omega) (by simp [maxPagesM3]; omega)
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
  grind

/-- **A failed `memory.grow`: `old + n = 2049 + e0 + 2^16·e1`**, so `old + n > maxMemoryPages`. -/
theorem m3_grow_fail {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 31)
    (hg : rowNat tr 31 r MemG.fGrow = 1) (hok : rowNat tr 31 r MemG.ok = 0) :
    rowNat tr 31 r MemG.old + (rowNat tr 31 r MemG.n0 + 65536 * rowNat tr 31 r MemG.n1) =
      maxPagesM3 + 1 + (rowNat tr 31 r MemG.e0 + 65536 * rowNat tr 31 r MemG.e1) := by
  have hT := m3_air_31 nloc ngl
  have hc := memg_fgrow_cnt (pub := pub) hg
  have ha := memg_act_cnt H hr hg
  have hn0 := m3_col_lt H hpub (by decide) hT hr (k := MemG.n0) (by simp [MemG.table, MemG.inters]) hc
  have hn1' := m3_col_lt H hpub (by decide) hT hr (k := MemG.n1) (by simp [MemG.table, MemG.inters]) hc
  have hn1 := m3_col32_lt H hpub (by decide) hT hr (k := MemG.n1) hn1'
    (by simp [MemG.table, MemG.inters]) hc
  have hold := m3_col_lt H hpub (by decide) hT hr (k := MemG.old) (by simp [MemG.table, MemG.inters]) ha
  have he0 := m3_col_lt H hpub (by decide) hT hr (k := MemG.e0) (by simp [MemG.table, MemG.inters]) ha
  have he1' := m3_col_lt H hpub (by decide) hT hr (k := MemG.e1) (by simp [MemG.table, MemG.inters]) ha
  have he1 := m3_col32_lt H hpub (by decide) hT hr (k := MemG.e1) he1'
    (by simp [MemG.table, MemG.inters]) ha
  have h := m3_constr H (t := 31) (by decide) hT hr (e := MemG.cFail)
    (by simp [MemG.table, MemG.constraints])
  simp only [MemG.cFail, MemG.nE, Expr.eval_mul', Expr.eval_sub', Expr.eval_add', Expr.eval_ofNat',
    Expr.eval_c, col_eval_nat, hok, hg, cast_one] at h
  have hP := P_val
  refine natEq ?_ (by omega) (by simp [maxPagesM3]; omega)
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, cast_one]
  grind

/-- **Only a successful grow offers a GINIT range** (`gm·(1 − ok) = 0`). -/
theorem m3_grow_gm {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 31)
    (hok : rowNat tr 31 r MemG.ok = 0) : rowNat tr 31 r MemG.gm = 0 := by
  have h := m3_constr H (t := 31) (by decide) (m3_air_31 nloc ngl) hr
    (e := v MemG.gm * (1 - v MemG.ok)) (by simp [MemG.table, MemG.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', col_eval_nat, hok, cast_one] at h
  exact cast_zero_nat (rowNat_lt _ _ _ _) (by grind)

/-! ## MSZ -/

/-- **Only row 0 of MSZ is active.** -/
theorem m3_msz_only_first {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 32) (h0 : r ≠ 0) :
    rowNat tr 32 r MSz.act = 0 := by
  have h := m3_constr H (t := 32) (by decide) (m3_air_32 nloc ngl) hr
    (e := (1 - Expr.first) * v MSz.act) (by simp [MSz.table, MSz.constraints])
  have hf : (r == 0) = false := by simpa using h0
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval, Chips.v, Expr.eval_col, cell_cast, Trace.row, hf,
    Bool.false_eq_true, ite_false, col_eval_nat, cast_one] at h
  exact cast_zero_nat (rowNat_lt _ _ _ _) (by grind)

/-- **MSZ's row 0 is active and carries the initial size: `65536·pg = pubMem`.** -/
theorem m3_msz_pages {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hr : 0 < tr.height 32) :
    rowNat tr 32 0 MSz.act = 1 ∧
      ((65536 : Nat) : F) * ((rowNat tr 32 0 MSz.pg : Nat) : F) = (tr.row pub 32 0).pub Boundary.pubMem := by
  have h1 := m3_constr H (t := 32) (by decide) (m3_air_32 nloc ngl) hr
    (e := Expr.first * (1 - v MSz.act)) (by simp [MSz.table, MSz.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval, Chips.v, Expr.eval_col, cell_cast, Trace.row,
    beq_self_eq_true, ite_true, col_eval_nat, cast_one] at h1
  have ha : rowNat tr 32 0 MSz.act = 1 := cast_one_nat (rowNat_lt _ _ _ _) (by grind)
  refine ⟨ha, ?_⟩
  have h2 := m3_constr H (t := 32) (by decide) (m3_air_32 nloc ngl) hr
    (e := v MSz.act * (65536 * v MSz.pg - pv Boundary.pubMem)) (by simp [MSz.table, MSz.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_pub, col_eval_nat, ha,
    cast_one, Chips.pv] at h2
  grind

/-! ## GINIT -/

/-- **A GINIT byte lies in its grow's range**: `65536·old ≤ ad < 65536·new`, for a range with
`old, new ≤ 2048` (what a successful MEMG row offers: `old + n + d = 2048`, `m3_grow_ok`). -/
theorem m3_ginit_range {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r < tr.height 33) (ha : rowNat tr 33 r GInit.act = 1)
    (hold : rowNat tr 33 r GInit.old ≤ 2048) (hnew : rowNat tr 33 r GInit.new ≤ 2048) :
    65536 * rowNat tr 33 r GInit.old ≤ rowNat tr 33 r GInit.ad ∧
      rowNat tr 33 r GInit.ad < 65536 * rowNat tr 33 r GInit.new := by
  have hT := m3_air_33 nloc ngl
  have hc : ((v GInit.act).eval (tr.row pub 33 r)).toNat = 1 := by rw [col_eval_nat, ha]; decide
  have hdlo := m3_col_lt H hpub (by decide) hT hr (k := GInit.dlo) (by simp [GInit.table, GInit.inters]) hc
  have hdhi' := m3_col_lt H hpub (by decide) hT hr (k := GInit.dhi) (by simp [GInit.table, GInit.inters]) hc
  have hdhi := m3_col32_lt H hpub (by decide) hT hr (k := GInit.dhi) hdhi'
    (by simp [GInit.table, GInit.inters]) hc
  have helo := m3_col_lt H hpub (by decide) hT hr (k := GInit.elo) (by simp [GInit.table, GInit.inters]) hc
  have hehi' := m3_col_lt H hpub (by decide) hT hr (k := GInit.ehi) (by simp [GInit.table, GInit.inters]) hc
  have hehi := m3_col32_lt H hpub (by decide) hT hr (k := GInit.ehi) hehi'
    (by simp [GInit.table, GInit.inters]) hc
  have hd := m3_constr H (t := 33) (by decide) hT hr
    (e := v GInit.act * (v GInit.ad - 65536 * v GInit.old - v GInit.dlo - 65536 * v GInit.dhi))
    (by simp [GInit.table, GInit.constraints])
  have he := m3_constr H (t := 33) (by decide) hT hr
    (e := v GInit.act * (65536 * v GInit.new - 1 - v GInit.ad - v GInit.elo - 65536 * v GInit.ehi))
    (by simp [GInit.table, GInit.constraints])
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', col_eval_nat, ha, cast_one] at hd he
  have hP := P_val
  have e1 : rowNat tr 33 r GInit.ad =
      65536 * rowNat tr 33 r GInit.old + rowNat tr 33 r GInit.dlo + 65536 * rowNat tr 33 r GInit.dhi := by
    refine natEq ?_ (rowNat_lt _ _ _ _) (by omega)
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    grind
  have e2 : 65536 * rowNat tr 33 r GInit.new =
      rowNat tr 33 r GInit.ad + 1 + rowNat tr 33 r GInit.elo + 65536 * rowNat tr 33 r GInit.ehi := by
    refine natEq ?_ (by omega) (by omega)
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, cast_one]
    grind
  omega

/-- **GINIT's active addresses are strictly increasing** (one step, for a predecessor address
`< 2^28`, which `m3_ginit_range` gives an active row). -/
theorem m3_ginit_step {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM3Air nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    {r : Nat} (hr : r + 1 < tr.height 33) (ha : rowNat tr 33 (r + 1) GInit.act = 1)
    (had0 : rowNat tr 33 r GInit.ad < 2 ^ 28) :
    rowNat tr 33 r GInit.ad < rowNat tr 33 (r + 1) GInit.ad := by
  have hT := m3_air_33 nloc ngl
  have hc : ((v GInit.act).eval (tr.row pub 33 (r + 1))).toNat = 1 := by rw [col_eval_nat, ha]; decide
  have hglo := m3_col_lt H hpub (by decide) hT hr (k := GInit.glo) (by simp [GInit.table, GInit.inters]) hc
  have hghi' := m3_col_lt H hpub (by decide) hT hr (k := GInit.ghi) (by simp [GInit.table, GInit.inters]) hc
  have hghi := m3_col32_lt H hpub (by decide) hT hr (k := GInit.ghi) hghi'
    (by simp [GInit.table, GInit.inters]) hc
  have h := m3_constr H (t := 33) (by decide) hT (r := r) (by omega)
    (e := .trans * (nv GInit.act * (nv GInit.ad - v GInit.ad - 1 - nv GInit.glo - 65536 * nv GInit.ghi)))
    (by simp [GInit.table, GInit.constraints])
  have hlast : (r + 1 == tr.height 33) = false := by simp; omega
  simp only [Chips.nv, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_nxt, Expr.eval,
    Chips.v, Expr.eval_col, Trace.row, hlast, Bool.false_eq_true, ite_false, Nat.mod_eq_of_lt hr, cell_cast, col_eval_nat,
    ha, cast_one] at h
  have hP := P_val
  have e : rowNat tr 33 (r + 1) GInit.ad =
      rowNat tr 33 r GInit.ad + 1 + rowNat tr 33 (r + 1) GInit.glo +
        65536 * rowNat tr 33 (r + 1) GInit.ghi := by
    refine natEq ?_ (rowNat_lt _ _ _ _) (by omega)
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, cast_one]
    grind
  omega

end WasmBase

#print axioms WasmBase.m3_hsend_r16
#print axioms WasmBase.m3_regLenAgree_group
#print axioms WasmBase.m3_host_arg_tag
#print axioms WasmBase.m3_host_arg_i32
#print axioms WasmBase.m3_host_res_i32
#print axioms WasmBase.m3_grow_ok
#print axioms WasmBase.m3_grow_fail
#print axioms WasmBase.m3_grow_gm
#print axioms WasmBase.m3_msz_only_first
#print axioms WasmBase.m3_msz_pages
#print axioms WasmBase.m3_ginit_range
#print axioms WasmBase.m3_ginit_step
