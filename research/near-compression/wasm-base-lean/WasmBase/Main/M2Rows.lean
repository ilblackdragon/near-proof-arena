import WasmBase.M2Ctx
import WasmBase.Main.M2Link
import WasmBase.Main.RegWalkG
import WasmBase.Main.RowIf
/-!
# WasmBase.Main.M2Rows — CONV (28) and UNREACH (29) rows of a `Holds (wasmBaseM2Air …)` trace

Everything here is about the **M2 AIR's own** `Holds` (its bus balance includes the CONV/UNREACH
FETCH and R16 queries) and the **M2 context** `M2Ctx` (`WasmBase/M2Ctx.lean`, code facts derived
from `checkModuleM2`).  No base `Ctx` appears: a base `Ctx` cannot exist for a module that contains
a conversion or `unreachable` (`checkModule` rejects it), so a statement over `Ctx` about these rows
would be vacuous.

## Contents

* **Lookups of the M2 AIR.**
  * `m2_recv_only_fetch`: every table of `wasmBaseM2Air` except CODE only *sends* on FETCH;
  * `m2_fetch`: a FETCH query with count 1 is a global code record of the M2 module (`CodeOKM2`,
    the commitment binding of the cached CODE table to the M2 records);
  * `m2_r16`: an R16 query with count 1 is `< 2^16` (from `m2_recv_only_range16`);
  * `m2_time_chk`: a channel time check bounds the producer time.
* **The FETCH pin.**  `m2_fetch_conv` / `m2_fetch_unreach`: the FETCH answer of a CONV (UNREACH)
  row pins a checked function `k`, a local pc, the instruction (`.num op` with `isConvOp op`,
  resp. `.unreachable`), its fee and its static height.
* **Row facts.**  `conv_row_m2` and `unreach_row_m2`: for an active row, the pinned instruction, the
  CH effect (`conv_row_spec`: the produced message is `convVal op` of the consumed one), and the six
  non-spec `RowFacts2` fields (`halt0`, `tsOut`, `gasOut`, `consT`, `prodT`, `prodNd`).
* **Spec steps over `M2Ctx`.**  `M2Ctx.step_eq_exec`, `M2Ctx.step_conv_spec`,
  `M2Ctx.step_unreach_spec`: the spec `step` at a conversion pc continues with the stack top
  replaced by `convVal op`, at an `unreachable` pc it aborts with `WasmTrap(Unreachable)`, both
  after charging the pc's fee.
* **Row ↔ step.**  `conv_row_step_m2`, `unreach_row_step_m2`: an active row and a spec state whose top
  frame is at the row's pc and whose stack top is the consumed value: the spec step produces exactly
  the value the row produces (resp. aborts as the row's `halted = 2` says).

## Named hypotheses (not discharged here)

* `hsendF` — the FETCH send-side bound `∀ o ∈ occs A tr pub, o.1 = busFetch → o.2.1 = true →
  o.2.2.2 ≤ 1` for `A = wasmBaseM2Air`.  The same kind of fact as the R16 bound: every FETCH send is
  counted by an `act` that the row's constraints make a bit.  `lookup_sound` needs it.
* `hsend` — the R16 send-side bound, of the shape fixed by the plan; it is being proved in parallel
  (`WasmBase/Main/RegSendM2.lean`) and is kept a hypothesis here.
* `CodeOKM2` — the statement binding of the cached CODE table to the M2 records (the M2 analogue of
  `Main/Lookups.lean:CodeOK`; it is a commitment-binding premise, not a provable fact).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-! ## Code records of the M2 context -/

/-- Global code record `j` of the M2 module, as field elements. -/
def codeRecM2 (X : M2Ctx) (j : Nat) : List F := (X.M.records[j]?.getD []).map fun x => ((x : Nat) : F)

/-- **Statement binding of the cached CODE table** to the M2 records (cf. `CodeOK`). -/
def CodeOKM2 (X : M2Ctx) (tr : Trace) : Prop :=
  ∀ r, r < tr.height 17 → ∃ j, j < X.M.codeSize ∧
    (List.range Boundary.recWidth).map (fun k => tr.cell 17 r k) = codeRecM2 X j

/-- Every opcode `recordAtM2` emits is below `0x243`. -/
theorem recordAtM2_op_lt {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) : rec.getD 1 0 < 0x243 := by
  unfold recordAtM2 at hr
  repeat' split at hr
  all_goals first
    | (have := recordOf_op_lt_opIf hr; simp only [IfC.opIf] at this; omega)
    | (simp at hr; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       simp [Chips.IfC.opIf, Chips.Ctrl.opJump, Chips.opHost, opHostX, opUnreach, opMemGrowX,
         opMemSizeX]; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       simp only [List.getD_cons_succ, List.getD_cons_zero]
       have := isConvOp_cases ‹isConvOp _ = true›; omega)

theorem M2Ctx.recOp_lt (X : M2Ctx) {j : Nat} (hj : j < X.M.codeSize) :
    (X.M.records[j]?.getD []).getD 1 0 < 0x243 := by
  obtain ⟨k, l, hk, hl, -, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  rw [hrj, Array.getElem?_eq_getElem hsz, Option.getD_some, Option.getD_some]
  exact recordAtM2_op_lt hrec

/-! ## Lookups of the M2 AIR -/

theorem table_fetch_of_all {T : Table}
    (h : T.inters.all (fun i => i.bus != busFetch || i.send) = true) :
    ∀ i ∈ T.inters, i.bus = busFetch → i.send = true :=
  recv_only_gen (L := [T]) (by simpa using h) T (by simp)

theorem instr_tables_fetch :
    instrTables.all (fun T => T.inters.all (fun i => i.bus != busFetch || i.send)) = true := by
  simp only [instrTables, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.true_and]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem m2_get_base (nloc ngl t : Nat) (ht : t < 22) :
    (wasmBaseM2Air nloc ngl).tables[t]'(by rw [m2_air_len]; omega) =
      (wasmBaseAir nloc ngl).tables[t]'(by rw [air_len]; exact ht) := by
  unfold wasmBaseM2Air
  rw [List.getElem_append_left (by simp [air_len]; exact ht)]

theorem m2_t28 (nloc ngl : Nat) :
    (wasmBaseM2Air nloc ngl).tables[28]'(by rw [m2_air_len]; decide) = Conv.table := by
  simp [wasmBaseM2Air, wasmBaseAir]

theorem m2_t29 (nloc ngl : Nat) :
    (wasmBaseM2Air nloc ngl).tables[29]'(by rw [m2_air_len]; decide) = Unreach.table := by
  simp [wasmBaseM2Air, wasmBaseAir]

/-- The M2 tables 22–29, explicitly. -/
theorem m2_get_new (nloc ngl t : Nat) (h1 : 22 ≤ t) (h2 : t < 30) :
    (wasmBaseM2Air nloc ngl).tables[t]'(by rw [m2_air_len]; exact h2) ∈
      [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table, RegC.table, Conv.table,
        Unreach.table] := by
  rcases (show t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [wasmBaseM2Air, wasmBaseAir]

theorem new_tables_fetch :
    [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table, RegC.table, Conv.table,
      Unreach.table].all (fun T => T.inters.all (fun i => i.bus != busFetch || i.send)) = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, Bool.true_and]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **FETCH lookup soundness on the M2 AIR.**  A FETCH query with count 1 is a code record of the
M2 module. -/
theorem m2_fetch (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    (hsendF : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs (wasmBaseM2Air nloc ngl) tr pub) (hb : o.1 = busFetch)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ j, j < X.M.codeSize ∧ o.2.2.1 = codeRecM2 X j := by
  refine lookup_sound H busFetch (fun m => ∃ j, j < X.M.codeSize ∧ m = codeRecM2 X j) ?_ hsendF ho hb hs hc
  intro o' ho' hb' hs' _
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho'
  simp only at hb' hs' ⊢
  have ht30 : t < 30 := by rw [m2_air_len] at ht; exact ht
  by_cases h22 : t < 22
  · rw [m2_get_base nloc ngl t h22] at hi
    rcases table_class nloc ngl t h22 with ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ |
      ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨rfl, hT⟩ | ⟨_, _, hT⟩
    · rw [hT] at hi; exact absurd hb' (boundary_lookups nloc ngl i hi).2.2.1
    · rw [hT] at hi
      simp only [Code.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
      subst hi
      obtain ⟨j, hj, he⟩ := hcode r hr
      refine ⟨j, hj, ?_⟩
      rw [← he]
      simp [List.map_map, Function.comp, v, Expr.eval_col, Trace.row, Boundary.recWidth]
    all_goals first
      | (rw [hT] at hi; exact absurd (recv_only_code_fetch _ (by simp) i hi hb') (by simp [hs']))
      | exact absurd (recv_only_gen instr_tables_fetch _ hT i hi hb') (by simp [hs'])
  · have hmem := m2_get_new nloc ngl t (by omega) ht30
    exact absurd (recv_only_gen new_tables_fetch _ hmem i hi hb') (by simp [hs'])

/-- **R16 lookup soundness on the M2 AIR.** -/
theorem m2_r16 {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {o : Occ} (ho : o ∈ occs (wasmBaseM2Air nloc ngl) tr pub) (hb : o.1 = busR16)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 :=
  lookup_r16G H hsend (regG_r16_recv (regAt_m2 nloc ngl) H) ho hb hs hc

/-- Every `recordAtM2` record has eight fields. -/
theorem recordAtM2_shape {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) :
    ∃ a op b c d e f g, rec = [a, op, b, c, d, e, f, g] := by
  unfold recordAtM2 at hr
  repeat' split at hr
  all_goals first
    | (obtain ⟨_, _, _, _, _, rfl, -⟩ := recordOf_spec hr; exact ⟨_, _, _, _, _, _, _, _, rfl⟩)
    | (simp at hr; done)
    | (simp only [Option.some.injEq] at hr; subst hr; exact ⟨_, _, _, _, _, _, _, _, rfl⟩)

theorem M2Ctx.recShape (X : M2Ctx) {j : Nat} (hj : j < X.M.codeSize) :
    ∃ a op b c d e f g, X.M.records[j]?.getD [] = [a, op, b, c, d, e, f, g] := by
  obtain ⟨k, l, hk, hl, -, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  rw [hrj, Array.getElem?_eq_getElem hsz, Option.getD_some, Option.getD_some]
  exact recordAtM2_shape hrec

theorem cast8_inj {a b c d e f g h a' b' c' d' e' f' g' h' : Nat}
    (heq : [((a : Nat) : F), ((b : Nat) : F), ((c : Nat) : F), ((d : Nat) : F), ((e : Nat) : F),
      ((f : Nat) : F), ((g : Nat) : F), ((h : Nat) : F)] =
      [a', b', c', d', e', f', g', h'].map fun x => ((x : Nat) : F)) :
    ((a : Nat) : F) = a' ∧ ((b : Nat) : F) = b' ∧ ((c : Nat) : F) = c' ∧ ((d : Nat) : F) = d' := by
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at heq
  exact ⟨heq.1, heq.2.1, heq.2.2.1, heq.2.2.2.1⟩

/-- **The FETCH pin of a conversion row.**  A count-1 FETCH query `[pc, op, h, fee, 0, 0, 0, 0]` of
the M2 AIR with a conversion opcode `op` pins a checked function `k` and local pc with
`code[pc] = .num op`, the pc's fee and its static height. -/
theorem m2_fetch_conv (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    (hsendF : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 ≤ 1)
    {pcN opN hN feeN : Nat} (hpcP : pcN < P) (hhP : hN < P) (hfP : feeN < P)
    (hop : isConvOp opN = true)
    (ho : (busFetch, true, [((pcN : Nat) : F), ((opN : Nat) : F), ((hN : Nat) : F), ((feeN : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)], 1) ∈
        occs (wasmBaseM2Air nloc ngl) tr pub) :
    ∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = pcN ∧
      (X.pfOf k).code[pc]? = some (.num opN) ∧ feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧
      feeN = fee ∧ hN = (X.ckOf k).heights[pc]?.getD 0 ∧ fee ≤ X.maxFee := by
  have hP' := P_val
  obtain ⟨j, hj, hm⟩ := m2_fetch X H hcode hsendF ho rfl rfl rfl
  simp only [codeRecM2] at hm
  obtain ⟨a, op, b, c, d, e, f, g, hsh⟩ := X.recShape hj
  have hopl := X.recOp_lt hj
  rw [hsh] at hm hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  obtain ⟨-, e1, -, -⟩ := cast8_inj hm
  have hconv := isConvOp_cases hop
  have hopEq : opN = op := natEq e1 (by omega) (by omega)
  subst hopEq
  have hop2 : isConvOp ((X.M.records[j]?.getD []).getD 1 0) = true := by rw [hsh]; exact hop
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hrec⟩ := X.recG_conv hj hop2
  rw [hsh] at hrec hins
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hrec hins
  rw [hrec] at hm
  obtain ⟨e0, -, e2, e3⟩ := cast8_inj hm
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hpcEq : pcN = j := natEq e0 hpcP (by omega)
  have hhb := (X.factsOf hk).hBound pc hpc
  have hfl := feeUnits_lt hfee
  refine ⟨k, pc, fee, hk, hpc, by omega, hins, hfee, natEq e3 hfP (by omega), natEq e2 hhP (by omega), ?_⟩
  have := X.recFee_le hj
  rw [hsh] at this
  simp only [List.cons.injEq] at hrec
  simp only [List.getD_cons_succ, List.getD_cons_zero] at this
  omega

/-- **The FETCH pin of an `unreachable` row.** -/
theorem m2_fetch_unreach (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    (hsendF : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 ≤ 1)
    {pcN hN feeN : Nat} (hpcP : pcN < P) (hhP : hN < P) (hfP : feeN < P)
    (ho : (busFetch, true, [((pcN : Nat) : F), ((opUnreach : Nat) : F), ((hN : Nat) : F), ((feeN : Nat) : F),
      ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F)], 1) ∈
        occs (wasmBaseM2Air nloc ngl) tr pub) :
    ∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = pcN ∧
      (X.pfOf k).code[pc]? = some .unreachable ∧ feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧
      feeN = fee ∧ hN = (X.ckOf k).heights[pc]?.getD 0 ∧ fee ≤ X.maxFee := by
  have hP' := P_val
  obtain ⟨j, hj, hm⟩ := m2_fetch X H hcode hsendF ho rfl rfl rfl
  simp only [codeRecM2] at hm
  obtain ⟨a, op, b, c, d, e, f, g, hsh⟩ := X.recShape hj
  have hopl := X.recOp_lt hj
  rw [hsh] at hm hopl
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hopl
  obtain ⟨-, e1, -, -⟩ := cast8_inj hm
  have hopEq : opUnreach = op := natEq e1 (by simp [opUnreach]; omega) (by omega)
  have hop2 : (X.M.records[j]?.getD []).getD 1 0 = opUnreach := by rw [hsh]; exact hopEq.symm
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hrec⟩ := X.recG_unreach hj hop2
  rw [hsh] at hrec
  rw [hrec] at hm
  obtain ⟨e0, -, e2, e3⟩ := cast8_inj hm
  have hjl : j < 2 ^ 20 := Nat.lt_trans hj X.mf.total
  have hhb := (X.factsOf hk).hBound pc hpc
  have hfl := feeUnits_lt hfee
  refine ⟨k, pc, fee, hk, hpc, by have := natEq e0 hpcP (by omega); omega, hins, hfee,
    natEq e3 hfP (by omega), natEq e2 hhP (by omega), ?_⟩
  have := X.recFee_le hj
  rw [hsh] at this
  simp only [List.cons.injEq] at hrec
  simp only [List.getD_cons_succ, List.getD_cons_zero] at this
  omega

/-- **Time check on the M2 AIR**: the two R16 queries `[ts − tp − 1 − 2^16·hi]`, `[4·hi]` with count 1
bound the producer time. -/
theorem m2_time_chk {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr)
    (hsend : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {ts tp hi : F}
    (h1 : (busR16, true, [ts - tp - ((1 : Nat) : F) - ((65536 : Nat) : F) * hi], 1) ∈
      occs (wasmBaseM2Air nloc ngl) tr pub)
    (h2 : (busR16, true, [((4 : Nat) : F) * hi], 1) ∈ occs (wasmBaseM2Air nloc ngl) tr pub) :
    ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((tp.toNat + 1 + n : Nat) : F) = ts := by
  obtain ⟨x, hx, hxl⟩ := m2_r16 H hsend h1 rfl rfl rfl
  obtain ⟨y, hy, hyl⟩ := m2_r16 H hsend h2 rfl rfl rfl
  simp only [List.cons.injEq, and_true] at hx hy
  refine ⟨x.toNat + 16384 * y.toNat, by omega, ?_⟩
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat]
  rw [← hx, ← hy]
  have : ((65536 : Nat) : F) = ((16384 : Nat) : F) * ((4 : Nat) : F) := by
    rw [← Lean.Grind.Semiring.natCast_mul]
  rw [this]; grind

/-! ## CONV rows (table 28) -/

/-- The opcode a CONV row's FETCH query carries, as a natural number. -/
def convOpN (tr : Trace) (r : Nat) : Nat :=
  0xA7 * cn tr 28 r Conv.fWrap + 0xAD * cn tr 28 r Conv.fExtU + 0xAC * cn tr 28 r Conv.fExtS

theorem conv_rowIn {tr : Trace} {pub : List F} {r : Nat} :
    rowIn Conv.table tr pub 28 r =
      [tr.cell 28 r 0, tr.cell 28 r 1, tr.cell 28 r 2, ((0 : Nat) : F), tr.cell 28 r Conv.kSb,
        tr.cell 28 r Conv.kCid] := by
  simp only [rowIn, Conv.table, Conv.inters, stdState, stateIn, List.cons_append, List.getD_cons_zero,
    List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', Trace.row, cPc, cTs, cS]

theorem conv_rowOut {tr : Trace} {pub : List F} {r : Nat} :
    rowOut Conv.table tr pub 28 r =
      [tr.cell 28 r 0 + ((1 : Nat) : F), tr.cell 28 r 1 + ((1 : Nat) : F), tr.cell 28 r 2 + tr.cell 28 r 4,
        ((0 : Nat) : F), tr.cell 28 r Conv.kSb, tr.cell 28 r Conv.kCid] := by
  simp only [rowOut, Conv.table, Conv.inters, stdState, stateOut, List.cons_append, List.getD_cons_succ,
    List.getD_cons_zero, List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', Expr.eval_add',
    Trace.row, cPc, cTs, cS, cFee]

theorem one_cast : ((1 : Nat) : F) = 1 := rfl
theorem zero_cast : ((0 : Nat) : F) = 0 := rfl

/-- **An active CONV row of a `Holds (wasmBaseM2Air …)` trace.**  Its FETCH answer pins a checked
function `k` and local pc whose instruction is the conversion `.num (convOpN tr r)`, with the row's
fee and height the pc's (all from `checkModuleM2`); its CH effect is `convVal` of the consumed value
(`conv_row_spec`, with the R16 bound of `2·rl` from the lookup); and the six non-spec `RowFacts2`
fields hold. -/
theorem conv_row_m2 (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    (hsendF : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 ≤ 1)
    (hsend : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height 28) (hact : (Conv.act.eval (tr.row pub 28 r)).toNat = 1) :
    (∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = cn tr 28 r cPc ∧
      (X.pfOf k).code[pc]? = some (.num (convOpN tr r)) ∧ isConvOp (convOpN tr r) = true ∧
      feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧ fee ≤ X.maxFee ∧ cn tr 28 r cFee = fee ∧
      cn tr 28 r cH = (X.ckOf k).heights[pc]?.getD 0) ∧
    (∀ {i tp : Nat} {x : Val}, isNum x →
      decMsg [((0 : Nat) : F), (v Conv.kSb + v cH - 1).eval (tr.row pub 28 r),
        ((cn tr 28 r Conv.fWrap : Nat) : F), ((cn tr 28 r Conv.a : Nat) : F),
        ((cn tr 28 r (Conv.a + 1) : Nat) : F), ((cn tr 28 r (Conv.a + 2) : Nat) : F),
        ((cn tr 28 r (Conv.a + 3) : Nat) : F), ((cn tr 28 r Conv.ta : Nat) : F)] = enc 0 i x tp →
      rowCons Conv.table tr pub 28 r = [enc 0 i x tp] ∧
      rowProd Conv.table tr pub 28 r = [enc 0 i (convVal (convOpN tr r) x) (cn tr 28 r cTs)]) ∧
    (rowIn Conv.table tr pub 28 r).getD 3 0 = 0 ∧
    lvl (rowOut Conv.table tr pub 28 r) = lvl (rowIn Conv.table tr pub 28 r) + 1 ∧
    (∃ fee, fee ≤ X.maxFee ∧
      gasF (rowOut Conv.table tr pub 28 r) = gasF (rowIn Conv.table tr pub 28 r) + (fee : F)) ∧
    (∀ x ∈ rowCons Conv.table tr pub 28 r, ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowIn Conv.table tr pub 28 r)) ∧
    (∀ x ∈ rowProd Conv.table tr pub 28 r, x.tp < P ∧
      ((x.tp : Nat) : F) = lvl (rowIn Conv.table tr pub 28 r)) ∧
    (rowProd Conv.table tr pub 28 r).Nodup := by
  have hP' := P_val
  have ht : 28 < (wasmBaseM2Air nloc ngl).tables.length := by rw [m2_air_len]; decide
  have hT := m2_t28 nloc ngl
  have hc := table_constr_eq H ht Conv.table hT hr
  have hPr := rowNat_lt tr 28 r
  obtain ⟨hfl, -, -, -⟩ := conv_row_facts hc hact
  have hop : isConvOp (convOpN tr r) = true := by
    simp only [convOpN, isConvOp, Bool.or_eq_true, beq_iff_eq]
    rcases hfl with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> rw [a, b, c] <;> simp
  have hopP : convOpN tr r < P := by
    have := isConvOp_cases hop; omega
  -- interactions of the row, as occurrences
  have occ : ∀ i ∈ Conv.inters, (i.bus, i.send, i.msg.map (·.eval (tr.row pub 28 r)),
      (i.count.eval (tr.row pub 28 r)).toNat) ∈ occs (wasmBaseM2Air nloc ngl) tr pub := by
    intro i hi
    refine row_occ ht hr ?_
    rw [hT]; exact hi
  -- the FETCH pin
  have hfo := occ (fetch (v cPc) Conv.op (v cH) (v cFee) zeros4 Conv.act) (by simp [Conv.inters, stdState])
  have hopE : Conv.op.eval (tr.row pub 28 r) = ((convOpN tr r : Nat) : F) := by
    simp only [Conv.op, convOpN, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', conv_col_eval,
      Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
  simp only [fetch, zeros4, List.cons_append, List.nil_append, List.map_cons, List.map_nil, hact, hopE,
    Expr.eval_ofNat', conv_col_eval] at hfo
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hfeq, hheq, hfle⟩ :=
    m2_fetch_conv X H hcode hsendF (hPr _) (hPr _) (hPr _) hop hfo
  refine ⟨⟨k, pc, fee, hk, hpc, hoff, hins, hop, hfee, hfle, hfeq, hheq⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the CH effect
    intro i tp x hx hin
    refine conv_row_spec hc hact (fun h1 => ?_) hx hin
    have hro := occ (r16 (2 * v Conv.rl) (v Conv.fExtS)) (by simp [Conv.inters])
    simp only [r16, List.map_cons, List.map_nil, Expr.eval_mul', Expr.eval_ofNat', conv_col_eval] at hro
    have hcnt : (((cn tr 28 r Conv.fExtS : Nat) : F)).toNat = 1 := by
      rw [Fp.toNat_cast_of_lt (hPr _)]; exact h1
    rw [hcnt] at hro
    obtain ⟨y, hy, hyl⟩ := m2_r16 H hsend hro rfl rfl rfl
    simp only [List.cons.injEq, and_true] at hy
    rw [← Lean.Grind.Semiring.natCast_mul] at hy
    rw [← hy, Fp.toNat_cast] at hyl
    exact hyl
  · rw [conv_rowIn]; rfl
  · rw [conv_rowIn, conv_rowOut]; simp only [lvl, List.getD_cons_succ, List.getD_cons_zero, one_cast]
  · refine ⟨fee, hfle, ?_⟩
    rw [conv_rowIn, conv_rowOut]
    simp only [gasF, List.getD_cons_succ, List.getD_cons_zero]
    rw [cell_cast tr 28 r 4]
    have : rowNat tr 28 r 4 = fee := hfeq
    rw [this]
  · -- consT from the time check
    intro x hx
    rw [conv_row_cons hact] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    have h1 := occ ((timeChk (v cTs) (v Conv.ta) (v Conv.ha) Conv.act)[0]'(by simp [timeChk]))
      (by simp [Conv.inters, timeChk])
    have h2 := occ ((timeChk (v cTs) (v Conv.ta) (v Conv.ha) Conv.act)[1]'(by simp [timeChk]))
      (by simp [Conv.inters, timeChk])
    simp only [timeChk, r16, B16, List.getElem_cons_zero, List.getElem_cons_succ, List.map_cons,
      List.map_nil, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', conv_col_eval, hact] at h1 h2
    obtain ⟨n, hn, he⟩ := m2_time_chk H hsend h1 h2
    refine ⟨n, hn, ?_⟩
    rw [conv_rowIn]
    simp only [decMsg, List.getD_cons_succ, List.getD_cons_zero, lvl]
    rw [Fp.toNat_cast_of_lt (hPr _)] at he ⊢
    rw [he, cell_cast tr 28 r 1]; rfl
  · intro x hx
    rw [conv_row_prod hact] at hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    simp only [decMsg, List.getD_cons_succ, List.getD_cons_zero]
    rw [Fp.toNat_cast_of_lt (hPr _), conv_rowIn]
    refine ⟨hPr _, ?_⟩
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero]
    rw [cell_cast tr 28 r 1]; rfl
  · rw [conv_row_prod hact]; simp

/-! ## UNREACH rows (table 29) -/

theorem unreach_rowIn {tr : Trace} {pub : List F} {r : Nat} :
    rowIn Unreach.table tr pub 29 r =
      [tr.cell 29 r 0, tr.cell 29 r 1, tr.cell 29 r 2, ((0 : Nat) : F), tr.cell 29 r Unreach.kSb,
        tr.cell 29 r Unreach.kCid] := by
  simp only [rowIn, Unreach.table, Unreach.inters, stateIn, List.getD_cons_zero,
    List.map_cons, List.map_nil, v, Expr.eval_col, Expr.eval_ofNat', Trace.row, cPc, cTs, cS]

/-- **An active UNREACH row of a `Holds (wasmBaseM2Air …)` trace.**  Its FETCH answer pins a checked
function `k` and local pc whose instruction is `unreachable` (with the row's fee and height the pc's);
it consumes and produces nothing; its STATE output carries `halted = 2`; and the `RowFacts2` fields
`halt0`, `tsOut`, `gasOut` hold (`consT`, `prodT`, `prodNd` are trivial: no CH traffic). -/
theorem unreach_row_m2 (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    (hsendF : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height 29) (hact : ((v Unreach.act).eval (tr.row pub 29 r)).toNat = 1) :
    (∃ k pc fee, k < X.nf ∧ pc < (X.pfOf k).code.size ∧ X.offOf k + pc = cn tr 29 r cPc ∧
      (X.pfOf k).code[pc]? = some .unreachable ∧
      feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee ∧ fee ≤ X.maxFee ∧ cn tr 29 r cFee = fee ∧
      cn tr 29 r cH = (X.ckOf k).heights[pc]?.getD 0) ∧
    rowCons Unreach.table tr pub 29 r = [] ∧ rowProd Unreach.table tr pub 29 r = [] ∧
    (rowOut Unreach.table tr pub 29 r).getD 3 0 = ((2 : Nat) : F) ∧
    (rowIn Unreach.table tr pub 29 r).getD 3 0 = 0 ∧
    lvl (rowOut Unreach.table tr pub 29 r) = lvl (rowIn Unreach.table tr pub 29 r) + 1 ∧
    (∃ fee, fee ≤ X.maxFee ∧
      gasF (rowOut Unreach.table tr pub 29 r) = gasF (rowIn Unreach.table tr pub 29 r) + (fee : F)) := by
  have ht : 29 < (wasmBaseM2Air nloc ngl).tables.length := by rw [m2_air_len]; decide
  have hT := m2_t29 nloc ngl
  have hPr := rowNat_lt tr 29 r
  have hfo := row_occ (pub := pub) ht hr
    (i := fetch (v cPc) (Expr.c opUnreach) (v cH) (v cFee) zeros4 (v Unreach.act))
    (by rw [hT]; simp [Unreach.table, Unreach.inters])
  have hact' : (((cn tr 29 r Unreach.act : Nat) : F)).toNat = 1 := by rw [← conv_col_eval]; exact hact
  simp only [fetch, zeros4, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
    Expr.eval_ofNat', Expr.eval_c, conv_col_eval, hact'] at hfo
  obtain ⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hfeq, hheq, hfle⟩ :=
    m2_fetch_unreach X H hcode hsendF (hPr _) (hPr _) (hPr _) hfo
  obtain ⟨hcons, hprod, hout⟩ := unreach_row hact
  refine ⟨⟨k, pc, fee, hk, hpc, hoff, hins, hfee, hfle, hfeq, hheq⟩, hcons, hprod, ?_, ?_, ?_, ?_⟩
  · rw [hout]; rfl
  · rw [unreach_rowIn]; rfl
  · rw [unreach_rowIn, hout]
    simp only [lvl, List.getD_cons_succ, List.getD_cons_zero, one_cast, cell_cast]; rfl
  · refine ⟨fee, hfle, ?_⟩
    rw [unreach_rowIn, hout]
    simp only [gasF, List.getD_cons_succ, List.getD_cons_zero, cell_cast]
    have e : cn tr 29 r cFee = fee := hfeq
    rw [e]; rfl

/-! ## Spec steps over `M2Ctx` -/

/-- **One spec step at a checked pc** charges the pc's fee and executes its instruction (the
`M2Ctx` counterpart of `Step.lean:step_eq_exec`, with the gas facts as plain hypotheses instead of a
`RelW`). -/
theorem M2Ctx.step_eq_exec (X : M2Ctx) {s : St} {f : Frame} {rest : List Frame} {k pc fee : Nat}
    {ins : Instr} (hfr : s.frames = f :: rest) (hk : k < X.nf) (hfn : f.fn = X.fnOf k) (hpcf : f.pc = pc)
    (hins : (X.pfOf k).code[pc]? = some ins) (hfee : feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee)
    (hle : X.R * fee ≤ s.gas.g) (hlt : X.R * fee < u64Bound) :
    step X.cfg X.p s =
      exec X.cfg X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f (X.pfOf k) ins := by
  have hpf : X.p.funcs[f.fn]? = some (X.pfOf k) := by rw [hfn]; exact (X.factsOf hk).func
  have hcode : (X.pfOf k).code[f.pc]? = some ins := by rw [hpcf]; exact hins
  cases hg' : (X.pfOf k).gas[pc]? with
  | none => simp [feeUnits, hg'] at hfee
  | some e =>
    cases e with
    | none =>
      simp only [feeUnits, hg', Option.some.injEq] at hfee
      subst hfee
      have hge : (X.pfOf k).gas[f.pc]? = some none := by rw [hpcf]; exact hg'
      rw [Nat.mul_zero, Nat.sub_zero, show ({ s with gas := { s.gas with g := s.gas.g } } : St) = s from rfl]
      simp only [step, hfr, hpf, hcode, hge]
    | some kf =>
      obtain ⟨kk, fe⟩ := kf
      simp only [feeUnits, hg'] at hfee
      split at hfee
      · rename_i hc
        obtain ⟨hl, hR, hmod, _⟩ := hc
        simp only [Option.some.injEq] at hfee
        have hc : fe.c = X.R * fee := by
          rw [← hfee]; unfold M2Ctx.R; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
        have hge : (X.pfOf k).gas[f.pc]? = some (some (kk, fe)) := by rw [hpcf]; exact hg'
        have hamt : ∀ n, n * fe.l + fe.c = X.R * fee := by intro n; rw [hl, hc]; simp
        have hlt' : ¬ (X.R * fee ≥ u64Bound) := by omega
        have hle' : ¬ (X.R * fee > s.gas.g) := by omega
        simp only [step, hfr, hpf, hcode, hge, charge, hamt, hlt', hle', ite_false]
      · simp at hfee

/-- **The spec step of a conversion** at an M2-checked pc: it continues with the stack top replaced by
`convVal op` of it, the frame at `pc + 1`, and the fee charged; memory, globals and the stack budget
are untouched. -/
theorem M2Ctx.step_conv_spec (X : M2Ctx) {s : St} {f : Frame} {rest : List Frame} {k pc fee op : Nat}
    (hfr : s.frames = f :: rest) (hk : k < X.nf) (hfn : f.fn = X.fnOf k) (hpcf : f.pc = pc)
    (hins : (X.pfOf k).code[pc]? = some (.num op)) (hop : isConvOp op = true)
    (hfee : feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee)
    (hle : X.R * fee ≤ s.gas.g) (hlt : X.R * fee < u64Bound) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      s'.stack = s.stack.pop.push (convVal op (s.stack.back?.getD (.i32 0))) ∧
      s'.frames = { f with pc := pc + 1 } :: rest ∧ s'.gas.g = s.gas.g - X.R * fee ∧
      s'.pages = s.pages ∧ s'.globals = s.globals ∧ s'.stackRem = s.stackRem := by
  rw [X.step_eq_exec hfr hk hfn hpcf hins hfee hle hlt]
  simp only [exec, execNum_conv _ _ hop]
  refine ⟨_, rfl, ?_⟩
  simp only [pushV, setFrame, hfr, hpcf]
  simp

/-- **The spec step of `unreachable`** at an M2-checked pc: it aborts with `WasmTrap(Unreachable)`
after charging the pc's fee. -/
theorem M2Ctx.step_unreach_spec (X : M2Ctx) {s : St} {f : Frame} {rest : List Frame} {k pc fee : Nat}
    (hfr : s.frames = f :: rest) (hk : k < X.nf) (hfn : f.fn = X.fnOf k) (hpcf : f.pc = pc)
    (hins : (X.pfOf k).code[pc]? = some .unreachable)
    (hfee : feeUnits X.cfg (X.pfOf k).gas[pc]? = some fee)
    (hle : X.R * fee ≤ s.gas.g) (hlt : X.R * fee < u64Bound) :
    step X.cfg X.p s =
      .abort { s with gas := { s.gas with g := s.gas.g - X.R * fee } } (trapStr "Unreachable") := by
  rw [X.step_eq_exec hfr hk hfn hpcf hins hfee hle hlt]
  simp [exec]

/-! ## Row ↔ step -/

/-- **A CONV row and the spec step it stands for.**  Let the spec state's top frame be at the row's pc
(`X.offOf k' + pc' = pc` cell, `k'` checked), with the fee affordable, and let the row consume the
stack top: `enc 0 (n − 1) x tp` with `x` the spec stack top.  Then the spec step continues, the new
stack top is `convVal op x`, and the row's produced message is exactly the encoding of that new top at
the same slot, at the row's time. -/
theorem conv_row_step_m2 (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    (hsendF : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 ≤ 1)
    (hsend : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height 28) (hact : (Conv.act.eval (tr.row pub 28 r)).toNat = 1)
    {s : St} {f : Frame} {rest : List Frame} {k' pc' tp : Nat}
    (hfr : s.frames = f :: rest) (hk' : k' < X.nf) (hpc' : pc' < (X.pfOf k').code.size)
    (hfn : f.fn = X.fnOf k') (hpcf : f.pc = pc') (hgpc : X.offOf k' + pc' = cn tr 28 r cPc)
    (hle : X.R * cn tr 28 r cFee ≤ s.gas.g) (hlt : X.R * cn tr 28 r cFee < u64Bound)
    (hnum : isNum (s.stack.back?.getD (.i32 0)))
    (hin : decMsg [((0 : Nat) : F), (v Conv.kSb + v cH - 1).eval (tr.row pub 28 r),
        ((cn tr 28 r Conv.fWrap : Nat) : F), ((cn tr 28 r Conv.a : Nat) : F),
        ((cn tr 28 r (Conv.a + 1) : Nat) : F), ((cn tr 28 r (Conv.a + 2) : Nat) : F),
        ((cn tr 28 r (Conv.a + 3) : Nat) : F), ((cn tr 28 r Conv.ta : Nat) : F)] =
      enc 0 (s.stack.size - 1) (s.stack.back?.getD (.i32 0)) tp) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      s'.stack = s.stack.pop.push (convVal (convOpN tr r) (s.stack.back?.getD (.i32 0))) ∧
      s'.frames = { f with pc := pc' + 1 } :: rest ∧ s'.gas.g = s.gas.g - X.R * cn tr 28 r cFee ∧
      rowCons Conv.table tr pub 28 r = [enc 0 (s.stack.size - 1) (s.stack.back?.getD (.i32 0)) tp] ∧
      rowProd Conv.table tr pub 28 r =
        [enc 0 (s'.stack.size - 1) (s'.stack.back?.getD (.i32 0)) (cn tr 28 r cTs)] := by
  obtain ⟨⟨k, pc, fee, hk, hpc, hoff, hins, hop, hfee, -, hfeq, -⟩, hspec, -⟩ :=
    conv_row_m2 X H hcode hsendF hsend hr hact
  obtain ⟨rfl, rfl⟩ := X.loc_unique hk' hpc' hk hpc (by rw [hgpc, hoff])
  rw [hfeq] at hle hlt ⊢
  obtain ⟨s', hst, hstk', hfr', hg', -⟩ := X.step_conv_spec hfr hk hfn hpcf hins hop hfee hle hlt
  obtain ⟨hc, hp⟩ := hspec hnum hin
  refine ⟨s', hst, hstk', hfr', hg', hc, ?_⟩
  rw [hp, hstk']
  simp only [Array.size_push, Array.size_pop, Array.back?_push, Option.getD_some]
  congr 2

/-- **An UNREACH row and the spec step it stands for**: at the row's pc the spec step aborts with
`WasmTrap(Unreachable)` after charging the row's fee, and the row's STATE output says `halted = 2`
with no CH traffic. -/
theorem unreach_row_step_m2 (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hcode : CodeOKM2 X tr)
    (hsendF : ∀ o ∈ occs (wasmBaseM2Air nloc ngl) tr pub, o.1 = busFetch → o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height 29) (hact : ((v Unreach.act).eval (tr.row pub 29 r)).toNat = 1)
    {s : St} {f : Frame} {rest : List Frame} {k' pc' : Nat}
    (hfr : s.frames = f :: rest) (hk' : k' < X.nf) (hpc' : pc' < (X.pfOf k').code.size)
    (hfn : f.fn = X.fnOf k') (hpcf : f.pc = pc') (hgpc : X.offOf k' + pc' = cn tr 29 r cPc)
    (hle : X.R * cn tr 29 r cFee ≤ s.gas.g) (hlt : X.R * cn tr 29 r cFee < u64Bound) :
    step X.cfg X.p s =
      .abort { s with gas := { s.gas with g := s.gas.g - X.R * cn tr 29 r cFee } } (trapStr "Unreachable") ∧
    rowCons Unreach.table tr pub 29 r = [] ∧ rowProd Unreach.table tr pub 29 r = [] ∧
    (rowOut Unreach.table tr pub 29 r).getD 3 0 = ((2 : Nat) : F) := by
  obtain ⟨⟨k, pc, fee, hk, hpc, hoff, hins, hfee, -, hfeq, -⟩, hc, hp, hh, -⟩ :=
    unreach_row_m2 X H hcode hsendF hr hact
  obtain ⟨rfl, rfl⟩ := X.loc_unique hk' hpc' hk hpc (by rw [hgpc, hoff])
  rw [hfeq] at hle hlt ⊢
  exact ⟨X.step_unreach_spec hfr hk hfn hpcf hins hfee hle hlt, hc, hp, hh⟩

#print axioms conv_row_m2
#print axioms unreach_row_m2
#print axioms M2Ctx.step_eq_exec
#print axioms M2Ctx.step_conv_spec
#print axioms M2Ctx.step_unreach_spec
#print axioms conv_row_step_m2
#print axioms unreach_row_step_m2
#print axioms m2_fetch
#print axioms m2_r16
#print axioms m2_fetch_conv
#print axioms m2_fetch_unreach
#print axioms m2_time_chk

end WasmBase
