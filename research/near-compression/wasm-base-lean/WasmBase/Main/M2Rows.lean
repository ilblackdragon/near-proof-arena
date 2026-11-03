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

#print axioms m2_fetch
#print axioms m2_r16
#print axioms m2_fetch_conv
#print axioms m2_fetch_unreach
#print axioms m2_time_chk

end WasmBase
