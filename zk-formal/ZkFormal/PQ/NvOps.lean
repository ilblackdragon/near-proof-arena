import ZkFormal.PQ.NvProg

/-!
# ZkFormal.PQ.NvOps — per-op ALU row semantics of the exported NvAir

Lane E (E2E M11i), 2026-11-21. Everything is proved from the circuit's own predicate
`NvField.NvHold`, by partial evaluation (`NvAff.affEval`) of the exported constraint and
interaction expressions on a bound program row (as in `NvProg`).

## Row entries

* `rowEnt tr pub r b`: the entries `(count, message)` of NvAir (table 0) at row `r` on bus `b`;
  `tEntries_rows`: NvAir's `tEntries` on bus `b` is the concatenation of the rows' `rowEnt`.
* `live fx L`: the interactions of `L` whose count does **not** partially evaluate to the
  constant `0`, with their count and message forms; `live_filter`: on a row agreeing with `fx`,
  the nonzero-count entries of the row are the nonzero-count values of `live`'s forms. Checked
  against a stated spec (`LiveIs`, by `decide +kernel`), this gives the exact list of
  nonzero-count entries of a row on a bus (`liveIs_row`).

## Per-op semantics (bound program row `y`, `ProgBound`, `ProgWF`, `GlueByteBool`)

* `add_sem` (op 2): `c_y = c_x + c_z` limb-wise (slot-1 / slot-2 reads, constraints `subIdx`).
* `const_sem` (op 4): `c_y = (A, 0, .., 0)`.
* `unit1_sem` (op 7): `c_y = c_x`; one slot-bus entry `(1, [1, K1, K2, 0, c_x[0], 0, 0])`, nothing
  on the job and digest buses (`unit1_mem`: the entry is a row entry).
* `job_sem` (op 14): slot bus `(1, [1, J, 0, 0, NB, 0, 0])`, `(1, [1, J, 1, 0, 0, 0, 0])`; job bus
  `(1, [J, TAG, 1])`; digest bus nothing.
* `dig_sem` (op 17, `NB ∈ {1, 2}`): digest bus `(−1, [J, P, c_y[0..6]])` and, for `NB = 2`,
  `(−1, [J, P + 1, c_y[6..12]])`; nothing on the slot and job buses; for `NB = 1`,
  `c_y[6..12] = 0` (exported constraints 1786–1791 are `ka·h1·g2·(2 − (P1 − 17·2^24))·c_{52+k}`,
  i.e. `(2 − B)·c_{52+k}`: they force the high half to zero exactly when `B ≠ 2`).

## Classification (all 40 ops, `decide +kernel`)

* `alu_slot_job`: every nonzero-count slot-bus entry of a bound ALU row with channel `1` carries
  `P2` (= `K1`) as its second field; `alu_job_job`: every nonzero-count job-bus entry carries `P2`
  as its first field; `nop_silent`: a `Nop` ALU row has only zero counts on buses 0, 1, 2.
* **Caveat (Nop)**: a program row `⟨0, A, 0, K1, K2⟩` has `P1 = 0`, so the exported constraint
  `(1 − ka)·P1` does not force it to be an ALU row; the row lemmas therefore take
  `0 < op ∨ 0 < B ∨ ka = 1` (`AluHyp`). For `op ≥ 1` it is automatic.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.NvOps

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.NvAirExport ZkFormal.PQ.NvCircuitExport
open ZkFormal.PQ.NvTape ZkFormal.PQ.NvAff ZkFormal.PQ.NvField ZkFormal.PQ.NvProg

set_option maxRecDepth 100000

/-! ## Row entries -/

/-- The result cell of row `y` (12 limbs, columns 46..57). -/
def cellOf (tr : Trace Fp) (y : Nat) : List Fp := (List.range 12).map fun k => cv tr 0 y (46 + k)

theorem cellOf_eq (tr : Trace Fp) (y : Nat) : cellOf tr y =
    [cv tr 0 y 46, cv tr 0 y 47, cv tr 0 y 48, cv tr 0 y 49, cv tr 0 y 50, cv tr 0 y 51,
     cv tr 0 y 52, cv tr 0 y 53, cv tr 0 y 54, cv tr 0 y 55, cv tr 0 y 56, cv tr 0 y 57] := rfl

/-- The entries of NvAir (table 0) at row `r` on bus `b`. -/
def rowEnt (tr : Trace Fp) (pub : List Fp) (r b : Nat) : List (Fp × List Fp) :=
  ((tableOf nvNodes nvConstraintIdx nvInteractionIdx).ints.filter fun i => i.bus == b).map
    fun i => (i.count.eval tr 0 r pub, i.msg.map fun e => e.eval tr 0 r pub)

theorem tEntries_rows (tr : Trace Fp) (pub : List Fp) (b : Nat) :
    tEntries (tableOf nvNodes nvConstraintIdx nvInteractionIdx) tr 0 pub b =
      (List.range (tr.height 0)).flatMap fun r => rowEnt tr pub r b := rfl

/-- NvAir's interactions on bus `b` (exported). -/
def busIdx (b : Nat) : List (Nat × Nat × List Nat) := nvInteractionIdx.filter fun x => x.1 == b

/-- The value of an exported interaction at row `r`. -/
def ent (tr : Trace Fp) (pub : List Fp) (r : Nat) (x : Nat × Nat × List Nat) : Fp × List Fp :=
  ((dag x.2.1).eval tr 0 r pub, x.2.2.map fun m => (dag m).eval tr 0 r pub)

theorem rowEnt_eq (tr : Trace Fp) (pub : List Fp) (r b : Nat) :
    rowEnt tr pub r b = (busIdx b).map (ent tr pub r) := by
  unfold rowEnt busIdx
  rw [tableOf_filter, List.map_map]
  simp only [dagOf_nv, List.map_map, Function.comp_def]
  rfl

/-! ## The live (not constant-zero count) interactions -/

def mapAff (fx : Fix) : List Nat → Option (List Aff)
  | [] => some []
  | m :: ms => match affEval fx (dag m), mapAff fx ms with
    | some a, some l => some (a :: l)
    | _, _ => none

/-- The interactions whose count is not the constant `0`, with count and message forms. -/
def live (fx : Fix) : List (Nat × Nat × List Nat) → Option (List (Aff × List Aff))
  | [] => some []
  | x :: xs => match affEval fx (dag x.2.1) with
    | none => none
    | some c => if c.vs.isEmpty && c.c == 0 then live fx xs else
      match mapAff fx x.2.2, live fx xs with
      | some ms, some l => some ((c, ms) :: l)
      | _, _ => none

def evA (val : Nat → Bool → Fp) (p : Aff × List Aff) : Fp × List Fp :=
  (p.1.eval val, p.2.map fun a => a.eval val)

section Live
variable {fx : Fix} {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem mapAff_eval (hag : Agrees fx (rowEnv tr 0 r pub)) :
    ∀ ms l, mapAff fx ms = some l →
      ms.map (fun m => (dag m).eval tr 0 r pub) = l.map fun a => a.eval (rowVal tr 0 r pub)
  | [], l, h => by
    simp only [mapAff, Option.some.injEq] at h; subst h; rfl
  | m :: ms, l, h => by
    simp only [mapAff] at h
    cases ha : affEval fx (dag m) with
    | none => rw [ha] at h; simp at h
    | some a =>
      cases hl : mapAff fx ms with
      | none => rw [ha, hl] at h; simp at h
      | some l' =>
        rw [ha, hl] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.map_cons, affEval_row fx tr 0 r pub hag _ a ha, mapAff_eval hag ms l' hl]

theorem live_filter (hag : Agrees fx (rowEnv tr 0 r pub)) :
    ∀ L S, live fx L = some S →
      (L.map (ent tr pub r)).filter (fun e => e.1 ≠ 0) =
        (S.map (evA (rowVal tr 0 r pub))).filter (fun e => e.1 ≠ 0)
  | [], S, h => by
    simp only [live, Option.some.injEq] at h; subst h; rfl
  | x :: xs, S, h => by
    simp only [live] at h
    cases hc : affEval fx (dag x.2.1) with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only at h
      have ec := affEval_row fx tr 0 r pub hag _ c hc
      by_cases hz : (c.vs.isEmpty && c.c == 0) = true
      · rw [if_pos hz] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at hz
        have e0 : (ent tr pub r x).1 = 0 := by
          show (dag x.2.1).eval tr 0 r pub = 0
          rw [ec, Aff.eval, sumV_nil_of _ hz.1, hz.2]; grind
        rw [List.map_cons, List.filter_cons_of_neg (by simp [e0])]
        exact live_filter hag xs S h
      · rw [if_neg hz] at h
        cases hm : mapAff fx x.2.2 with
        | none => rw [hm] at h; simp at h
        | some ms =>
          cases hl : live fx xs with
          | none => rw [hm, hl] at h; simp at h
          | some l =>
            rw [hm, hl] at h
            simp only [Option.some.injEq] at h
            subst h
            have ee : ent tr pub r x = evA (rowVal tr 0 r pub) (c, ms) := by
              unfold ent evA
              rw [ec, mapAff_eval hag _ _ hm]
            rw [List.map_cons, List.map_cons, ee, List.filter_cons, List.filter_cons,
              live_filter hag xs l hl]

end Live

/-! ## Specs of the live entries -/

/-- An expected affine form `c + Σ k·x_v`. -/
abbrev Form := Fp × List (Nat × Bool) × List Fp

def evF (val : Nat → Bool → Fp) (f : Form) : Fp := f.1 + lin val f.2.1 f.2.2

def evSp (val : Nat → Bool → Fp) (s : Form × List Form) : Fp × List Fp :=
  (evF val s.1, s.2.map (evF val))

def FormsOK : List Aff → List Form → Bool
  | [], [] => true
  | a :: as, f :: fs => a.Is f.1 f.2.1 f.2.2 && FormsOK as fs
  | _, _ => false

def SpecOK : List (Aff × List Aff) → List (Form × List Form) → Bool
  | [], [] => true
  | p :: ps, s :: ss => p.1.Is s.1.1 s.1.2.1 s.1.2.2 && FormsOK p.2 s.2 && SpecOK ps ss
  | _, _ => false

theorem formsOK_eval (val : Nat → Bool → Fp) :
    ∀ as fs, FormsOK as fs = true → as.map (fun a => a.eval val) = fs.map (evF val)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [FormsOK] at h
  | _ :: _, [], h => by simp [FormsOK] at h
  | a :: as, f :: fs, h => by
    simp only [FormsOK, Bool.and_eq_true] at h
    simp only [List.map_cons, aff_is_eval a _ _ _ h.1 val, formsOK_eval val as fs h.2, evF]

theorem specOK_eval (val : Nat → Bool → Fp) :
    ∀ S ss, SpecOK S ss = true → S.map (evA val) = ss.map (evSp val)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [SpecOK] at h
  | _ :: _, [], h => by simp [SpecOK] at h
  | p :: ps, s :: ss, h => by
    simp only [SpecOK, Bool.and_eq_true] at h
    simp only [List.map_cons, evA, evSp, aff_is_eval p.1 _ _ _ h.1.1 val,
      formsOK_eval val _ _ h.1.2, specOK_eval val ps ss h.2, evF]

/-- The live entries of bus `b` under `fx` are the spec. -/
def LiveIs (fx : Fix) (b : Nat) (ss : List (Form × List Form)) : Bool :=
  match live fx (busIdx b) with
  | some S => SpecOK S ss
  | none => false

/-- **The nonzero-count entries of a row on a bus, from a checked spec.** -/
theorem liveIs_row {fx : Fix} {tr : Trace Fp} {r : Nat} {pub : List Fp}
    (hag : Agrees fx (rowEnv tr 0 r pub)) {b : Nat} {ss : List (Form × List Form)}
    (h : LiveIs fx b ss = true) :
    (rowEnt tr pub r b).filter (·.1 ≠ 0) = (ss.map (evSp (rowVal tr 0 r pub))).filter (·.1 ≠ 0) := by
  unfold LiveIs at h
  cases hl : live fx (busIdx b) with
  | none => rw [hl] at h; simp at h
  | some S =>
    rw [hl] at h
    rw [rowEnt_eq, live_filter hag _ S hl, specOK_eval _ S ss h]

/-! ## Evaluating spec forms -/

theorem evF_c (val : Nat → Bool → Fp) (c : Fp) : evF val (c, [], []) = c := by
  simp only [evF, lin]; grind

theorem evF_cv (val : Nat → Bool → Fp) (c : Fp) (v : Nat × Bool) :
    evF val (c, [v], [1]) = c + val v.1 v.2 := by
  simp only [evF, lin]; grind

theorem fp_zero_add (x : Fp) : (0 : Fp) + x = x := by grind

theorem dec_one : decide ((1 : Fp) ≠ 0) = true := by decide
theorem dec_negone : decide ((-1 : Fp) ≠ 0) = true := by decide

/-- Spec shorthands: a constant, a column. -/
abbrev fc (c : Fp) : Form := (c, [], [])
abbrev fv (c : Nat) : Form := (0, [(c, false)], [1])

/-! ## Bound ALU rows -/

/-- The row is an ALU row: forced unless the instruction is `⟨0, A, 0, ..⟩` (`P1 = 0`). -/
def AluHyp (tr : Trace Fp) (prog : List Instr) (y : Nat) (hy : y < prog.length) : Prop :=
  0 < prog[y].op ∨ 0 < prog[y].b ∨ cv tr 0 y 0 = 1

section Rows
variable {tr : Trace Fp} {pub : List Fp} {prog : List Instr}

theorem ka_of_prog (hh : NvHold pub tr) (hG : GlueByteBool tr pub) (hP : ProgBound tr prog)
    (hW : ProgWF prog) {y : Nat} (hy : y < prog.length) (hA : AluHyp tr prog y hy) :
    cv tr 0 y 0 = 1 := by
  rcases hA with h | h | h
  · exact (bound_row hh hG hP hW hy h).2.1
  · have hr : y < tr.height 0 := Nat.lt_of_lt_of_le hy hP.1
    obtain ⟨hop', hb⟩ := hW _ (List.getElem_mem hy)
    refine ka_of_p1 (nvConstr_of hh) hr ?_
    rw [(hP.2 y hy).2.1]
    intro e
    have := cast_inj (a := prog[y].b + prog[y].op * 2 ^ 24) (b := 0) (by unfold P; omega)
      (by decide) (e.trans natCast_zero.symm)
    omega
  · exact h

/-- **A bound ALU row agrees with its op's fixing.** -/
theorem prog_agrees (hh : NvHold pub tr) (hG : GlueByteBool tr pub) (hP : ProgBound tr prog)
    (hW : ProgWF prog) {y : Nat} (hy : y < prog.length) (hka : cv tr 0 y 0 = 1) :
    y < tr.height 0 ∧ Agrees (fxOp (prog[y].op % 8) (prog[y].op / 8)) (rowEnv tr 0 y pub) := by
  have hr : y < tr.height 0 := Nat.lt_of_lt_of_le hy hP.1
  obtain ⟨hop', hb⟩ := hW _ (List.getElem_mem hy)
  obtain ⟨hx, hy'⟩ := alu_op hh hG hr hka _ (hP.2 y hy) hop' hb
  exact ⟨hr, agrees_op (nvConstr_of hh) hr hka hx hy'⟩

/-- `fxOp` with `P1` fixed too. -/
def fxB (a b v : Nat) : Fix := fun c nx =>
  if c = 7 ∧ nx = false then some ((v : Nat) : Fp) else fxOp a b c nx

theorem agrees_fxB {a b v r : Nat} (hag : Agrees (fxOp a b) (rowEnv tr 0 r pub))
    (h7 : cv tr 0 r 7 = ((v : Nat) : Fp)) : Agrees (fxB a b v) (rowEnv tr 0 r pub) := by
  intro c nx w hw
  unfold fxB at hw
  by_cases h : c = 7 ∧ nx = false
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true, Option.some.injEq] at hw
    show rowVal tr 0 r pub 7 false = w
    rw [rowVal_col tr 0 r pub 7 (by decide), ← hw]
    exact h7
  · rw [if_neg h] at hw
    exact hag c nx w hw

/-- A constraint on a row agreeing with `fx`, checked to be an `Is`-form. -/
theorem cons_lin {fx : Fix} (hc : NvConstr tr 0 pub) {r : Nat} (hr : r < tr.height 0)
    (hag : Agrees fx (rowEnv tr 0 r pub)) {j : Nat} (hj : j ∈ nvConstraintIdx) {c : Fp}
    {vars : List (Nat × Bool)} {ks : List Fp} (he : EvalIs fx (dag j) c vars ks = true) :
    c + lin (rowVal tr 0 r pub) vars ks = 0 := by
  have e := hc r hr j hj
  rwa [evalIs_row fx tr 0 r pub hag _ _ _ _ he] at e

/-- **A count-1 read slot**: the cell at the read address is the slot's message. -/
theorem slot_read {fx : Fix} (hc : NvConstr tr 0 pub) (hb : MemBalance tr 0 pub)
    (hH : tr.height 0 ≤ 2 ^ 24) {r : Nat} (hr : r < tr.height 0)
    (hag : Agrees fx (rowEnv tr 0 r pub)) (cm : Nat × List Nat) (hcm : cm ∈ memIdx)
    (c0 : Fp) (v0 base : Nat) (hv0 : v0 < 1000) (hbase : base + 12 ≤ 1000)
    (hcnt : EvalIs fx (dag cm.1) 1 [] [] = true) (hms : ExpsOK fx cm.2 (rdExps c0 v0 base) = true)
    {n : Nat} (hn : n < 2 ^ 24) (hval : c0 + cv tr 0 r v0 = ((n : Nat) : Fp)) :
    ∀ k, k < 12 → cv tr 0 n (46 + k) = cv tr 0 r (base + k) := by
  have ea := slot_mem (pub := pub) hr cm hcm
  rw [evalIs_row _ tr 0 r pub hag _ _ _ _ hcnt, lin_nil, expsOK_eval _ hag _ _ hms,
    rdExps_eval tr r pub _ _ _ hv0 hbase, hval] at ea
  have ra := (mem_read hc hb hH ea hn).2
  intro k hk
  have := congrArg (fun l : List Fp => l.getD k 0) ra
  simpa [List.getD_eq_getElem?_getD, List.getElem?_range hk] using this

theorem slot1_mem : (4229, slot1Msgs) ∈ memIdx := by rw [memIdx_eq]; simp [slot1Msgs]
theorem slot2_mem : (4281, slot2Msgs) ∈ memIdx := by rw [memIdx_eq]; simp [slot2Msgs]

theorem cast_off (n c : Nat) : -((c : Nat) : Fp) + ((n + c : Nat) : Fp) = ((n : Nat) : Fp) := by
  simp only [Lean.Grind.Semiring.natCast_add]; grind

theorem fp_add_zero_cast (n : Nat) : (0 : Fp) + ((n : Nat) : Fp) = ((n : Nat) : Fp) := by grind

end Rows

/-! ## `Add` (op 2) -/

theorem add_ok :
    EvalIs (fxOp 2 0) (dag 4229) 1 [] [] = true ∧ ExpsOK (fxOp 2 0) slot1Msgs (rdExps 0 6 10) = true ∧
    EvalIs (fxOp 2 0) (dag 4281) 1 [] [] = true ∧
      ExpsOK (fxOp 2 0) slot2Msgs (rdExps (-((2 * 2 ^ 24 : Nat) : Fp)) 7 22) = true ∧
    ∀ k, k < 12 → EvalIs (fxOp 2 0) (dag (subIdx.getD k 0)) 0
      [(46 + k, false), (10 + k, false), (22 + k, false)] [1, -1, -1] = true := by
  decide +kernel

/-- **`Add`: `c_y = c_x + c_z`, limb-wise.** -/
theorem add_sem {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) {x z k1 k2 : Nat} (hi : prog[y] = ⟨2, x, z, k1, k2⟩)
    (hx : x < 2 ^ 24) (hz : z < 2 ^ 24) :
    ∀ k, k < 12 → cv tr 0 y (46 + k) = cv tr 0 x (46 + k) + cv tr 0 z (46 + k) := by
  have hc := nvConstr_of hh
  have hb := memBalance_of hh
  have hH := height_le hh.2.1
  have hka := ka_of_prog hh hG hP hW hy (Or.inl (by simp [hi]))
  obtain ⟨hr, hag⟩ := prog_agrees (pub := pub) hh hG hP hW hy hka
  rw [hi] at hag
  simp only [Nat.reduceMod, Nat.reduceDiv] at hag
  have hag : Agrees (fxOp 2 0) (rowEnv tr 0 y pub) := hag
  have row := hP.2 y hy
  rw [hi] at row
  obtain ⟨c1, m1, c2, m2, cs⟩ := add_ok
  have ra := slot_read hc hb hH hr hag _ slot1_mem 0 6 10 (by decide) (by decide) c1 m1 hx
    (by rw [row.1]; exact fp_add_zero_cast x)
  have rb := slot_read hc hb hH hr hag _ slot2_mem _ 7 22 (by decide) (by decide) c2 m2 hz
    (by rw [row.2.1]; exact cast_off z _)
  intro k hk
  have e := cons_lin hc hr hag (subzero_ok k hk).2.1 (cs k hk)
  simp only [lin, rowVal_col tr 0 y pub _ (show 46 + k < 1000 by omega),
    rowVal_col tr 0 y pub _ (show 10 + k < 1000 by omega),
    rowVal_col tr 0 y pub _ (show 22 + k < 1000 by omega)] at e
  rw [ra k hk, rb k hk]
  grind

/-! ## `Const` (op 4) -/

theorem const_ok :
    EvalIs (fxOp 4 0) (dag (subIdx.getD 0 0)) 0 [(46, false), (6, false)] [1, -1] = true ∧
    ∀ k, k < 11 → EvalIs (fxOp 4 0) (dag (subIdx.getD (k + 1) 0)) 0 [(47 + k, false)] [1] = true := by
  decide +kernel

/-- **`Const`: `c_y = (A, 0, .., 0)`.** -/
theorem const_sem {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) {a b k1 k2 : Nat} (hi : prog[y] = ⟨4, a, b, k1, k2⟩) :
    cv tr 0 y 46 = ((a : Nat) : Fp) ∧ ∀ k, 1 ≤ k → k < 12 → cv tr 0 y (46 + k) = 0 := by
  have hc := nvConstr_of hh
  have hka := ka_of_prog hh hG hP hW hy (Or.inl (by simp [hi]))
  obtain ⟨hr, hag⟩ := prog_agrees (pub := pub) hh hG hP hW hy hka
  rw [hi] at hag
  simp only [Nat.reduceMod, Nat.reduceDiv] at hag
  have hag : Agrees (fxOp 4 0) (rowEnv tr 0 y pub) := hag
  have row := hP.2 y hy
  rw [hi] at row
  obtain ⟨c0, cs⟩ := const_ok
  refine ⟨?_, ?_⟩
  · have e := cons_lin hc hr hag (subzero_ok 0 (by decide)).2.1 c0
    simp only [lin, rowVal_col tr 0 y pub _ (show 46 < 1000 by omega),
      rowVal_col tr 0 y pub _ (show 6 < 1000 by omega)] at e
    rw [← row.1]; grind
  · intro k hk1 hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have e := cons_lin hc hr hag (subzero_ok (m + 1) hk).2.1 (cs m (by omega))
    simp only [lin, rowVal_col tr 0 y pub _ (show 47 + m < 1000 by omega)] at e
    rw [show 46 + (m + 1) = 47 + m by omega]
    grind

/-! ## `Unit1` (op 7) -/

def unit1Bus0 : List (Form × List Form) :=
  [(fc 1, [fc 1, fv 8, fv 9, fc 0, fv 46, fc 0, fc 0])]

theorem unit1_rd :
    EvalIs (fxOp 7 0) (dag 4229) 1 [] [] = true ∧ ExpsOK (fxOp 7 0) slot1Msgs (rdExps 0 6 10) = true ∧
    (∀ k, k < 12 → EvalIs (fxOp 7 0) (dag (subIdx.getD k 0)) 0
      [(46 + k, false), (10 + k, false)] [1, -1] = true) := by
  decide +kernel
theorem unit1_b0 : LiveIs (fxOp 7 0) 0 unit1Bus0 = true := by decide +kernel
theorem unit1_b1 : LiveIs (fxOp 7 0) 1 [] = true := by decide +kernel
theorem unit1_b2 : LiveIs (fxOp 7 0) 2 [] = true := by decide +kernel

/-- **`Unit1`: `c_y = c_x`, and its only nonzero-count entry on buses 0–2 is the slot-bus
send `(1, [1, K1, K2, 0, c_x[0], 0, 0])`.** -/
theorem unit1_sem {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) {x b k1 k2 : Nat} (hi : prog[y] = ⟨7, x, b, k1, k2⟩) (hx : x < 2 ^ 24) :
    cellOf tr y = cellOf tr x ∧
    (rowEnt tr pub y 0).filter (·.1 ≠ 0) =
      [((1 : Fp), [1, ((k1 : Nat) : Fp), ((k2 : Nat) : Fp), 0, cv tr 0 x 46, 0, 0])] ∧
    (rowEnt tr pub y 1).filter (·.1 ≠ 0) = [] ∧ (rowEnt tr pub y 2).filter (·.1 ≠ 0) = [] := by
  have hc := nvConstr_of hh
  have hb := memBalance_of hh
  have hH := height_le hh.2.1
  have hka := ka_of_prog hh hG hP hW hy (Or.inl (by simp [hi]))
  obtain ⟨hr, hag⟩ := prog_agrees (pub := pub) hh hG hP hW hy hka
  rw [hi] at hag
  simp only [Nat.reduceMod, Nat.reduceDiv] at hag
  have hag : Agrees (fxOp 7 0) (rowEnv tr 0 y pub) := hag
  have row := hP.2 y hy
  rw [hi] at row
  obtain ⟨c1, m1, cs⟩ := unit1_rd
  have l0 := unit1_b0
  have ra := slot_read hc hb hH hr hag _ slot1_mem 0 6 10 (by decide) (by decide) c1 m1 hx
    (by rw [row.1]; exact fp_add_zero_cast x)
  have hcell : ∀ k, k < 12 → cv tr 0 y (46 + k) = cv tr 0 x (46 + k) := by
    intro k hk
    have e := cons_lin hc hr hag (subzero_ok k hk).2.1 (cs k hk)
    simp only [lin, rowVal_col tr 0 y pub _ (show 46 + k < 1000 by omega),
      rowVal_col tr 0 y pub _ (show 10 + k < 1000 by omega)] at e
    rw [ra k hk]
    grind
  have hcl : cellOf tr y = cellOf tr x := by
    unfold cellOf
    apply List.map_congr_left
    intro k hk
    exact hcell k (List.mem_range.1 hk)
  refine ⟨hcl, ?_, ?_, ?_⟩
  · rw [liveIs_row hag l0]
    simp only [unit1Bus0, List.map_cons, List.map_nil, evSp, evF_c, evF_cv, fp_zero_add,
      rowVal_col tr 0 y pub 8 (by decide), rowVal_col tr 0 y pub 9 (by decide),
      rowVal_col tr 0 y pub 46 (by decide), List.filter_cons, List.filter_nil, dec_one, ite_true]
    rw [show tr.cell 0 y 8 = _ from row.2.2.1, show tr.cell 0 y 9 = _ from row.2.2.2,
      show tr.cell 0 y 46 = cv tr 0 x 46 from hcell 0 (by decide)]
  · rw [liveIs_row hag unit1_b1]; rfl
  · rw [liveIs_row hag unit1_b2]; rfl

/-- The `Unit1` slot-bus send is an entry of the row. -/
theorem unit1_mem {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) {x b k1 k2 : Nat} (hi : prog[y] = ⟨7, x, b, k1, k2⟩) (hx : x < 2 ^ 24) :
    ((1 : Fp), [1, ((k1 : Nat) : Fp), ((k2 : Nat) : Fp), 0, cv tr 0 x 46, 0, 0]) ∈ rowEnt tr pub y 0 := by
  have h := (unit1_sem hh hG hP hW hy hi hx).2.1
  have : ((1 : Fp), [1, ((k1 : Nat) : Fp), ((k2 : Nat) : Fp), 0, cv tr 0 x 46, 0, 0]) ∈
      (rowEnt tr pub y 0).filter (·.1 ≠ 0) := by rw [h]; exact List.mem_singleton_self _
  exact (List.mem_filter.1 this).1

/-! ## `Job` (op 14) -/

def jobBus0 : List (Form × List Form) :=
  [(fc 1, [fc 1, fv 8, fc 0, fc 0, (-((14 * 2 ^ 24 : Nat) : Fp), [(7, false)], [1]), fc 0, fc 0]),
   (fc 1, [fc 1, fv 8, fc 1, fc 0, fc 0, fc 0, fc 0])]
def jobBus1 : List (Form × List Form) := [(fc 1, [fv 8, fv 6, fc 1])]

theorem job_b0 : LiveIs (fxOp 6 1) 0 jobBus0 = true := by decide +kernel
theorem job_b1 : LiveIs (fxOp 6 1) 1 jobBus1 = true := by decide +kernel
theorem job_b2 : LiveIs (fxOp 6 1) 2 [] = true := by decide +kernel

/-- **`Job`: two slot-bus sends, one job-bus send, nothing on the digest bus.** -/
theorem job_sem {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) {tag nb j k2 : Nat} (hi : prog[y] = ⟨14, tag, nb, j, k2⟩) :
    (rowEnt tr pub y 0).filter (·.1 ≠ 0) =
      [((1 : Fp), [1, ((j : Nat) : Fp), 0, 0, ((nb : Nat) : Fp), 0, 0]),
       ((1 : Fp), [1, ((j : Nat) : Fp), 1, 0, 0, 0, 0])] ∧
    (rowEnt tr pub y 1).filter (·.1 ≠ 0) = [((1 : Fp), [((j : Nat) : Fp), ((tag : Nat) : Fp), 1])] ∧
    (rowEnt tr pub y 2).filter (·.1 ≠ 0) = [] := by
  have hka := ka_of_prog hh hG hP hW hy (Or.inl (by simp [hi]))
  obtain ⟨hr, hag⟩ := prog_agrees (pub := pub) hh hG hP hW hy hka
  rw [hi] at hag
  simp only [Nat.reduceMod, Nat.reduceDiv] at hag
  have hag : Agrees (fxOp 6 1) (rowEnv tr 0 y pub) := hag
  have row := hP.2 y hy
  rw [hi] at row
  refine ⟨?_, ?_, ?_⟩
  · rw [liveIs_row hag job_b0]
    simp only [jobBus0, List.map_cons, List.map_nil, evSp, evF_c, evF_cv, fp_zero_add,
      rowVal_col tr 0 y pub 8 (by decide), rowVal_col tr 0 y pub 7 (by decide),
      List.filter_cons, List.filter_nil, dec_one, ite_true]
    rw [show tr.cell 0 y 8 = _ from row.2.2.1, show tr.cell 0 y 7 = _ from row.2.1, cast_off]
  · rw [liveIs_row hag job_b1]
    simp only [jobBus1, List.map_cons, List.map_nil, evSp, evF_c, evF_cv, fp_zero_add,
      rowVal_col tr 0 y pub 8 (by decide), rowVal_col tr 0 y pub 6 (by decide),
      List.filter_cons, List.filter_nil, dec_one, ite_true]
    rw [show tr.cell 0 y 8 = _ from row.2.2.1, show tr.cell 0 y 6 = _ from row.1]
  · rw [liveIs_row hag job_b2]; rfl

/-! ## `Dig` (op 17) -/

def digLo : Form × List Form := (fc (-1), [fv 8, fv 9, fv 46, fv 47, fv 48, fv 49, fv 50, fv 51])
def digHi : Form × List Form :=
  (fc (-1), [fv 8, (1, [(9, false)], [1]), fv 52, fv 53, fv 54, fv 55, fv 56, fv 57])

/-- `Dig` with `B = 1`: one digest-bus receive; constraints 1786..1791 are `c_{52+k}`.
`B = 2`: two receives. -/
theorem dig1_b0 : LiveIs (fxB 1 2 (1 + 17 * 2 ^ 24)) 0 [] = true := by decide +kernel
theorem dig1_b1 : LiveIs (fxB 1 2 (1 + 17 * 2 ^ 24)) 1 [] = true := by decide +kernel
theorem dig1_b2 : LiveIs (fxB 1 2 (1 + 17 * 2 ^ 24)) 2 [digLo] = true := by decide +kernel
theorem dig2_b0 : LiveIs (fxB 1 2 (2 + 17 * 2 ^ 24)) 0 [] = true := by decide +kernel
theorem dig2_b1 : LiveIs (fxB 1 2 (2 + 17 * 2 ^ 24)) 1 [] = true := by decide +kernel
theorem dig2_b2 : LiveIs (fxB 1 2 (2 + 17 * 2 ^ 24)) 2 [digLo, digHi] = true := by decide +kernel

/-- With `B = 1`, constraints 1786..1791 are `c_{52}..c_{57}`. -/
theorem dig_z0 : 1786 ∈ nvConstraintIdx ∧
    EvalIs (fxB 1 2 (1 + 17 * 2 ^ 24)) (dag 1786) 0 [(52, false)] [1] = true := by
  decide +kernel
theorem dig_z1 : 1787 ∈ nvConstraintIdx ∧
    EvalIs (fxB 1 2 (1 + 17 * 2 ^ 24)) (dag 1787) 0 [(53, false)] [1] = true := by
  decide +kernel
theorem dig_z2 : 1788 ∈ nvConstraintIdx ∧
    EvalIs (fxB 1 2 (1 + 17 * 2 ^ 24)) (dag 1788) 0 [(54, false)] [1] = true := by
  decide +kernel
theorem dig_z3 : 1789 ∈ nvConstraintIdx ∧
    EvalIs (fxB 1 2 (1 + 17 * 2 ^ 24)) (dag 1789) 0 [(55, false)] [1] = true := by
  decide +kernel
theorem dig_z4 : 1790 ∈ nvConstraintIdx ∧
    EvalIs (fxB 1 2 (1 + 17 * 2 ^ 24)) (dag 1790) 0 [(56, false)] [1] = true := by
  decide +kernel
theorem dig_z5 : 1791 ∈ nvConstraintIdx ∧
    EvalIs (fxB 1 2 (1 + 17 * 2 ^ 24)) (dag 1791) 0 [(57, false)] [1] = true := by
  decide +kernel

/-- **What 1786..1791 are** (shown for 1786): on a `Dig` row, `(2 − B)·c_{52+k}` — the exported
expression is `ka·h1·g2·(2 − (P1 − Σ op-selector·op·2^24))·c_{52+k}`: for `B = 3` it is
`−c_{52}`, for `B = 2` it vanishes identically. -/
theorem dig_hi3 :
    EvalIs (fxB 1 2 (3 + 17 * 2 ^ 24)) (dag 1786) 0 [(52, false)] [-1] = true := by
  decide +kernel
theorem dig_hi2 : EvalIs (fxB 1 2 (2 + 17 * 2 ^ 24)) (dag 1786) 0 [] [] = true := by
  decide +kernel

theorem cast_one_add (p : Nat) : (1 : Fp) + ((p : Nat) : Fp) = ((p + 1 : Nat) : Fp) := by
  rw [cast_succ]; grind

/-- **`Dig` (`B ∈ {1, 2}`)**: the digest-bus receives `(−1, [J, P, c_y[0..6]])` and (for `B = 2`)
`(−1, [J, P + 1, c_y[6..12]])`; nothing on the slot and job buses; for `B = 1` the high half
of the cell is zero. -/
theorem dig_sem {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) {a nb j p : Nat} (hi : prog[y] = ⟨17, a, nb, j, p⟩)
    (hnb : nb = 1 ∨ nb = 2) :
    (rowEnt tr pub y 2).filter (·.1 ≠ 0) =
      ((-1 : Fp), [((j : Nat) : Fp), ((p : Nat) : Fp)] ++ (cellOf tr y).take 6) ::
        (if nb = 2 then [((-1 : Fp), [((j : Nat) : Fp), ((p + 1 : Nat) : Fp)] ++ (cellOf tr y).drop 6)]
         else []) ∧
    (rowEnt tr pub y 0).filter (·.1 ≠ 0) = [] ∧ (rowEnt tr pub y 1).filter (·.1 ≠ 0) = [] ∧
    (nb = 1 → (cellOf tr y).drop 6 = [0, 0, 0, 0, 0, 0]) := by
  have hc := nvConstr_of hh
  have hka := ka_of_prog hh hG hP hW hy (Or.inl (by simp [hi]))
  obtain ⟨hr, hag⟩ := prog_agrees (pub := pub) hh hG hP hW hy hka
  rw [hi] at hag
  simp only [Nat.reduceMod, Nat.reduceDiv] at hag
  have hag : Agrees (fxOp 1 2) (rowEnv tr 0 y pub) := hag
  have row := hP.2 y hy
  rw [hi] at row
  rcases hnb with rfl | rfl
  · have hag' := agrees_fxB (v := 1 + 17 * 2 ^ 24) hag row.2.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [liveIs_row hag' dig1_b2]
      simp only [digLo, List.map_cons, List.map_nil, evSp, evF_c, evF_cv, fp_zero_add,
        rowVal_col tr 0 y pub 8 (by decide), rowVal_col tr 0 y pub 9 (by decide),
        rowVal_col tr 0 y pub 46 (by decide), rowVal_col tr 0 y pub 47 (by decide),
        rowVal_col tr 0 y pub 48 (by decide), rowVal_col tr 0 y pub 49 (by decide),
        rowVal_col tr 0 y pub 50 (by decide), rowVal_col tr 0 y pub 51 (by decide),
        List.filter_cons, List.filter_nil, dec_negone, ite_true]
      rw [show tr.cell 0 y 8 = _ from row.2.2.1, show tr.cell 0 y 9 = _ from row.2.2.2, cellOf_eq,
        if_neg (by decide)]
      rfl
    · rw [liveIs_row hag' dig1_b0]; rfl
    · rw [liveIs_row hag' dig1_b1]; rfl
    · intro _
      have zk : ∀ {j c : Nat}, (j ∈ nvConstraintIdx ∧
          EvalIs (fxB 1 2 (1 + 17 * 2 ^ 24)) (dag j) 0 [(c, false)] [1] = true) → c < 1000 →
          cv tr 0 y c = 0 := by
        intro j c hz hc'
        have e := cons_lin hc hr hag' hz.1 hz.2
        simp only [lin, rowVal_col tr 0 y pub _ hc'] at e
        grind
      rw [cellOf_eq]
      simp only [List.drop_succ_cons, List.drop_zero]
      rw [zk dig_z0 (by decide), zk dig_z1 (by decide), zk dig_z2 (by decide),
        zk dig_z3 (by decide), zk dig_z4 (by decide), zk dig_z5 (by decide)]
  · have hag' := agrees_fxB (v := 2 + 17 * 2 ^ 24) hag row.2.1
    refine ⟨?_, ?_, ?_, fun h => absurd h (by decide)⟩
    · rw [liveIs_row hag' dig2_b2]
      simp only [digLo, digHi, List.map_cons, List.map_nil, evSp, evF_c, evF_cv, fp_zero_add,
        rowVal_col tr 0 y pub 8 (by decide), rowVal_col tr 0 y pub 9 (by decide),
        rowVal_col tr 0 y pub 46 (by decide), rowVal_col tr 0 y pub 47 (by decide),
        rowVal_col tr 0 y pub 48 (by decide), rowVal_col tr 0 y pub 49 (by decide),
        rowVal_col tr 0 y pub 50 (by decide), rowVal_col tr 0 y pub 51 (by decide),
        rowVal_col tr 0 y pub 52 (by decide), rowVal_col tr 0 y pub 53 (by decide),
        rowVal_col tr 0 y pub 54 (by decide), rowVal_col tr 0 y pub 55 (by decide),
        rowVal_col tr 0 y pub 56 (by decide), rowVal_col tr 0 y pub 57 (by decide),
        List.filter_cons, List.filter_nil, dec_negone, ite_true]
      rw [show tr.cell 0 y 8 = _ from row.2.2.1, show tr.cell 0 y 9 = _ from row.2.2.2, cellOf_eq,
        cast_one_add]
      rfl
    · rw [liveIs_row hag' dig2_b0]; rfl
    · rw [liveIs_row hag' dig2_b1]; rfl

/-! ## Classification over all 40 ops -/

/-- Slot bus: every live entry's channel is a constant; channel `1` carries `P2`. -/
def chk0 (S : List (Aff × List Aff)) : Bool :=
  S.all fun q => match q.2 with
    | m0 :: m1 :: _ => m0.vs.isEmpty && (m0.c != 1 || m1.Is 0 [(8, false)] [1])
    | _ => false

/-- Job bus: every live entry carries `P2` first. -/
def chk1 (S : List (Aff × List Aff)) : Bool :=
  S.all fun q => match q.2 with
    | m0 :: _ => m0.Is 0 [(8, false)] [1]
    | _ => false

def optAll (f : List (Aff × List Aff) → Bool) : Option (List (Aff × List Aff)) → Bool
  | some S => f S
  | none => false

/-- The classification check for op `8b + a` (one kernel check per op). -/
abbrev ClsAt (a b : Nat) : Prop :=
  optAll chk0 (live (fxOp a b) (busIdx 0)) = true ∧ optAll chk1 (live (fxOp a b) (busIdx 1)) = true

theorem cls_0_0 : ClsAt 0 0 := by decide +kernel
theorem cls_0_1 : ClsAt 0 1 := by decide +kernel
theorem cls_0_2 : ClsAt 0 2 := by decide +kernel
theorem cls_0_3 : ClsAt 0 3 := by decide +kernel
theorem cls_0_4 : ClsAt 0 4 := by decide +kernel
theorem cls_1_0 : ClsAt 1 0 := by decide +kernel
theorem cls_1_1 : ClsAt 1 1 := by decide +kernel
theorem cls_1_2 : ClsAt 1 2 := by decide +kernel
theorem cls_1_3 : ClsAt 1 3 := by decide +kernel
theorem cls_1_4 : ClsAt 1 4 := by decide +kernel
theorem cls_2_0 : ClsAt 2 0 := by decide +kernel
theorem cls_2_1 : ClsAt 2 1 := by decide +kernel
theorem cls_2_2 : ClsAt 2 2 := by decide +kernel
theorem cls_2_3 : ClsAt 2 3 := by decide +kernel
theorem cls_2_4 : ClsAt 2 4 := by decide +kernel
theorem cls_3_0 : ClsAt 3 0 := by decide +kernel
theorem cls_3_1 : ClsAt 3 1 := by decide +kernel
theorem cls_3_2 : ClsAt 3 2 := by decide +kernel
theorem cls_3_3 : ClsAt 3 3 := by decide +kernel
theorem cls_3_4 : ClsAt 3 4 := by decide +kernel
theorem cls_4_0 : ClsAt 4 0 := by decide +kernel
theorem cls_4_1 : ClsAt 4 1 := by decide +kernel
theorem cls_4_2 : ClsAt 4 2 := by decide +kernel
theorem cls_4_3 : ClsAt 4 3 := by decide +kernel
theorem cls_4_4 : ClsAt 4 4 := by decide +kernel
theorem cls_5_0 : ClsAt 5 0 := by decide +kernel
theorem cls_5_1 : ClsAt 5 1 := by decide +kernel
theorem cls_5_2 : ClsAt 5 2 := by decide +kernel
theorem cls_5_3 : ClsAt 5 3 := by decide +kernel
theorem cls_5_4 : ClsAt 5 4 := by decide +kernel
theorem cls_6_0 : ClsAt 6 0 := by decide +kernel
theorem cls_6_1 : ClsAt 6 1 := by decide +kernel
theorem cls_6_2 : ClsAt 6 2 := by decide +kernel
theorem cls_6_3 : ClsAt 6 3 := by decide +kernel
theorem cls_6_4 : ClsAt 6 4 := by decide +kernel
theorem cls_7_0 : ClsAt 7 0 := by decide +kernel
theorem cls_7_1 : ClsAt 7 1 := by decide +kernel
theorem cls_7_2 : ClsAt 7 2 := by decide +kernel
theorem cls_7_3 : ClsAt 7 3 := by decide +kernel
theorem cls_7_4 : ClsAt 7 4 := by decide +kernel

theorem cls_ok : ∀ a, a < 8 → ∀ b, b < 5 → ClsAt a b
  | a + 8, h, _, _ => absurd h (by omega)
  | _, _, b + 5, h => absurd h (by omega)
  | 0, _, 0, _ => cls_0_0
  | 0, _, 1, _ => cls_0_1
  | 0, _, 2, _ => cls_0_2
  | 0, _, 3, _ => cls_0_3
  | 0, _, 4, _ => cls_0_4
  | 1, _, 0, _ => cls_1_0
  | 1, _, 1, _ => cls_1_1
  | 1, _, 2, _ => cls_1_2
  | 1, _, 3, _ => cls_1_3
  | 1, _, 4, _ => cls_1_4
  | 2, _, 0, _ => cls_2_0
  | 2, _, 1, _ => cls_2_1
  | 2, _, 2, _ => cls_2_2
  | 2, _, 3, _ => cls_2_3
  | 2, _, 4, _ => cls_2_4
  | 3, _, 0, _ => cls_3_0
  | 3, _, 1, _ => cls_3_1
  | 3, _, 2, _ => cls_3_2
  | 3, _, 3, _ => cls_3_3
  | 3, _, 4, _ => cls_3_4
  | 4, _, 0, _ => cls_4_0
  | 4, _, 1, _ => cls_4_1
  | 4, _, 2, _ => cls_4_2
  | 4, _, 3, _ => cls_4_3
  | 4, _, 4, _ => cls_4_4
  | 5, _, 0, _ => cls_5_0
  | 5, _, 1, _ => cls_5_1
  | 5, _, 2, _ => cls_5_2
  | 5, _, 3, _ => cls_5_3
  | 5, _, 4, _ => cls_5_4
  | 6, _, 0, _ => cls_6_0
  | 6, _, 1, _ => cls_6_1
  | 6, _, 2, _ => cls_6_2
  | 6, _, 3, _ => cls_6_3
  | 6, _, 4, _ => cls_6_4
  | 7, _, 0, _ => cls_7_0
  | 7, _, 1, _ => cls_7_1
  | 7, _, 2, _ => cls_7_2
  | 7, _, 3, _ => cls_7_3
  | 7, _, 4, _ => cls_7_4

theorem nop_b0 : LiveIs (fxOp 0 0) 0 [] = true := by decide +kernel
theorem nop_b1 : LiveIs (fxOp 0 0) 1 [] = true := by decide +kernel
theorem nop_b2 : LiveIs (fxOp 0 0) 2 [] = true := by decide +kernel

/-- A nonzero-count entry of a row lies in `live`'s forms. -/
theorem live_mem {fx : Fix} {tr : Trace Fp} {r : Nat} {pub : List Fp}
    (hag : Agrees fx (rowEnv tr 0 r pub)) {b : Nat} {S : List (Aff × List Aff)}
    (hl : live fx (busIdx b) = some S) {e : Fp × List Fp} (he : e ∈ rowEnt tr pub r b)
    (h0 : e.1 ≠ 0) : ∃ q ∈ S, e = evA (rowVal tr 0 r pub) q := by
  have : e ∈ (rowEnt tr pub r b).filter (·.1 ≠ 0) := List.mem_filter.2 ⟨he, by simpa using h0⟩
  rw [rowEnt_eq, live_filter hag _ S hl] at this
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_filter.1 this).1
  exact ⟨q, hq, rfl⟩

theorem is_c8 {tr : Trace Fp} {r : Nat} {pub : List Fp} (m : Aff)
    (h : m.Is 0 [(8, false)] [1] = true) : m.eval (rowVal tr 0 r pub) = cv tr 0 r 8 := by
  rw [aff_is_eval m _ _ _ h]
  simp only [lin, rowVal_col tr 0 r pub 8 (by decide)]
  grind

/-- **Slot bus (all ops)**: on a bound ALU row, every nonzero-count slot-bus entry with channel `1`
(the SHA units) carries `P2` as its second field. -/
theorem alu_slot_job {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) (hA : AluHyp tr prog y hy) :
    ∀ e ∈ rowEnt tr pub y 0, e.1 ≠ 0 → e.2.head? = some 1 → e.2[1]? = some (cv tr 0 y 8) := by
  have hka := ka_of_prog hh hG hP hW hy hA
  obtain ⟨hr, hag⟩ := prog_agrees (pub := pub) hh hG hP hW hy hka
  obtain ⟨hop, -⟩ := hW _ (List.getElem_mem hy)
  have hc := (cls_ok (prog[y].op % 8) (Nat.mod_lt _ (by decide)) (prog[y].op / 8) (by omega)).1
  intro e he h0 h1
  unfold optAll at hc
  split at hc
  · next S hl =>
    obtain ⟨q, hq, rfl⟩ := live_mem hag hl he h0
    have hq' := List.all_eq_true.1 hc q hq
    obtain ⟨c, ms⟩ := q
    simp only [evA] at h1 ⊢
    rcases ms with _ | ⟨m0, _ | ⟨m1, rest⟩⟩
    · simp at hq'
    · simp at hq'
    · simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hq'
      simp only [List.map_cons, List.head?_cons, Option.some.injEq] at h1
      rw [Aff.eval, sumV_nil_of _ hq'.1] at h1
      rcases hq'.2 with hne | his
      · exact absurd (by rw [← h1]; grind) hne
      · simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero, is_c8 m1 his]
  · simp at hc

/-- **Job bus (all ops)**: every nonzero-count job-bus entry of a bound ALU row carries `P2`
first. -/
theorem alu_job_job {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) (hA : AluHyp tr prog y hy) :
    ∀ e ∈ rowEnt tr pub y 1, e.1 ≠ 0 → e.2.head? = some (cv tr 0 y 8) := by
  have hka := ka_of_prog hh hG hP hW hy hA
  obtain ⟨hr, hag⟩ := prog_agrees (pub := pub) hh hG hP hW hy hka
  obtain ⟨hop, -⟩ := hW _ (List.getElem_mem hy)
  have hc := (cls_ok (prog[y].op % 8) (Nat.mod_lt _ (by decide)) (prog[y].op / 8) (by omega)).2
  intro e he h0
  unfold optAll at hc
  split at hc
  · next S hl =>
    obtain ⟨q, hq, rfl⟩ := live_mem hag hl he h0
    have hq' := List.all_eq_true.1 hc q hq
    obtain ⟨c, ms⟩ := q
    simp only [evA]
    rcases ms with _ | ⟨m0, rest⟩
    · simp at hq'
    · simp only [List.map_cons, List.head?_cons, is_c8 m0 hq']
  · simp at hc

/-- **`Nop`**: a `Nop` ALU row has only zero counts on the slot, job and digest buses. -/
theorem nop_silent {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) (hop : prog[y].op = 0) (hA : AluHyp tr prog y hy) :
    ∀ b, b ≤ 2 → ∀ e ∈ rowEnt tr pub y b, e.1 = 0 := by
  have hka := ka_of_prog hh hG hP hW hy hA
  obtain ⟨hr, hag⟩ := prog_agrees (pub := pub) hh hG hP hW hy hka
  rw [hop] at hag
  simp only [Nat.reduceMod, Nat.reduceDiv] at hag
  have hag : Agrees (fxOp 0 0) (rowEnv tr 0 y pub) := hag
  have key : ∀ b, LiveIs (fxOp 0 0) b [] = true → ∀ e ∈ rowEnt tr pub y b, e.1 = 0 := by
    intro b hb e he
    have h := liveIs_row hag hb
    apply Classical.byContradiction
    intro h0
    have : e ∈ (rowEnt tr pub y b).filter (·.1 ≠ 0) := List.mem_filter.2 ⟨he, by simpa using h0⟩
    rw [h] at this
    simp at this
  intro b hb
  have : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact key 0 nop_b0
  · exact key 1 nop_b1
  · exact key 2 nop_b2

#print axioms tEntries_rows
#print axioms liveIs_row
#print axioms add_sem
#print axioms const_sem
#print axioms unit1_sem
#print axioms unit1_mem
#print axioms job_sem
#print axioms dig_sem
#print axioms dig_hi3
#print axioms dig_hi2
#print axioms cls_ok
#print axioms alu_slot_job
#print axioms alu_job_job
#print axioms nop_silent

end ZkFormal.PQ.NvOps
