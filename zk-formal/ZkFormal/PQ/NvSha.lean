import ZkFormal.PQ.NvOps
import ZkFormal.PQ.NvShaNative

/-!
# ZkFormal.PQ.NvSha — the SHA instance interface of NvAir: `hash_range`'s digest cells

Lane E (E2E M11i, item 1), 2026-11-21. `NodeSha` (`E2ENode.lean`) says the digest cells of each
`hash_range` job of the node program are the native tag-9 range digest of the statement its
message cells denote. This file proves that from the circuit's predicate `NvHold`, the program
binding, and **the SHA subsystem's contract**, for any `hash_range` job laid out as `build_agg`
emits it.

## The contract (`ShaContract`, a named premise)

The SHA subsystem is Sha512Air4 + TableAir4 (exported, `NvCircuitExport.lean`) and NvAir's GLUE
and HASH roles. Its faithfulness is the written argument of
`research/near-compression/results/pq384-sha-air3/FAITHFUL-v4.md` (C1–C8: the compression AIR is
SHA-512 compression) and of `results/pq-recursion-nv/FAITHFUL.md` §2(c) C9 (GLUE frames
`PREFIX ‖ tag ‖ units`, pads, chains from the SHA-384 IV, sends the digest pairs; C9.7–C9.8 the
42-B truncation with `lo6`) with the job-id uniqueness of §2(d) R.3.1. It is stated here at the
interface the ALU sees: **if the ALU rows offer job `j` exactly once on the job bus (`(j, tag, 1)`)
and exactly the units `us` (index `i` ↦ `us[i]`, in row order) on the slot bus, then every digest
the ALU receives for `(j, p)` is pair `p` of the job's SHA-384**, pair 2 with word 5 truncated and
its limb 2 offset by `δ` with `4δ` a byte (C9.8: `lo6` is free in GLUE).

## Proved (standard axioms only)

* `quiet_row`: an ALU row whose op is not a unit or job producer sends nothing on the job bus and
  no channel-1 unit (partial evaluation of the exported interactions for 26 ops).
* `offer_of_job`: for a `hash_range` job laid out at program rows (`RangeJob.OK`: one `Job` row,
  `Unit1` rows at unit indices `2 + i` in increasing row order, two `Dig` rows, and no other row
  with `P2 = j` producing units or jobs), the ALU's offer is exactly `rangeUnits` of the cell
  values (`job_sem`, `unit1_sem`, `alu_slot_job`, `alu_job_job`, `quiet_row`, the sparse
  concatenation `flatMap_range_sparse`).
* **`range_cells`**: the two `Dig` cells of such a job are the canonical range digest cells
  `rangeLimbs pre vals`, given the contract and **`TailCanon`** at the high `Dig` row.
* `nodeSha_of`: `E2ENode.NodeSha` for a node read whose digest cells are those `Dig` cells and
  whose statement cells are the jobs' unit cells (`ShaLay`).

## Finding: the range digest's tail is not pinned (`TailCanon`)

Every ALU job is a `tr = 1` job (the `Job` row's job-bus message is `(P2, P0, 1)`, exported), so
in 42-B mode GLUE sends limb 2 of word 5 as `s5 − lo6` with only `4·lo6` range-checked as a byte
(`glue.rs`: `lookup_byte(lo6·4)`). FAITHFUL.md C9.8 makes this sound **through the consumers**:
Merkle nodes and Merkle-root checks compare the limb with a canonical tail `64t`. Its consumer
list is `node` and `merkle_path`; **`hash_range` (`agg.rs`) is a third consumer and is not
canonical**: its `Dig` cells go to `assert_eq` against the child's packed public values (node
children) and to `PvD` (the node's own public digest), neither of which range-checks the limb. So
the 18th limb of every internal range digest carries a free shift `δ ∈ {v/4 : v < 256}`. The
digest comparison still binds 40 bytes plus the 16-bit tail up to ±1 (a near-collision of
SHA-384, ≈ 2^-334 classically), so this is not an attack, but the Lean statement
`kidDig = rdigest st` is false without a pin, and the honest-only canonicality is what V_d checks
at the wrap. `TailCanon tr dhi` (the high `Dig` cell's limb 5 is `64t`, `t < 2^16`) is the named
gap; `tail_pin` shows it gives the canonical value. Fix (lane D): pin `lo6` in GLUE (one byte-pair
lookup of `(s5 − lo6)/64`, FAITHFUL.md's own suggestion) or a `(t lo, t hi)` byte lookup in the
`Dig` row of range jobs.
-/

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace ZkFormal.PQ.NvSha

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.NvAirExport ZkFormal.PQ.NvCircuitExport
open ZkFormal.PQ.NvTape ZkFormal.PQ.NvAff ZkFormal.PQ.NvField ZkFormal.PQ.NvProg
open ZkFormal.PQ.NvOps ZkFormal.PQ.NvShaNative

/-! ## ALU entries, offers and the SHA contract -/

/-- The ALU rows' nonzero-count entries on bus `b`, in row order. -/
def aluEnt (tr : Trace Fp) (pub : List Fp) (b : Nat) : List (Fp × List Fp) :=
  (List.range (tr.height 0)).flatMap fun r =>
    if cv tr 0 r 0 = 1 then (rowEnt tr pub r b).filter (·.1 ≠ 0) else []

/-- The slot-bus send of unit `i` of job `j` with units `us`. -/
def unitMsg (j : Fp) (us : List (List Fp)) (i : Nat) : Fp × List Fp :=
  ((1 : Fp), [1, j, ((i : Nat) : Fp)] ++ us.getD i [])

/-- **The ALU's offer of job `j`**: exactly one job-bus send `(j, tag, 1)` and exactly the unit
sends of `us` (in row order) on the slot bus, channel 1. -/
def Offer (tr : Trace Fp) (pub : List Fp) (j : Fp) (tag : Nat) (us : List (List Fp)) : Prop :=
  (aluEnt tr pub 1).filter (fun e => decide (e.2.head? = some j)) =
      [((1 : Fp), [j, ((tag : Nat) : Fp), 1])] ∧
    (aluEnt tr pub 0).filter (fun e => decide (e.2.take 2 = [1, j])) =
      (List.range us.length).map (unitMsg j us)

/-- Digest pair `p` (six limbs) of an 18-limb digest. -/
def pairOf (l : List Fp) (p : Nat) : List Fp := (l.drop (6 * p)).take 6

/-- **The SHA subsystem's contract** (FAITHFUL-v4 C1–C8, FAITHFUL.md §2(c) C9, §2(d) R.3.1; 42-B
mode, `pre` the pinned 32-byte prefix): for an exactly offered ALU job, every digest the ALU
receives for `(j, p)`, `p < 3`, is pair `p` of the job's SHA-384; pair 2 truncated, its last limb
shifted by a `δ` with `4δ` a byte. -/
def ShaContract (pre : Bytes) (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ (j : Fp) (tag : Nat) (us : List (List Fp)), Offer tr pub j tag us →
    ∀ (p : Nat) (lim : List Fp), p < 3 → ((-1 : Fp), [j, ((p : Nat) : Fp)] ++ lim) ∈ aluEnt tr pub 2 →
      (p < 2 ∧ lim = pairOf (jobLimbs pre tag us) p) ∨
      (p = 2 ∧ ∃ δ : Fp, (∃ v, v < 256 ∧ (4 : Fp) * δ = ((v : Nat) : Fp)) ∧
        lim = (pairOf (jobLimbs pre tag us) 2).take 3 ++ [0, 0, (jobLimbs pre tag us).getD 17 0 - δ])

/-- **The named gap** (see the module doc): the high `Dig` cell of a range job holds a canonical
42-B tail in limb 5. -/
def TailCanon (tr : Trace Fp) (dhi : Nat) : Prop :=
  ∃ t, t < 2 ^ 16 ∧ cv tr 0 dhi 51 = ((64 * t : Nat) : Fp)

/-- Program binding of the whole program column (the NV program is pinned at the trace height:
BIND / V_d evaluate the full `P0..P3` columns). -/
def ProgFull (tr : Trace Fp) (prog : List Instr) : Prop :=
  ProgBound tr prog ∧ prog.length = tr.height 0

/-! ## Quiet ops: no job, no channel-1 unit -/

/-- The ops that produce SHA units or start jobs (from the exported interactions). -/
def unitOps : List Nat := [7, 9, 12, 13, 14, 18, 23, 24, 30, 32, 33, 34, 35, 39]

/-- A live slot-bus form whose first message field is a constant other than `1`. -/
def headNot1 (p : Aff × List Aff) : Bool :=
  match p.2 with
  | m :: _ => m.vs.isEmpty && decide (m.c ≠ 1)
  | [] => false

/-- The check of a quiet op: no live job-bus form, every live slot-bus form off channel 1. -/
def quietCheck (o : Nat) : Bool :=
  match live (fxOp (o % 8) (o / 8)) (busIdx 0), live (fxOp (o % 8) (o / 8)) (busIdx 1) with
  | some S0, some S1 => S1.isEmpty && S0.all headNot1
  | _, _ => false

/-- The quiet ops. -/
def quietOps : List Nat := (List.range 40).filter fun o => !unitOps.contains o

/-- One kernel check per quiet op (one check over all of them would exceed the memory cap;
`NvOps`' per-op cost is about 26 s / 6-8 GB). -/
theorem quiet_0 : quietCheck 0 = true := by decide +kernel
theorem quiet_1 : quietCheck 1 = true := by decide +kernel
theorem quiet_2 : quietCheck 2 = true := by decide +kernel
theorem quiet_3 : quietCheck 3 = true := by decide +kernel
theorem quiet_4 : quietCheck 4 = true := by decide +kernel
theorem quiet_5 : quietCheck 5 = true := by decide +kernel
theorem quiet_6 : quietCheck 6 = true := by decide +kernel
theorem quiet_8 : quietCheck 8 = true := by decide +kernel
theorem quiet_10 : quietCheck 10 = true := by decide +kernel
theorem quiet_11 : quietCheck 11 = true := by decide +kernel
theorem quiet_15 : quietCheck 15 = true := by decide +kernel
theorem quiet_16 : quietCheck 16 = true := by decide +kernel
theorem quiet_17 : quietCheck 17 = true := by decide +kernel
theorem quiet_19 : quietCheck 19 = true := by decide +kernel
theorem quiet_20 : quietCheck 20 = true := by decide +kernel
theorem quiet_21 : quietCheck 21 = true := by decide +kernel
theorem quiet_22 : quietCheck 22 = true := by decide +kernel
theorem quiet_25 : quietCheck 25 = true := by decide +kernel
theorem quiet_26 : quietCheck 26 = true := by decide +kernel
theorem quiet_27 : quietCheck 27 = true := by decide +kernel
theorem quiet_28 : quietCheck 28 = true := by decide +kernel
theorem quiet_29 : quietCheck 29 = true := by decide +kernel
theorem quiet_31 : quietCheck 31 = true := by decide +kernel
theorem quiet_36 : quietCheck 36 = true := by decide +kernel
theorem quiet_37 : quietCheck 37 = true := by decide +kernel
theorem quiet_38 : quietCheck 38 = true := by decide +kernel

theorem quiet_of : ∀ {o : Nat}, o < 40 → o ∉ unitOps → quietCheck o = true
  | 0, _, _ => quiet_0
  | 1, _, _ => quiet_1
  | 2, _, _ => quiet_2
  | 3, _, _ => quiet_3
  | 4, _, _ => quiet_4
  | 5, _, _ => quiet_5
  | 6, _, _ => quiet_6
  | 8, _, _ => quiet_8
  | 10, _, _ => quiet_10
  | 11, _, _ => quiet_11
  | 15, _, _ => quiet_15
  | 16, _, _ => quiet_16
  | 17, _, _ => quiet_17
  | 19, _, _ => quiet_19
  | 20, _, _ => quiet_20
  | 21, _, _ => quiet_21
  | 22, _, _ => quiet_22
  | 25, _, _ => quiet_25
  | 26, _, _ => quiet_26
  | 27, _, _ => quiet_27
  | 28, _, _ => quiet_28
  | 29, _, _ => quiet_29
  | 31, _, _ => quiet_31
  | 36, _, _ => quiet_36
  | 37, _, _ => quiet_37
  | 38, _, _ => quiet_38
  | 7, _, hu => absurd (by decide) hu
  | 9, _, hu => absurd (by decide) hu
  | 12, _, hu => absurd (by decide) hu
  | 13, _, hu => absurd (by decide) hu
  | 14, _, hu => absurd (by decide) hu
  | 18, _, hu => absurd (by decide) hu
  | 23, _, hu => absurd (by decide) hu
  | 24, _, hu => absurd (by decide) hu
  | 30, _, hu => absurd (by decide) hu
  | 32, _, hu => absurd (by decide) hu
  | 33, _, hu => absurd (by decide) hu
  | 34, _, hu => absurd (by decide) hu
  | 35, _, hu => absurd (by decide) hu
  | 39, _, hu => absurd (by decide) hu
  | _ + 40, ho, _ => absurd ho (by omega)

/-- **A quiet ALU row** sends nothing on the job bus and no channel-1 unit on the slot bus. -/
theorem quiet_row {tr : Trace Fp} {pub : List Fp} (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    {prog : List Instr} (hP : ProgBound tr prog) (hW : ProgWF prog) {y : Nat}
    (hy : y < prog.length) (hka : cv tr 0 y 0 = 1) (hu : prog[y].op ∉ unitOps) :
    (∀ e ∈ rowEnt tr pub y 0, e.1 ≠ 0 → e.2.head? ≠ some 1) ∧
      (∀ e ∈ rowEnt tr pub y 1, e.1 = 0) := by
  obtain ⟨hr, hag⟩ := prog_agrees (pub := pub) hh hG hP hW hy hka
  obtain ⟨hop, -⟩ := hW _ (List.getElem_mem hy)
  have hq := quiet_of hop hu
  unfold quietCheck at hq
  split at hq
  · next S0 S1 h0 h1 =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hq
    obtain ⟨hs1, hs0⟩ := hq
    refine ⟨fun e he hz => ?_, fun e he => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := live_mem hag h0 he hz
      have hn := List.all_eq_true.1 hs0 q hq
      obtain ⟨c, ms⟩ := q
      unfold headNot1 at hn
      cases ms with
      | nil => simp at hn
      | cons m rest =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
        simp only [evA, List.map_cons, List.head?_cons, ne_eq, Option.some.injEq]
        rw [Aff.eval, sumV_nil_of _ hn.1]
        intro e1
        exact hn.2 (by rw [← e1]; grind)
    · by_cases hz : e.1 = 0
      · exact hz
      · obtain ⟨q, hq, -⟩ := live_mem hag h1 he hz
        rw [hs1] at hq
        exact absurd hq (List.not_mem_nil)
  · simp at hq

/-! ## A `hash_range` job in the program -/

/-- The program rows of one `hash_range` job (`agg.rs::hash_range`, `builder.rs` `job_start`,
`unit1`, `dig`): job id `j`, the `Job` row, the unit cell addresses `cs` read by the `Unit1` rows
`ys`, the two `Dig` rows. -/
structure RangeJob where
  j : Nat
  y0 : Nat
  cs : List Nat
  ys : List Nat
  dlo : Nat
  dhi : Nat

/-- The layout facts (all decidable on the pinned program). -/
structure RangeJob.OK (J : RangeJob) (prog : List Instr) : Prop where
  j_lt : J.j < P
  k1_lt : ∀ i ∈ prog, i.k1 < P
  y0_lt : J.y0 < prog.length
  job : prog[J.y0]'y0_lt = ⟨14, 9, 4 * J.cs.length, J.j, 0⟩
  len : J.ys.length = J.cs.length
  sorted : (J.y0 :: J.ys).Pairwise (· < ·)
  ys_lt : ∀ i (h : i < J.ys.length), J.ys[i] < prog.length
  unit : ∀ i (h : i < J.ys.length),
    prog[J.ys[i]]'(ys_lt i h) = ⟨7, J.cs.getD i 0, 0, J.j, 2 + i⟩ ∧ J.cs.getD i 0 < 2 ^ 24
  dlo_lt : J.dlo < prog.length
  dlo : prog[J.dlo]'dlo_lt = ⟨17, 0, 2, J.j, 0⟩
  dhi_lt : J.dhi < prog.length
  dhi : prog[J.dhi]'dhi_lt = ⟨17, 0, 1, J.j, 2⟩
  excl : ∀ y (h : y < prog.length), y ∉ J.y0 :: J.ys → prog[y].k1 = J.j → prog[y].op ∉ unitOps

/-- The unit values of a job: limb 0 of its unit cells. -/
def RangeJob.vals (tr : Trace Fp) (J : RangeJob) : List Fp := J.cs.map fun c => cv tr 0 c 46

/-! ## Helper lemmas -/

theorem flatMap_idx {β γ : Type} (g : Nat → List γ) :
    ∀ (ys : List Nat) (F : Nat → γ), (∀ i (h : i < ys.length), g ys[i] = [F i]) →
      ys.flatMap g = (List.range ys.length).map F
  | [], _, _ => rfl
  | y :: ys, F, h => by
    rw [List.flatMap_cons, h 0 (by simp), List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    simp only [List.getElem_cons_zero, List.singleton_append, List.cons.injEq, true_and]
    exact flatMap_idx g ys (fun i => F (i + 1)) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa using this)

theorem cast_ne {a b : Nat} (ha : a < P) (hb : b < P) (h : a ≠ b) :
    ((a : Nat) : Fp) ≠ ((b : Nat) : Fp) := fun e => h (cast_inj ha hb e)

theorem take2_eq {l : List Fp} {x y : Fp} (h : l.take 2 = [x, y]) :
    l.head? = some x ∧ l[1]? = some y := by
  match l, h with
  | a :: b :: _, h => simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at h; simp [h]

theorem alu_row_of {tr : Trace Fp} {prog : List Instr} (hP : ProgFull tr prog) {r : Nat}
    (hr : r < tr.height 0) : r < prog.length := by rw [hP.2]; exact hr

/-! ## The offer of a `hash_range` job -/

section Offer

variable {tr : Trace Fp} {pub : List Fp} {prog : List Instr}

theorem k1_cast (hP : ProgFull tr prog) {y : Nat} (hy : y < prog.length) :
    cv tr 0 y 8 = ((prog[y].k1 : Nat) : Fp) := (hP.1.2 y hy).2.2.1

/-- **The job-bus part of the offer.** -/
theorem offer_job (hh : NvHold pub tr) (hG : GlueByteBool tr pub) (hP : ProgFull tr prog)
    (hW : ProgWF prog) {J : RangeJob} (hJ : J.OK prog) :
    (aluEnt tr pub 1).filter (fun e => decide (e.2.head? = some ((J.j : Nat) : Fp))) =
      [((1 : Fp), [((J.j : Nat) : Fp), ((9 : Nat) : Fp), 1])] := by
  unfold aluEnt
  rw [List.filter_flatMap]
  rw [flatMap_range_sparse _ (tr.height 0) [J.y0] (by simp)
    (by intro y hy; simp at hy; subst hy; rw [← hP.2]; exact hJ.y0_lt)]
  · have hka := ka_of_prog hh hG hP.1 hW hJ.y0_lt (by rw [hJ.job]; exact .inl (by decide))
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hka, ite_true]
    rw [(job_sem hh hG hP.1 hW hJ.y0_lt hJ.job).2.1]
    simp
  · intro r hr hrs
    have hrs : r ≠ J.y0 := by simpa using hrs
    by_cases hka : cv tr 0 r 0 = 1
    · simp only [hka, ite_true]
      have hrp := alu_row_of hP hr
      rw [List.filter_filter, List.filter_eq_nil_iff]
      intro e he
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro hz hhd
      by_cases hk : prog[r].k1 = J.j
      · by_cases hu : r ∈ J.ys
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
          have h1 := (unit1_sem hh hG hP.1 hW (hJ.ys_lt i hi) (hJ.unit i hi).1 (hJ.unit i hi).2).2.2.1
          have : e ∈ (rowEnt tr pub J.ys[i] 1).filter (·.1 ≠ 0) :=
            List.mem_filter.2 ⟨he, by simpa using hz⟩
          rw [h1] at this
          exact absurd this (List.not_mem_nil)
        · have hq := (quiet_row hh hG hP.1 hW hrp hka (hJ.excl r hrp (by simp [hrs, hu]) hk)).2 e he
          exact hz hq
      · have := alu_job_job hh hG hP.1 hW hrp (.inr (.inr hka)) e he hz
        rw [k1_cast hP hrp, hhd, Option.some.injEq] at this
        exact cast_ne (hJ.k1_lt _ (List.getElem_mem hrp)) hJ.j_lt hk this.symm
    · simp [hka]

/-- **The slot-bus part of the offer.** -/
theorem offer_slot (hh : NvHold pub tr) (hG : GlueByteBool tr pub) (hP : ProgFull tr prog)
    (hW : ProgWF prog) {J : RangeJob} (hJ : J.OK prog) :
    (aluEnt tr pub 0).filter (fun e => decide (e.2.take 2 = [1, ((J.j : Nat) : Fp)])) =
      (List.range (rangeUnits (J.vals tr)).length).map (unitMsg ((J.j : Nat) : Fp) (rangeUnits (J.vals tr))) := by
  unfold aluEnt
  rw [List.filter_flatMap]
  have hS : ∀ y ∈ J.y0 :: J.ys, y < tr.height 0 := by
    intro y hy
    rw [← hP.2]
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hJ.y0_lt
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      exact hJ.ys_lt i hi
  rw [flatMap_range_sparse _ (tr.height 0) (J.y0 :: J.ys) hJ.sorted hS]
  · rw [List.flatMap_cons]
    have hka := ka_of_prog hh hG hP.1 hW hJ.y0_lt (by rw [hJ.job]; exact .inl (by decide))
    simp only [hka, ite_true]
    rw [(job_sem hh hG hP.1 hW hJ.y0_lt hJ.job).1]
    rw [flatMap_idx _ J.ys (fun i => unitMsg ((J.j : Nat) : Fp) (rangeUnits (J.vals tr)) (i + 2))]
    · simp only [rangeUnits, List.length_cons, List.length_map, RangeJob.vals]
      rw [List.range_succ_eq_map, List.range_succ_eq_map, hJ.len]
      simp only [List.map_cons, List.map_map]
      simp [unitMsg, List.filter, Function.comp_def]
    · intro i hi
      have hu := hJ.unit i hi
      have hkay := ka_of_prog hh hG hP.1 hW (hJ.ys_lt i hi) (by rw [hu.1]; exact .inl (by decide))
      simp only [hkay, ite_true]
      rw [(unit1_sem hh hG hP.1 hW (hJ.ys_lt i hi) hu.1 hu.2).2.1]
      have hic : i < J.cs.length := hJ.len ▸ hi
      simp [unitMsg, rangeUnits, RangeJob.vals, List.getD_eq_getElem?_getD, hic,
        Nat.add_comm i 2]
  · intro r hr hrs
    by_cases hka : cv tr 0 r 0 = 1
    · simp only [hka, ite_true]
      have hrp := alu_row_of hP hr
      rw [List.filter_filter, List.filter_eq_nil_iff]
      intro e he
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro hz htk
      obtain ⟨h1, h2⟩ := take2_eq htk
      by_cases hk : prog[r].k1 = J.j
      · exact (quiet_row hh hG hP.1 hW hrp hka (hJ.excl r hrp hrs hk)).1 e he hz h1
      · have := alu_slot_job hh hG hP.1 hW hrp (.inr (.inr hka)) e he hz h1
        rw [k1_cast hP hrp, h2, Option.some.injEq] at this
        exact cast_ne (hJ.k1_lt _ (List.getElem_mem hrp)) hJ.j_lt hk this.symm
    · simp [hka]

theorem offer_of_job (hh : NvHold pub tr) (hG : GlueByteBool tr pub) (hP : ProgFull tr prog)
    (hW : ProgWF prog) {J : RangeJob} (hJ : J.OK prog) :
    Offer tr pub ((J.j : Nat) : Fp) 9 (rangeUnits (J.vals tr)) :=
  ⟨offer_job hh hG hP hW hJ, offer_slot hh hG hP hW hJ⟩

/-- The `Dig` receives of the job are ALU digest-bus entries. -/
theorem dig_in (hh : NvHold pub tr) (hG : GlueByteBool tr pub) (hP : ProgFull tr prog)
    (hW : ProgWF prog) {y : Nat} (hy : y < prog.length) {e : Fp × List Fp}
    (hop : 0 < prog[y].op) (he : e ∈ (rowEnt tr pub y 2).filter (·.1 ≠ 0)) : e ∈ aluEnt tr pub 2 := by
  have hka := ka_of_prog hh hG hP.1 hW hy (.inl hop)
  unfold aluEnt
  refine List.mem_flatMap.2 ⟨y, List.mem_range.2 (by rw [← hP.2]; exact hy), ?_⟩
  simp only [hka, ite_true]
  exact he

end Offer

#print axioms quiet_row
#print axioms offer_of_job

/-! ## The digest cells of a `hash_range` job -/

section Cells

variable {tr : Trace Fp} {pub : List Fp} {prog : List Instr}

theorem list6 {l : List Nat} (h : l.length = 6) : ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l, h with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

theorem div42_lt {w : Nat} (h : w < 2 ^ 64) : w / 2 ^ 42 < 2 ^ 22 := by
  rw [Nat.div_lt_iff_lt_mul (by decide)]; omega

theorem toNat_cast {n : Nat} (h : n < P) : (((n : Nat) : Fp)).toNat = n := by
  show (Fp.ofNat n).toNat = n
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **The `Dig` cells of a `hash_range` job are the canonical range digest cells** (from the SHA
contract and the tail pin). -/
theorem range_cells (pre : Bytes) (hh : NvHold pub tr) (hG : GlueByteBool tr pub)
    (hP : ProgFull tr prog) (hW : ProgWF prog) (hC : ShaContract pre tr pub) {J : RangeJob}
    (hJ : J.OK prog) (hT : TailCanon tr J.dhi) :
    cellOf tr J.dlo ++ (cellOf tr J.dhi).take 6 = rangeLimbs pre (J.vals tr) := by
  have hO := offer_of_job hh hG hP hW hJ
  have hlo := (dig_sem hh hG hP.1 hW hJ.dlo_lt hJ.dlo (.inr rfl)).1
  have hhi := (dig_sem hh hG hP.1 hW hJ.dhi_lt hJ.dhi (.inl rfl))
  simp only [ite_true] at hlo
  have e0 : ((-1 : Fp), [((J.j : Nat) : Fp), ((0 : Nat) : Fp)] ++ (cellOf tr J.dlo).take 6) ∈
      aluEnt tr pub 2 :=
    dig_in hh hG hP hW hJ.dlo_lt (by rw [hJ.dlo]; decide) (by rw [hlo]; simp)
  have e1 : ((-1 : Fp), [((J.j : Nat) : Fp), ((1 : Nat) : Fp)] ++ (cellOf tr J.dlo).drop 6) ∈
      aluEnt tr pub 2 :=
    dig_in hh hG hP hW hJ.dlo_lt (by rw [hJ.dlo]; decide) (by rw [hlo]; simp)
  have e2 : ((-1 : Fp), [((J.j : Nat) : Fp), ((2 : Nat) : Fp)] ++ (cellOf tr J.dhi).take 6) ∈
      aluEnt tr pub 2 :=
    dig_in hh hG hP hW hJ.dhi_lt (by rw [hJ.dhi]; decide) (by rw [hhi.1]; simp)
  have hz := hhi.2.2.2 rfl
  obtain ⟨-, h0⟩ | ⟨h, -⟩ := hC _ _ _ hO 0 _ (by decide) e0
  swap; · exact absurd h (by decide)
  obtain ⟨-, h1⟩ | ⟨h, -⟩ := hC _ _ _ hO 1 _ (by decide) e1
  swap; · exact absurd h (by decide)
  obtain ⟨h, -⟩ | ⟨-, δ, ⟨v, hv, hδ⟩, h2⟩ := hC _ _ _ hO 2 _ (by decide) e2
  · exact absurd h (by decide)
  obtain ⟨t, ht, hT⟩ := hT
  -- the digest words
  generalize hd : NearSpecV3.E2E.Bnd.sha384 (jobMsg pre 9 (rangeUnits (J.vals tr))) = d at *
  have hwl := digWords_lt d
  obtain ⟨w0, w1, w2, w3, w4, w5, hw⟩ := list6 (digWords_length d)
  have hL : jobLimbs pre 9 (rangeUnits (J.vals tr)) =
      wlimbs w0 ++ wlimbs w1 ++ wlimbs w2 ++ wlimbs w3 ++ wlimbs w4 ++ wlimbs w5 := by
    unfold jobLimbs; rw [hd, hw]; simp
  have h5 : w5 < 2 ^ 64 := hwl w5 (by rw [hw]; simp)
  have hs5 := div42_lt h5
  rw [hL] at h0 h1 h2
  unfold rangeLimbs
  rw [← hd, hL]
  simp only [cellOf_eq, pairOf, wlimbs, List.take, List.drop, List.cons_append, List.nil_append,
    List.getD_cons_succ, List.getD_cons_zero, List.cons.injEq, and_true, List.drop_succ_cons,
    List.drop_zero, List.take_succ_cons, List.take_zero] at h0 h1 h2 hz ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h0
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h1
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := h2
  have hpin := tail_pin hs5 ht hv hδ (by rw [← c5, hT])
  simp only [truncLimbs, List.set, List.getD_cons_succ, List.getD_cons_zero,
    toNat_cast (show w5 / 2 ^ 42 < P by unfold P; omega)]
  rw [a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4, hT, hpin]

end Cells

#print axioms range_cells

end ZkFormal.PQ.NvSha
