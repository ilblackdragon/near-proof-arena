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

* `offer_of_job`: for a `hash_range` job laid out at program rows (`RangeJob.OK`: one `Job` row,
  `Unit1` rows at unit indices `2 + i` in increasing row order, two `Dig` rows, and no other row
  with `P2 = j`: a program fact), the ALU's offer is exactly `rangeUnits` of the cell
  values (`job_sem`, `unit1_sem`, `alu_slot_job`, `alu_job_job`, `dig_sem`, the sparse
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
  excl : ∀ y (h : y < prog.length), y ∉ J.y0 :: J.ys → y ≠ J.dlo → y ≠ J.dhi → prog[y].k1 ≠ J.j

/-- The unit values of a job: limb 0 of its unit cells. -/
def RangeJob.vals (tr : Trace Fp) (J : RangeJob) : List Fp := J.cs.map fun c => cv tr 0 c 46

/-! ## Helper lemmas -/

theorem flatMap_idx {γ : Type} (g : Nat → List γ) :
    ∀ (ys : List Nat) (F : Nat → γ), (∀ i (h : i < ys.length), g ys[i] = [F i]) →
      ys.flatMap g = (List.range ys.length).map F
  | [], _, _ => rfl
  | y :: ys, F, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [List.flatMap_cons, h0, List.length_cons, List.range_succ_eq_map,
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
  · have hka := ka_of_prog hh hG hP.1 hW hJ.y0_lt (Or.inl (by rw [hJ.job]; simp))
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
      intro hhd hz
      by_cases hk : prog[r].k1 = J.j
      · by_cases hu : r ∈ J.ys
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
          have h1 := (unit1_sem hh hG hP.1 hW (hJ.ys_lt i hi) (hJ.unit i hi).1 (hJ.unit i hi).2).2.2.1
          have : e ∈ (rowEnt tr pub J.ys[i] 1).filter (·.1 ≠ 0) :=
            List.mem_filter.2 ⟨he, by simpa using hz⟩
          rw [h1] at this
          exact absurd this (List.not_mem_nil)
        · have hd : r = J.dlo ∨ r = J.dhi := by
            by_cases h1 : r = J.dlo
            · exact .inl h1
            by_cases h2 : r = J.dhi
            · exact .inr h2
            exact absurd hk (hJ.excl r hrp (by simp [hrs, hu]) h1 h2)
          have hb1 : (rowEnt tr pub r 1).filter (·.1 ≠ 0) = [] := by
            rcases hd with rfl | rfl
            · exact (dig_sem hh hG hP.1 hW hJ.dlo_lt hJ.dlo (.inr rfl)).2.2.1
            · exact (dig_sem hh hG hP.1 hW hJ.dhi_lt hJ.dhi (.inl rfl)).2.2.1
          have : e ∈ (rowEnt tr pub r 1).filter (·.1 ≠ 0) := List.mem_filter.2 ⟨he, by simpa using hz⟩
          rw [hb1] at this
          exact absurd this (List.not_mem_nil)
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
    have hka := ka_of_prog hh hG hP.1 hW hJ.y0_lt (Or.inl (by rw [hJ.job]; simp))
    simp only [hka, ite_true]
    rw [(job_sem hh hG hP.1 hW hJ.y0_lt hJ.job).1]
    rw [flatMap_idx _ J.ys (fun i => unitMsg ((J.j : Nat) : Fp) (rangeUnits (J.vals tr)) (i + 2))]
    · simp only [rangeUnits, List.length_cons, List.length_map, RangeJob.vals]
      rw [List.range_succ_eq_map, List.range_succ_eq_map, hJ.len]
      simp only [List.map_cons, List.map_map]
      simp [unitMsg, List.filter, Function.comp_def, natCast_zero, natCast_one]
    · intro i hi
      have hu := hJ.unit i hi
      have hkay := ka_of_prog hh hG hP.1 hW (hJ.ys_lt i hi) (Or.inl (by rw [hu.1]; simp))
      simp only [hkay, ite_true]
      rw [(unit1_sem hh hG hP.1 hW (hJ.ys_lt i hi) hu.1 hu.2).2.1]
      have hic : i < J.cs.length := hJ.len ▸ hi
      rw [Nat.add_comm 2 i]
      simp [unitMsg, rangeUnits, RangeJob.vals, List.getD_eq_getElem?_getD, hic]
  · intro r hr hrs
    by_cases hka : cv tr 0 r 0 = 1
    · simp only [hka, ite_true]
      have hrp := alu_row_of hP hr
      rw [List.filter_filter, List.filter_eq_nil_iff]
      intro e he
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro htk hz
      obtain ⟨h1, h2⟩ := take2_eq htk
      by_cases hk : prog[r].k1 = J.j
      · have hd : r = J.dlo ∨ r = J.dhi := by
          by_cases h1 : r = J.dlo
          · exact .inl h1
          by_cases h2 : r = J.dhi
          · exact .inr h2
          exact absurd hk (hJ.excl r hrp hrs h1 h2)
        have hb0 : (rowEnt tr pub r 0).filter (·.1 ≠ 0) = [] := by
          rcases hd with rfl | rfl
          · exact (dig_sem hh hG hP.1 hW hJ.dlo_lt hJ.dlo (.inr rfl)).2.1
          · exact (dig_sem hh hG hP.1 hW hJ.dhi_lt hJ.dhi (.inl rfl)).2.1
        have : e ∈ (rowEnt tr pub r 0).filter (·.1 ≠ 0) := List.mem_filter.2 ⟨he, by simpa using hz⟩
        rw [hb0] at this
        exact absurd this (List.not_mem_nil)
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
    dig_in hh hG hP hW hJ.dlo_lt (by rw [hJ.dlo]; simp) (by rw [hlo]; simp)
  have e1 : ((-1 : Fp), [((J.j : Nat) : Fp), ((1 : Nat) : Fp)] ++ (cellOf tr J.dlo).drop 6) ∈
      aluEnt tr pub 2 :=
    dig_in hh hG hP hW hJ.dlo_lt (by rw [hJ.dlo]; simp) (by rw [hlo]; simp)
  have e2 : ((-1 : Fp), [((J.j : Nat) : Fp), ((2 : Nat) : Fp)] ++ (cellOf tr J.dhi).take 6) ∈
      aluEnt tr pub 2 :=
    dig_in hh hG hP hW hJ.dhi_lt (by rw [hJ.dhi]; simp) (by rw [hhi.1]; simp)
  have hz := hhi.2.2.2 rfl
  have h0 : (cellOf tr J.dlo).take 6 = pairOf (jobLimbs pre 9 (rangeUnits (J.vals tr))) 0 := by
    rcases hC _ _ _ hO 0 _ (by decide) e0 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  have h1 : (cellOf tr J.dlo).drop 6 = pairOf (jobLimbs pre 9 (rangeUnits (J.vals tr))) 1 := by
    rcases hC _ _ _ hO 1 _ (by decide) e1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
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
  rw [hL]
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
