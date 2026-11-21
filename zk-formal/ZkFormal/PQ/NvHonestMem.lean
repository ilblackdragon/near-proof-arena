import ZkFormal.PQ.NvHonestRows
import ZkFormal.PQ.NvHonestMemData

/-!
# ZkFormal.PQ.NvHonestMem — the honest trace's memory bus balances

Lane E (E2E M11g, item 1), 2026-11-04. `MemBalance` (`NvTape`) on the honest trace of
`NvHonestRows`: the three exported mem interactions are evaluated per row over `Nat` mod `p`
(`evN`, sound for the expression semantics: `evN_sound`), the entries with a non-zero count are
collected from the 792 used rows (rows `792..4095` are zero rows: every mem count vanishes,
`count_zeroL`), and every such entry's message is checked to have a total count `≡ 0 (mod p)`
(`mem_check`, kernel evaluation). `memBal_of_check` lifts this to every message of `Fp`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.NvHonestMem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.NvAirExport ZkFormal.PQ.NvTape
open ZkFormal.PQ.NvDagEval ZkFormal.PQ.NvHonestRows ZkFormal.PQ.NvHonestExport

set_option maxRecDepth 100000

/-- `Nat` semantics of an expression (mod `p`). -/
def evN (env : Env) : Expr → Nat
  | .const n => n % P
  | .col c nx => (if nx then env.nxt else env.loc).getD c 0 % P
  | .pub i => env.pv.getD i 0 % P
  | .isFirst => env.fst % P
  | .isLast => env.lst % P
  | .isTransition => env.trn % P
  | .add a b => (evN env a + evN env b) % P
  | .mul a b => (evN env a * evN env b) % P
  | .neg a => (P - evN env a) % P

theorem evN_lt (env : Env) (e : Expr) : evN env e < P := by
  cases e <;> simp only [evN] <;> exact Nat.mod_lt _ (by decide)

theorem evN_sound (env : Env) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hra : RowAgrees env tr t r pub) : ∀ e, e.eval tr t r pub = ((evN env e : Nat) : Fp)
  | .const n => by show ((n : Nat) : Fp) = _; simp only [evN, cast_mod]
  | .col c nx => by
    cases nx
    · show tr.cell t r c = _; simp only [evN, if_false, Bool.false_eq_true, cast_mod, hra.1]
    · show tr.cell t ((r + 1) % tr.height t) c = _; simp only [evN, if_true, cast_mod, hra.2.1]
  | .pub i => by show pub.getD i 0 = _; simp only [evN, cast_mod, hra.2.2.1]
  | .isFirst => by show (if r = 0 then (1 : Fp) else 0) = _; simp only [evN, cast_mod, hra.2.2.2.1]
  | .isLast => by
    show (if r + 1 = tr.height t then (1 : Fp) else 0) = _; simp only [evN, cast_mod, hra.2.2.2.2.1]
  | .isTransition => by
    show (if r + 1 = tr.height t then (0 : Fp) else 1) = _; simp only [evN, cast_mod, hra.2.2.2.2.2]
  | .add a b => by
    show a.eval tr t r pub + b.eval tr t r pub = _
    rw [evN_sound env tr t r pub hra a, evN_sound env tr t r pub hra b]
    simp only [evN, cast_mod, Lean.Grind.Semiring.natCast_add]
  | .mul a b => by
    show a.eval tr t r pub * b.eval tr t r pub = _
    rw [evN_sound env tr t r pub hra a, evN_sound env tr t r pub hra b]
    simp only [evN, cast_mod, Lean.Grind.Semiring.natCast_mul]
  | .neg a => by
    show -(a.eval tr t r pub) = _
    rw [evN_sound env tr t r pub hra a]
    simp only [evN, cast_mod, cast_sub _ (Nat.le_of_lt (evN_lt env a))]

/-- The mem entries of row `r`, over `Nat`. -/
def memRowN (r : Nat) : List (Nat × List Nat) :=
  memIdx.map fun cm => (evN (hEnv r) (dag cm.1), cm.2.map fun m => evN (hEnv r) (dag m))

def castE (e : Nat × List Nat) : Fp × List Fp := (((e.1 : Nat) : Fp), e.2.map fun n => ((n : Nat) : Fp))

theorem memEntries_eq : memEntries hTr 0 hPubF = ((List.range 4096).flatMap memRowN).map castE := by
  unfold memEntries
  rw [hHeight, List.map_flatMap]
  congr 1
  funext r
  simp only [memRowN, List.map_map]
  apply List.map_congr_left
  intro cm _
  simp only [Function.comp_def, castE, List.map_map, evN_sound (hEnv r) hTr 0 r hPubF (hAgrees r)]

/-- The total count of message `m`, over `Nat`. -/
def fsumN (m : List Nat) : List (Nat × List Nat) → Nat
  | [] => 0
  | e :: l => (if e.2 = m then e.1 else 0) + fsumN m l

/-- The non-zero-count entries of the used rows, per 64-row chunk. -/
def chunkNZ (k : Nat) : List (Nat × List Nat) :=
  ((List.range' (64 * k) (min 64 (792 - 64 * k))).flatMap memRowN).filter (fun e => e.1 != 0)

-- The chunks, checked against the literal data (one kernel run each).
set_option maxHeartbeats 0 in
theorem chunk0 : chunkNZ 0 = NvHonestMemData.lit0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk1 : chunkNZ 1 = NvHonestMemData.lit1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk2 : chunkNZ 2 = NvHonestMemData.lit2 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk3 : chunkNZ 3 = NvHonestMemData.lit3 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk4 : chunkNZ 4 = NvHonestMemData.lit4 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk5 : chunkNZ 5 = NvHonestMemData.lit5 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk6 : chunkNZ 6 = NvHonestMemData.lit6 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk7 : chunkNZ 7 = NvHonestMemData.lit7 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk8 : chunkNZ 8 = NvHonestMemData.lit8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk9 : chunkNZ 9 = NvHonestMemData.lit9 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk10 : chunkNZ 10 = NvHonestMemData.lit10 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk11 : chunkNZ 11 = NvHonestMemData.lit11 := by decide +kernel
set_option maxHeartbeats 0 in
theorem chunk12 : chunkNZ 12 = NvHonestMemData.lit12 := by decide +kernel

open NvHonestMemData in
/-- All non-zero-count entries of the used rows. -/
def LNnz : List (Nat × List Nat) :=
  lit0 ++ lit1 ++ lit2 ++ lit3 ++ lit4 ++ lit5 ++ lit6 ++ lit7 ++ lit8 ++ lit9 ++ lit10 ++ lit11 ++ lit12

/-- Entries whose message starts with address `a`. -/
def bucket (a : Nat) : List (Nat × List Nat) := LNnz.filter (fun e => e.2.head? == some a)

-- **The check**: every message has an address below 1024, and within each address's bucket every
-- message's total count is `0 mod p`.
set_option maxHeartbeats 0 in
theorem heads_ok : LNnz.all (fun e => match e.2.head? with | some a => decide (a < 1024) | none => false) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem buckets_ok : (List.range 1024).all
    (fun a => (bucket a).all fun e => fsumN e.2 (bucket a) % P == 0) = true := by
  decide +kernel

theorem range_split : List.range 4096 =
    (List.range 13).flatMap (fun k => List.range' (64 * k) (min 64 (792 - 64 * k))) ++
      List.range' 792 3304 := by decide +kernel

theorem fsumN_filter_nz (m : List Nat) : ∀ L : List (Nat × List Nat),
    fsumN m L = fsumN m (L.filter fun e => e.1 != 0)
  | [] => rfl
  | e :: l => by
    rw [fsumN, fsumN_filter_nz m l]
    by_cases h : e.1 = 0
    · rw [List.filter_cons_of_neg (by simp [h]), h]; split <;> simp
    · rw [List.filter_cons_of_pos (by simp [h]), fsumN]

theorem fsumN_filter_head (m : List Nat) (a : Nat) (hm : m.head? = some a) :
    ∀ L : List (Nat × List Nat), fsumN m L = fsumN m (L.filter fun e => e.2.head? == some a)
  | [] => rfl
  | e :: l => by
    rw [fsumN, fsumN_filter_head m a hm l]
    by_cases h : e.2.head? = some a
    · rw [List.filter_cons_of_pos (by simp [h]), fsumN]
    · rw [List.filter_cons_of_neg (by simp [h])]
      have : ¬ e.2 = m := fun e' => h (e' ▸ hm)
      rw [if_neg this, Nat.zero_add]

theorem LN_filter : ((List.range 13).flatMap (fun k => (List.range' (64 * k) (min 64 (792 - 64 * k))).flatMap
    memRowN)).filter (fun e => e.1 != 0) = LNnz := by
  rw [List.filter_flatMap]
  have : ∀ k, ((List.range' (64 * k) (min 64 (792 - 64 * k))).flatMap memRowN).filter
      (fun e => e.1 != 0) = chunkNZ k := fun k => rfl
  simp only [this]
  show [chunkNZ 0, chunkNZ 1, chunkNZ 2, chunkNZ 3, chunkNZ 4, chunkNZ 5, chunkNZ 6, chunkNZ 7,
    chunkNZ 8, chunkNZ 9, chunkNZ 10, chunkNZ 11, chunkNZ 12].flatten = _
  rw [chunk0, chunk1, chunk2, chunk3, chunk4, chunk5, chunk6, chunk7, chunk8, chunk9, chunk10,
    chunk11, chunk12]
  simp [LNnz]

/-- Zero-ness of an expression on a row whose current-row columns are zero (next-row columns,
public values and selectors not assumed zero). -/
def zeroL : Expr → Bool
  | .col _ false => true
  | .const n => n == 0
  | .add a b => zeroL a && zeroL b
  | .mul a b => zeroL a || zeroL b
  | .neg a => zeroL a
  | _ => false

theorem evN_zeroL (env : Env) (hz : ∀ c, env.loc.getD c 0 = 0) :
    ∀ e, zeroL e = true → evN env e = 0
  | .col c nx, h => by
    cases nx
    · simp only [evN, if_false, Bool.false_eq_true, hz]; rfl
    · simp [zeroL] at h
  | .const n, h => by
    have : n = 0 := by simpa [zeroL] using h
    subst this; rfl
  | .add a b, h => by
    simp only [zeroL, Bool.and_eq_true] at h
    simp only [evN, evN_zeroL env hz a h.1, evN_zeroL env hz b h.2]; rfl
  | .mul a b, h => by
    simp only [zeroL, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [evN, evN_zeroL env hz a h, Nat.zero_mul]; rfl
    · simp only [evN, evN_zeroL env hz b h, Nat.mul_zero]; rfl
  | .neg a, h => by
    simp only [zeroL] at h
    simp only [evN, evN_zeroL env hz a h, Nat.sub_zero, Nat.mod_self]
  | .pub _, h => by simp [zeroL] at h
  | .isFirst, h => by simp [zeroL] at h
  | .isLast, h => by simp [zeroL] at h
  | .isTransition, h => by simp [zeroL] at h

theorem count_zeroL : memIdx.all (fun cm => zeroL (dag cm.1)) = true := by decide +kernel

theorem hRows_len : hRows.length = 792 := by decide

/-- Rows `≥ 792` contribute only zero counts. -/
theorem tail_zero {r : Nat} (hr : 792 ≤ r) : ∀ e ∈ memRowN r, e.1 = 0 := by
  intro e he
  simp only [memRowN, List.mem_map] at he
  obtain ⟨cm, hcm, rfl⟩ := he
  apply evN_zeroL
  · intro c
    show (hRows.getD r []).getD c 0 = 0
    have : hRows.getD r [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hRows_len]; exact hr)]; rfl
    rw [this]; rfl
  · exact List.all_eq_true.1 count_zeroL cm hcm

theorem fsumN_append (m : List Nat) (a b : List (Nat × List Nat)) :
    fsumN m (a ++ b) = fsumN m a + fsumN m b := by
  induction a with
  | nil => simp [fsumN]
  | cons e l ih => simp only [List.cons_append, fsumN, ih]; omega

theorem fsumN_zero (m : List Nat) : ∀ L : List (Nat × List Nat), (∀ e ∈ L, e.1 = 0) → fsumN m L = 0
  | [], _ => rfl
  | e :: l, h => by
    simp only [fsumN, fsumN_zero m l (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      h e List.mem_cons_self]
    split <;> rfl

theorem cast_list_inj : ∀ (a b : List Nat), (∀ x ∈ a, x < P) → (∀ x ∈ b, x < P) →
    a.map (fun n => ((n : Nat) : Fp)) = b.map (fun n => ((n : Nat) : Fp)) → a = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [ZkFormal.PQ.StatePort.nat_inj_of_lt (ha x List.mem_cons_self) (hb y List.mem_cons_self) h.1,
      cast_list_inj xs ys (fun z hz => ha z (List.mem_cons_of_mem _ hz))
        (fun z hz => hb z (List.mem_cons_of_mem _ hz)) h.2]

/-- Entries are reduced. -/
def Reduced (L : List (Nat × List Nat)) : Prop := ∀ e ∈ L, e.1 < P ∧ ∀ x ∈ e.2, x < P

theorem fsumAt_cast (m : List Nat) (hm : ∀ x ∈ m, x < P) :
    ∀ L, Reduced L → fsumAt (m.map fun n => ((n : Nat) : Fp)) (L.map castE) = ((fsumN m L : Nat) : Fp)
  | [], _ => rfl
  | e :: l, hr => by
    simp only [List.map_cons, fsumAt, fsumN, castE,
      fsumAt_cast m hm l (fun e' he' => hr e' (List.mem_cons_of_mem _ he'))]
    have he := hr e List.mem_cons_self
    by_cases h : e.2 = m
    · rw [if_pos (by show e.2.map _ = _; rw [h]), if_pos h, Lean.Grind.Semiring.natCast_add]
    · rw [if_neg (fun h' => h (cast_list_inj _ _ he.2 hm h')), if_neg h, Nat.zero_add]
      grind

theorem fsumAt_none (m : List Fp) : ∀ L : List (Nat × List Nat),
    (∀ e ∈ L, e.1 ≠ 0 → (e.2.map fun n => ((n : Nat) : Fp)) ≠ m) → fsumAt m (L.map castE) = 0
  | [], _ => rfl
  | e :: l, h => by
    simp only [List.map_cons, fsumAt, castE,
      fsumAt_none m l (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    by_cases hz : e.1 = 0
    · show (if (e.2.map _) = m then ((e.1 : Nat) : Fp) else 0) + 0 = 0
      rw [hz]; split <;> rfl
    · rw [if_neg (h e List.mem_cons_self hz)]; rfl

theorem memRowN_reduced (r : Nat) : Reduced (memRowN r) := by
  intro e he
  simp only [memRowN, List.mem_map] at he
  obtain ⟨cm, -, rfl⟩ := he
  refine ⟨evN_lt _ _, fun x hx => ?_⟩
  simp only [List.mem_map] at hx
  obtain ⟨m, -, rfl⟩ := hx
  exact evN_lt _ _

/-- **The honest trace's mem bus balances.** -/
theorem honest_mem : MemBalance hTr 0 hPubF := by
  intro m
  rw [memEntries_eq]
  have hsplit : (List.range 4096).flatMap memRowN =
      (List.range 13).flatMap (fun k => (List.range' (64 * k) (min 64 (792 - 64 * k))).flatMap
        memRowN) ++ (List.range' 792 3304).flatMap memRowN := by
    rw [range_split, List.flatMap_append, List.flatMap_assoc]
  have hT : ∀ e ∈ (List.range' 792 3304).flatMap memRowN, e.1 = 0 := by
    intro e he
    obtain ⟨r, hr, he⟩ := List.mem_flatMap.1 he
    exact tail_zero (List.mem_range'_1.1 hr).1 e he
  have hred : Reduced ((List.range 4096).flatMap memRowN) := by
    intro e he
    obtain ⟨r, -, he⟩ := List.mem_flatMap.1 he
    exact memRowN_reduced r e he
  by_cases hex : ∃ e ∈ (List.range 4096).flatMap memRowN, e.1 ≠ 0 ∧
      (e.2.map fun n => ((n : Nat) : Fp)) = m
  · obtain ⟨e, he, hz, rfl⟩ := hex
    rw [fsumAt_cast e.2 (hred e he).2 _ hred, hsplit, fsumN_append, fsumN_zero _ _ hT, Nat.add_zero,
      fsumN_filter_nz, LN_filter]
    have heL : e ∈ LNnz := by
      rw [← LN_filter]
      rw [hsplit] at he
      rcases List.mem_append.1 he with h | h
      · exact List.mem_filter.2 ⟨h, by simp [hz]⟩
      · exact absurd (hT e h) hz
    have hh := List.all_eq_true.1 heads_ok e heL
    cases ha : e.2.head? with
    | none => rw [ha] at hh; simp at hh
    | some a =>
      rw [ha] at hh
      have ha' : a < 1024 := by simpa using hh
      rw [fsumN_filter_head e.2 a ha]
      have hb := List.all_eq_true.1 (List.all_eq_true.1 buckets_ok a (List.mem_range.2 ha')) e
        (List.mem_filter.2 ⟨heL, by simp [ha]⟩)
      simp only [beq_iff_eq] at hb
      show (((fsumN e.2 (bucket a)) : Nat) : Fp) = 0
      rw [← cast_mod, hb]
      rfl
  · simp only [not_exists, not_and] at hex
    exact fsumAt_none m _ (fun e he hz hm => hex e he hz hm)

#print axioms honest_mem

end ZkFormal.PQ.NvHonestMem
