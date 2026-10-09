import ZkFormal.NearV3.Sched.Complete.Cmp

/-!
# ZkFormal.NearV3.Sched.Complete.Height — row counts and height bounds of the scheduler tables (M4)

Every scheduler table holds all instances `τ` of the claim. Instance `τ` is summarised by its
public / run counts (`IStat`):

* `n` shards (`N = n²` links), whether the previous `0x0f` value is present (`pre`);
* `C` converted requests (raw requests with a set bit), `S` processing steps (= bucket entries
  = `sprV3` entry rows), `Rd` rounds, `K` RNG words drawn.

**Row counts per instance** (from the generators' structure, `Gen/*`):

| table | rows of one instance |
|---|---|
| `schV3` codec | `5 + 24·N + 32 + 32 = |post| + 32` (`|post| = 37 + 24·N`) |
| `ssdV3` scan + distribute | `[C > 0]·(1 + 20·C) + 2n + n·(1 + n)` |
| `sprV3` process | `16 + Rd + S` |
| `smmV3` memory | `(N + 2n)` INIT rows `+ C` READs `+ 3·S` GRANTs |
| `scpV3` comparator | `≤ C + 7·S + Rd + 3·N + 2n` (memory: `C + 6S`; process: `≤ Rd + S`; codec: `N` + `N` in τ = 0; distribute: `2n + #allowed ≤ 2n + N`) |
| `shufV3` / `genV3` / `chachaV3` (lane v3-chacha) | `S` / `K` / `86·⌈K/16⌉` |

Each table's height is `2^maxLog`-bounded when the total over instances plus its forced padding
row (`+1`) is.

**Hypotheses (all parametric):**
* A7 (`B0`): `Σ_τ (|pre_τ| + |post_τ|) ≤ B0`;
* A8: `C ≤ N` (at most `n` requests per sender) and `n ≤ 64` (`prepD0` facts);
* the **step budget** `Steps κ`: `Rd ≤ S` (rounds are nonempty) and `S ≤ C + κ·n` (a
  re-push needs a successful grant, which spends `≥ ⌊D/40⌋ ≥ 102,357` of a sender budget
  `≤ 4,500,000`, so at most 43 per sender: `κ = 43`; **proved** from the replay,
  `Spec/Steps.steps_pv86`, and discharged per instance in `Complete/Steps.heights_prep`);
* at most `T` instances.

**Results** (`B0 = 2,000,000`, `maxLog = 22`, `T = 33`, `κ = 43`):
* without the step budget (only `Shape`: `Rd ≤ S ≤ 40·C`): codec `≤ 2·B0 + 1` ✓, scan + distribute `≤ B0 + 1` ✓; process, memory and
  comparator **do not** fit: the worst case (`worst`: 20 instances `n = 64`, one `n = 37`, one
  `n = 3`, `C = N`, `S = Rd = 40·C`, no previous values; A7 holds with `Σ |post| = 1,999,966`)
  needs 6,664,193 / 10,164,997 / 26,991,193 rows (`worst_*`);
* with `κ`: process `≤ 348,826 + 1`, memory `≤ 693,338 + 1`, comparator `≤ 1,730,752 + 1`
  (all `≤ 2^22`, `heights_22`).
-/

namespace ZkFormal.NearV3.Sched.Complete

/-- Counts of one scheduler instance. -/
structure IStat where
  n : Nat
  pre : Bool
  C : Nat
  S : Nat
  Rd : Nat
  K : Nat
  deriving Repr, DecidableEq

namespace IStat

def N (s : IStat) : Nat := s.n * s.n
def postLen (s : IStat) : Nat := 37 + 24 * s.N
def preLen (s : IStat) : Nat := if s.pre then s.postLen else 0

/-! ## Rows of one instance -/

def codecRows (s : IStat) : Nat := 5 + 24 * s.N + 32 + 32
def sdRows (s : IStat) : Nat := (if s.C = 0 then 0 else 1 + 20 * s.C) + (2 * s.n + s.n * (1 + s.n))
def procRows (s : IStat) : Nat := 16 + s.Rd + s.S
def memRows (s : IStat) : Nat := (s.N + 2 * s.n) + s.C + 3 * s.S
/-- Upper bound of the comparator rows of one instance. -/
def cmpRows (s : IStat) : Nat := s.C + 7 * s.S + s.Rd + 3 * s.N + 2 * s.n
def shufRows (s : IStat) : Nat := s.S
def genRows (s : IStat) : Nat := s.K
def chachaRows (s : IStat) : Nat := 86 * ((s.K + 15) / 16)

end IStat

open IStat

/-- Rows of a table over all instances. -/
def total (f : IStat → Nat) (Ps : List IStat) : Nat := (Ps.map f).sum

/-! ## Hypotheses -/

/-- A7: total previous + new `0x0f` value bytes `≤ B0`. -/
def A7 (B0 : Nat) (Ps : List IStat) : Prop := total (fun s => s.preLen + s.postLen) Ps ≤ B0

/-- A8 (at most `n` requests per sender: `C ≤ N`) and `n ≤ 64` (both `prepD0` facts,
`Complete/Steps.statOf_ok`). -/
def A8 (Ps : List IStat) : Prop := ∀ s ∈ Ps, s.C ≤ s.N ∧ s.n ≤ 64

/-- The step budget: rounds are nonempty (`Rd ≤ S`) and at most `κ` re-pushes per sender
shard (`S ≤ C + κ·n`). **Proved** for the replay with `κ = 43` under PV 86
(`Spec/Steps.steps_pv86`, `Complete/Steps.statOf_ok`). -/
def Steps (κ : Nat) (Ps : List IStat) : Prop := ∀ s ∈ Ps, s.Rd ≤ s.S ∧ s.S ≤ s.C + κ * s.n

/-- The request structure alone (no step budget): `Rd ≤ S ≤ 40·C` (`incsOf_length_le`). -/
def Shape (Ps : List IStat) : Prop := ∀ s ∈ Ps, s.Rd ≤ s.S ∧ s.S ≤ 40 * s.C

/-! ## Sums -/

theorem total_le {f g : IStat → Nat} {Ps : List IStat} (h : ∀ s ∈ Ps, f s ≤ g s) :
    total f Ps ≤ total g Ps := by
  induction Ps with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [total, List.map_cons, List.sum_cons] at *
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun s hs => h s (List.mem_cons_of_mem _ hs))

theorem total_add (f g : IStat → Nat) (Ps : List IStat) :
    total (fun s => f s + g s) Ps = total f Ps + total g Ps := by
  induction Ps with
  | nil => rfl
  | cons x l ih => simp only [total, List.map_cons, List.sum_cons] at *; rw [ih]; omega

theorem total_mul (a : Nat) (f : IStat → Nat) (Ps : List IStat) :
    total (fun s => a * f s) Ps = a * total f Ps := by
  induction Ps with
  | nil => simp [total]
  | cons x l ih => simp only [total, List.map_cons, List.sum_cons] at *; rw [ih, Nat.mul_add]

theorem total_const (a : Nat) (Ps : List IStat) : total (fun _ => a) Ps = a * Ps.length := by
  induction Ps with
  | nil => simp [total]
  | cons x l ih => simp only [total, List.map_cons, List.sum_cons, List.length_cons] at *; rw [ih]; rw [Nat.mul_succ]; omega

/-- `Σ N ≤ B0 / 24` under A7 (as `24·Σ N ≤ B0`). -/
theorem sumN_le {B0 : Nat} {Ps : List IStat} (h7 : A7 B0 Ps) : 24 * total IStat.N Ps ≤ B0 := by
  have : total (fun s => 24 * s.N) Ps ≤ total (fun s => s.preLen + s.postLen) Ps :=
    total_le fun s _ => by unfold IStat.postLen; omega
  rw [total_mul] at this
  exact Nat.le_trans this h7

theorem sumPost_le {B0 : Nat} {Ps : List IStat} (h7 : A7 B0 Ps) : total IStat.postLen Ps ≤ B0 :=
  Nat.le_trans (total_le fun s _ => Nat.le_add_left _ _) h7

theorem sumn_le {T : Nat} {Ps : List IStat} (h8 : A8 Ps) (hT : Ps.length ≤ T) :
    total IStat.n Ps ≤ 64 * T := by
  have := total_le (g := fun _ => 64) (Ps := Ps) fun s hs => (h8 s hs).2
  rw [total_const] at this
  exact Nat.le_trans this (Nat.mul_le_mul_left _ hT)

theorem n_le_N (s : IStat) : s.n ≤ s.N := by
  unfold IStat.N
  rcases Nat.eq_zero_or_pos s.n with h | h
  · rw [h]; exact Nat.zero_le _
  · exact Nat.le_mul_of_pos_left _ h

/-! ## Codec and scan + distribute: A7 alone -/

/-- `schV3`: `rows ≤ 2·B0` (each instance has `|post| + 32 ≤ 2·|post|` rows). -/
theorem codec_total {B0 : Nat} {Ps : List IStat} (h7 : A7 B0 Ps) : total codecRows Ps ≤ 2 * B0 := by
  have h1 : total codecRows Ps ≤ total (fun s => 2 * s.postLen) Ps :=
    total_le fun s _ => by unfold codecRows IStat.postLen; omega
  rw [total_mul] at h1
  have := sumPost_le h7
  omega

/-- `ssdV3`: `rows ≤ B0` (each instance has `≤ 1 + 24·N ≤ |post|` rows, by A8). -/
theorem sd_total {B0 : Nat} {Ps : List IStat} (h7 : A7 B0 Ps) (h8 : A8 Ps) : total sdRows Ps ≤ B0 := by
  refine Nat.le_trans (total_le fun s hs => ?_) (sumPost_le h7)
  have hC := (h8 s hs).1
  have hn := n_le_N s
  have hsq : s.n * (1 + s.n) = s.n + s.N := by unfold IStat.N; rw [Nat.mul_add, Nat.mul_one]
  unfold sdRows IStat.postLen
  rw [hsq]
  split <;> omega

/-! ## Process, memory, comparator: with the step budget -/

theorem proc_total {B0 T κ : Nat} {Ps : List IStat} (h7 : A7 B0 Ps) (h8 : A8 Ps) (hb : Steps κ Ps)
    (hT : Ps.length ≤ T) : 24 * total procRows Ps ≤ 24 * (16 * T) + 2 * B0 + 24 * (2 * κ * (64 * T)) := by
  have h1 : total procRows Ps ≤ total (fun s => 16 + (2 * s.N + 2 * κ * s.n)) Ps :=
    total_le fun s hs => by
      have := (h8 s hs); have := hb s hs
      have : 2 * κ * s.n = 2 * (κ * s.n) := Nat.mul_assoc _ _ _
      unfold procRows; omega
  rw [total_add, total_const, total_add, total_mul, total_mul] at h1
  have hN := sumN_le h7
  have hn := sumn_le h8 hT
  have : 2 * κ * total IStat.n Ps ≤ 2 * κ * (64 * T) := Nat.mul_le_mul_left _ hn
  have : 16 * Ps.length ≤ 16 * T := Nat.mul_le_mul_left _ hT
  omega

theorem mem_total {B0 T κ : Nat} {Ps : List IStat} (h7 : A7 B0 Ps) (h8 : A8 Ps) (hb : Steps κ Ps)
    (hT : Ps.length ≤ T) : 24 * total memRows Ps ≤ 5 * B0 + 24 * ((2 + 3 * κ) * (64 * T)) := by
  have h1 : total memRows Ps ≤ total (fun s => 5 * s.N + (2 + 3 * κ) * s.n) Ps :=
    total_le fun s hs => by
      have := (h8 s hs); have := hb s hs
      have : (2 + 3 * κ) * s.n = 2 * s.n + 3 * (κ * s.n) := by rw [Nat.add_mul, Nat.mul_assoc]
      unfold memRows; omega
  rw [total_add, total_mul, total_mul] at h1
  have hN := sumN_le h7
  have : (2 + 3 * κ) * total IStat.n Ps ≤ (2 + 3 * κ) * (64 * T) := Nat.mul_le_mul_left _ (sumn_le h8 hT)
  omega

theorem cmp_total {B0 T κ : Nat} {Ps : List IStat} (h7 : A7 B0 Ps) (h8 : A8 Ps) (hb : Steps κ Ps)
    (hT : Ps.length ≤ T) : 24 * total cmpRows Ps ≤ 12 * B0 + 24 * ((8 * κ + 2) * (64 * T)) := by
  have h1 : total cmpRows Ps ≤ total (fun s => 12 * s.N + (8 * κ + 2) * s.n) Ps :=
    total_le fun s hs => by
      have := (h8 s hs); have := hb s hs
      have : (8 * κ + 2) * s.n = 8 * (κ * s.n) + 2 * s.n := by rw [Nat.add_mul, Nat.mul_assoc]
      unfold cmpRows; omega
  rw [total_add, total_mul, total_mul] at h1
  have hN := sumN_le h7
  have : (8 * κ + 2) * total IStat.n Ps ≤ (8 * κ + 2) * (64 * T) := Nat.mul_le_mul_left _ (sumn_le h8 hT)
  omega

/-! ## Parametric height statements -/

/-- Height bound of a table with one forced padding row, from a bound `F` on its rows. -/
theorem fits {rows F maxLog : Nat} (h : rows ≤ F) (hF : F + 1 ≤ 2 ^ maxLog) : rows + 1 ≤ 2 ^ maxLog :=
  Nat.le_trans (Nat.add_le_add_right h 1) hF

/-- Row bounds of the five scheduler tables (each `+ 1` padding row), parametric in `B0`,
the instance count `T` and the step budget `κ`. -/
def codecMax (B0 : Nat) : Nat := 2 * B0
def sdMax (B0 : Nat) : Nat := B0
def procMax (B0 T κ : Nat) : Nat := 16 * T + B0 / 12 + 2 * κ * (64 * T)
def memMax (B0 T κ : Nat) : Nat := 5 * B0 / 24 + (2 + 3 * κ) * (64 * T)
def cmpMax (B0 T κ : Nat) : Nat := B0 / 2 + (8 * κ + 2) * (64 * T)

theorem heights (B0 T κ maxLog : Nat) (Ps : List IStat) (h7 : A7 B0 Ps) (h8 : A8 Ps)
    (hb : Steps κ Ps) (hT : Ps.length ≤ T)
    (hc : codecMax B0 + 1 ≤ 2 ^ maxLog) (hs : sdMax B0 + 1 ≤ 2 ^ maxLog)
    (hp : procMax B0 T κ + 1 ≤ 2 ^ maxLog) (hm : memMax B0 T κ + 1 ≤ 2 ^ maxLog)
    (hq : cmpMax B0 T κ + 1 ≤ 2 ^ maxLog) :
    total codecRows Ps + 1 ≤ 2 ^ maxLog ∧ total sdRows Ps + 1 ≤ 2 ^ maxLog ∧
    total procRows Ps + 1 ≤ 2 ^ maxLog ∧ total memRows Ps + 1 ≤ 2 ^ maxLog ∧
    total cmpRows Ps + 1 ≤ 2 ^ maxLog := by
  refine ⟨fits (codec_total h7) hc, fits (sd_total h7 h8) hs, fits ?_ hp, fits ?_ hm, fits ?_ hq⟩
  · have := proc_total h7 h8 hb hT; unfold procMax; omega
  · have := mem_total h7 h8 hb hT; unfold memMax; omega
  · have := cmp_total h7 h8 hb hT; unfold cmpMax; omega

/-- **Instantiation**: `B0 = 2,000,000` (`ChunkValidationV0a.B0`), at most 33 instances
(`prepD0_len`), step budget `κ = 43`, `maxLog = 22`. -/
theorem heights_22 (Ps : List IStat) (h7 : A7 2000000 Ps) (h8 : A8 Ps) (hb : Steps 43 Ps)
    (hT : Ps.length ≤ 33) :
    total codecRows Ps + 1 ≤ 2 ^ 22 ∧ total sdRows Ps + 1 ≤ 2 ^ 22 ∧
    total procRows Ps + 1 ≤ 2 ^ 22 ∧ total memRows Ps + 1 ≤ 2 ^ 22 ∧
    total cmpRows Ps + 1 ≤ 2 ^ 22 :=
  heights 2000000 33 43 22 Ps h7 h8 hb hT (by decide) (by decide) (by decide) (by decide) (by decide)

theorem maxes_22 : codecMax 2000000 = 4000000 ∧ sdMax 2000000 = 2000000 ∧
    procMax 2000000 33 43 = 348826 ∧ memMax 2000000 33 43 = 693338 ∧
    cmpMax 2000000 33 43 = 1730752 := by decide

/-! ## Without the step budget: the worst case -/

/-- 20 instances with `n = 64`, one with `n = 37`, one with `n = 3`; `C = N`, `S = Rd = 40·C`,
no previous value, `K = 0`. -/
def worst : List IStat :=
  List.replicate 20 ⟨64, false, 4096, 163840, 163840, 0⟩ ++
    [⟨37, false, 1369, 54760, 54760, 0⟩, ⟨3, false, 9, 360, 360, 0⟩]

theorem worst_a7 : A7 2000000 worst ∧ total IStat.postLen worst = 1999966 := by unfold A7; decide

theorem worst_a8 : A8 worst ∧ Shape worst := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩ <;>
  simp only [worst, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
  rcases hs with ⟨-, rfl⟩ | rfl | rfl <;> decide

theorem worst_len : worst.length = 22 := by decide

/-- Rows (with the padding row) of process, memory and comparator in the worst case: all
`> 2^22 = 4,194,304`. -/
theorem worst_rows : total procRows worst + 1 = 6664193 ∧ total memRows worst + 1 = 10164997 ∧
    total cmpRows worst + 1 = 26991193 := by decide

theorem worst_exceeds : ¬ total procRows worst + 1 ≤ 2 ^ 22 ∧ ¬ total memRows worst + 1 ≤ 2 ^ 22 ∧
    ¬ total cmpRows worst + 1 ≤ 2 ^ 22 := by decide

/-- With A7 and A8 alone, codec and scan + distribute fit `2^22` at `B0 = 2,000,000`. -/
theorem codec_sd_22 (Ps : List IStat) (h7 : A7 2000000 Ps) (h8 : A8 Ps) :
    total codecRows Ps + 1 ≤ 2 ^ 22 ∧ total sdRows Ps + 1 ≤ 2 ^ 22 :=
  ⟨fits (codec_total h7) (by decide), fits (sd_total h7 h8) (by decide)⟩

/-! ## Lane tables: `shufV3`, `genV3`, `chachaV3`

`shufV3` has one row per step (`S`), `genV3` one per drawn word (`K`), `chachaV3` 86 per
ChaCha block (`⌈K/16⌉` per instance). The spec bounds `K` only by the fuel:
`K + 64·Rd ≤ 64·S` (`Fuel`; `Spec/Draws.lp_draws`: `≤ 64` words per `gen_index` call, `S − Rd`
calls). -/

/-- The fuel bound on the words drawn (proved for the replay, `Spec/Draws.lp_draws`). -/
def Fuel (Ps : List IStat) : Prop := ∀ s ∈ Ps, s.K + 64 * s.Rd ≤ 64 * s.S

/-- `shufV3` rows from the step budget: `24·Σ S ≤ B0 + 24·κ·64·T`. -/
theorem shuf_total {B0 T κ : Nat} {Ps : List IStat} (h7 : A7 B0 Ps) (h8 : A8 Ps) (hb : Steps κ Ps)
    (hT : Ps.length ≤ T) : 24 * total shufRows Ps ≤ B0 + 24 * (κ * (64 * T)) := by
  have h1 : total shufRows Ps ≤ total (fun s => s.N + κ * s.n) Ps :=
    total_le fun s hs => by have := h8 s hs; have := hb s hs; unfold shufRows; omega
  rw [total_add, total_mul] at h1
  have hN := sumN_le h7
  have : κ * total IStat.n Ps ≤ κ * (64 * T) := Nat.mul_le_mul_left _ (sumn_le h8 hT)
  omega

/-- `chachaV3` rows from the words: `16·rows ≤ 86·(Σ K + 15·T)`. -/
theorem chacha_total {T : Nat} {Ps : List IStat} (hT : Ps.length ≤ T) :
    16 * total chachaRows Ps ≤ 86 * (total genRows Ps + 15 * T) := by
  have h1 : total (fun s => 16 * chachaRows s) Ps ≤ total (fun s => 86 * genRows s + 86 * 15) Ps :=
    total_le fun s _ => by unfold chachaRows genRows; omega
  rw [total_mul, total_add, total_mul, total_const] at h1
  have : 86 * 15 * Ps.length ≤ 86 * 15 * T := Nat.mul_le_mul_left _ hT
  omega

def shufMax (B0 T κ : Nat) : Nat := B0 / 24 + κ * (64 * T)
def chachaMax (W T : Nat) : Nat := 86 * (W + 15 * T) / 16

/-- **Lane heights, parametric in a bound `W` on the total words drawn.** `W` is **not** a
consequence of the spec (see `worstK`); it is the execution-level condition the lane tables
need. -/
theorem lane_heights (B0 T κ W maxLog : Nat) (Ps : List IStat) (h7 : A7 B0 Ps) (h8 : A8 Ps)
    (hb : Steps κ Ps) (hT : Ps.length ≤ T) (hW : total genRows Ps ≤ W)
    (hs : shufMax B0 T κ + 1 ≤ 2 ^ maxLog) (hg : W + 1 ≤ 2 ^ maxLog)
    (hc : chachaMax W T + 1 ≤ 2 ^ maxLog) :
    total shufRows Ps + 1 ≤ 2 ^ maxLog ∧ total genRows Ps + 1 ≤ 2 ^ maxLog ∧
    total chachaRows Ps + 1 ≤ 2 ^ maxLog := by
  refine ⟨fits ?_ hs, fits hW hg, fits ?_ hc⟩
  · have := shuf_total h7 h8 hb hT; unfold shufMax; omega
  · have := chacha_total (Ps := Ps) hT
    have : 86 * (total genRows Ps + 15 * T) ≤ 86 * (W + 15 * T) := Nat.mul_le_mul_left _ (by omega)
    unfold chachaMax; omega

/-- **Lane heights at the RelD0a word bound `W0 = 770,000`** (A9 `e.chacha_words`, user decision
2026-10-09; `B0 = 2,000,000`, `T = 33`, `κ = 43`): `shufV3 ≤ 174,149 < 2^22`,
`genV3 ≤ 770,000 < 2^20`, `chachaV3 ≤ 4,141,410 < 2^22` rows (`laneMaxes_770k`). The ChaCha
bound needs `2^22`; the deployed `Chacha.Table.maxLog` is still `21` (raising it is blocked by
the fingerprint budget of four candidate families, `chacha_cap_short` and
STATUS-V3-AIR §5), so this is a row-count theorem, not yet the table's completeness bound. It
replaces the earlier `W = 360,000` instantiation (`lane_22`, chachaV3 `≤ 1,937,660 < 2^21`). -/
theorem lane_770k_22 (Ps : List IStat) (h7 : A7 2000000 Ps) (h8 : A8 Ps) (hb : Steps 43 Ps)
    (hT : Ps.length ≤ 33) (hW : total genRows Ps ≤ 770000) :
    total shufRows Ps + 1 ≤ 2 ^ 22 ∧ total genRows Ps + 1 ≤ 2 ^ 20 ∧
    total chachaRows Ps + 1 ≤ 2 ^ 22 := by
  have bounds := lane_heights 2000000 33 43 770000 22 Ps h7 h8 hb hT hW
    (by decide) (by decide) (by decide)
  exact ⟨bounds.1, fits hW (by decide), bounds.2.2⟩

theorem laneMaxes_770k : chachaMax 770000 33 = 4141410 ∧
    chachaMax 770000 33 + 1 ≤ 2 ^ 22 ∧ 2 ^ 21 < chachaMax 770000 33 + 1 := by decide

/-- `shufV3`'s maximum at `B0` (unchanged by `W`). -/
theorem shufMax_B0 : shufMax 2000000 33 43 = 174149 := by decide

/-- The largest word bound whose ChaCha lane fits `2^22` rows (with `T = 33`) is `779,840`;
`W0 = 770,000` is within it. -/
theorem chachaMax_tight : chachaMax 779840 33 + 1 ≤ 2 ^ 22 ∧ 2 ^ 22 < chachaMax 779841 33 + 1 := by
  decide

/-- **Worst case of the lane tables** under A7, A8, the step budget and the fuel bound
(maximum of `Σ (S − Rd)` over claims of `≤ 33` instances with `C = N`, `S = C + 43·n`, one
round each, no previous values, found by exhaustive search; every call draws 64 words):
23 instances `n = 50`, 6 `n = 49`, 2 `n = 51`, one `n = 53`, one `n = 58`
(`Σ |post| = 1,999,965`). -/
def worstK : List IStat :=
  (List.replicate 23 50 ++ List.replicate 6 49 ++ [51, 51, 53, 58]).map fun n =>
    ⟨n, false, n * n, n * n + 43 * n, 1, 64 * (n * n + 43 * n - 1)⟩

theorem worstK_ok : A7 2000000 worstK ∧ A8 worstK ∧ Steps 43 worstK ∧ Shape worstK ∧ Fuel worstK ∧
    worstK.length = 33 := by
  refine ⟨by unfold A7; decide, ?_, ?_, ?_, ?_, by decide⟩ <;>
  · intro s hs
    simp only [worstK, List.mem_map, List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    obtain ⟨n, hn, rfl⟩ := hs
    rcases hn with ((⟨-, rfl⟩ | ⟨-, rfl⟩) | rfl | rfl | rfl | rfl) <;> decide

/-- 154,499 calls, 9,887,936 words: `genV3` and `chachaV3` exceed `2^22` (`shufV3` fits). -/
theorem worstK_rows : total shufRows worstK = 154532 ∧ total genRows worstK = 9887936 ∧
    total chachaRows worstK = 53147656 := by decide

theorem worstK_exceeds : ¬ total genRows worstK + 1 ≤ 2 ^ 22 ∧ ¬ total chachaRows worstK + 1 ≤ 2 ^ 22 := by
  decide

end ZkFormal.NearV3.Sched.Complete
