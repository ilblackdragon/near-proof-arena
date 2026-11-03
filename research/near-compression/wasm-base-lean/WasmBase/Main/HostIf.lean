import WasmBase.Main.SegChainSigma
import WasmBase.Main.SegLinkage

/-!
# WasmBase.Main.HostIf — the bus-level host contract `HostIf` and the σ-thread (E2E M6, HOSTIF)

The host analogue of the SHA chip's `ChipIf` (m6 README §3).  A segment's HOST rows are answered
by *something* (today the free oracle `HOSTO`; after the join lane B's state rows).  `HostIf` is
what that answerer must satisfy, phrased against a **per-call sequence of host sides**
`σc 0, σc 1, …, σc m` (`σc j : St`, read through `sideR`: every non-Wasm field with the gas
register blanked, plus the register file), one entry per host call of the segment, in STATE-time
order.

## Indexing: host calls by rank

`hts : List Nat` is the list of the active HOST rows' STATE times (`times`/`onto`, no duplicates).
The **index of a host call** at time `t` is its rank `rank hts t` = number of host times `< t`, so
the `j`-th call goes from `σc j` to `σc (j + 1)`; no sortedness is needed.  The **σ-thread** is the
piecewise-constant extension by STATE time, `thread hts σc t := σc (rank hts (t % P))` (the
`% P` makes it a function of the field element `(t : F)`, which is all a STATE message pins):

* `thread_keep` — constant across a non-host time; `thread_host` — at a host time it steps from
  `σc j` to `σc (j + 1)`;
* `thread_in` / `thread_out` — `σc 0` at `t_in + 1` and `σc m` at `t_out + 1` (host times in
  `(t_in, t_out]`), i.e. the in/out pins of `seg_sound_σ`;
* **`sigKeep_of_hostIf`** / `sigKeep_of_hostIf_seg` — the thread satisfies `SigKeep` (task (a)).

## The contract (per HOST row, `j` its rank)

* `ans : HostWit` — the row's bus traffic (STATE in/out, consumed `consCHS` = stack args + HOSTB
  bytes read + REG-C reads + gas register; produced `prodCHS` = result word + HOSTB bytes written +
  REG-C writes + gas register `g_after`) is the honest answer **from some related pre-state whose
  host side is `σc j`**, landing at host side `σc (j + 1)` (`HostPost`: the body of `RowSpecSegJ`
  with the out-pin);
* `reg : RegStep` — the row's REG-C traffic turns a bus view of `σc j`'s register file into one of
  `σc (j + 1)`'s (a statement about messages and `σ` only);
* `cap` — every `σc j` has registers below `Register.cap`.

## The spec half: `HostFootprint` (FOOT2's lemma, taken as a named hypothesis)

`HostFootprint`: per HOST row, `HostPost` transfers between two related pre-states with the same
host side (`post`, the two-run footprint of `callHost` read through the row relation), and a
continuing step from a pre-state with host side `σc j` lands at register file
`(σc (j + 1)).registers` (`regs`).  This is exactly what FOOT2's `callHost_two_run` + the bridge
("single-state facts ⇒ HoldRowSσ") produce; nothing here depends on how.

## Results

* **`holdRowSσ_of_hostIf`** (task (c)): `HostIf` + `HostFootprint` + the HOST rows' flat AIR facts
  (`HostRowsFlat`) ⇒ `HoldRowSσ X tr pub sg (thread hts σc)`;
* **`hostRelyσ_of_hostIf`**: `HostIf` + `HostFootprint.regs` ⇒ `HostRelyσ X tr pub (thread hts σc)`;
* **`host_msgs_of_thread`** (task (b)): from any related pre-state on the thread, the HOST row's
  step continues to a state on the thread at `σc (j + 1)`, whose gas register is the row's
  `g_after` segment value and whose Wasm/host view contains every message the row produced
  (result word, bytes written, register entries, gas register): the bus messages are the run's;
* **`seg_sound_hostIf`**: `seg_sound_σ` with its σ-premises discharged by `HostIf` +
  `HostFootprint` + `HostRowsFlat`, the pins being `σc 0` and `σc m`.

The lane-E tie (M6.5) and the producer obligations (M6.4) are in `Main/HostIfTape.lean`; the
per-function answer functions in `Main/HostAns.lean`.
-/

namespace WasmBase
namespace HostIf

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Rank and the piecewise-constant thread -/

/-- The rank of time `t` among the host times: how many host calls happen strictly before `t`. -/
def rank (hts : List Nat) (t : Nat) : Nat := (hts.filter (fun x => decide (x < t))).length

/-- **The σ-thread**: the per-call sequence `σc` extended to every STATE time, constant between host
calls.  A function of `t % P` (the STATE message's field element). -/
def thread (hts : List Nat) (σc : Nat → St) (t : Nat) : St := σc (rank hts (t % P))

theorem rank_succ_of_not_mem {hts : List Nat} {t : Nat} (h : t ∉ hts) : rank hts (t + 1) = rank hts t := by
  unfold rank
  congr 1
  apply List.filter_congr
  intro x hx
  have : x ≠ t := fun e => h (e ▸ hx)
  simp only [decide_eq_decide]
  omega

theorem rank_succ_of_mem {hts : List Nat} {t : Nat} (hnd : hts.Nodup) (h : t ∈ hts) :
    rank hts (t + 1) = rank hts t + 1 := by
  induction hts with
  | nil => simp at h
  | cons x l ih =>
    obtain ⟨hxl, hl⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp h with rfl | hm
    · have e := rank_succ_of_not_mem hxl
      unfold rank at e ⊢
      simp only [List.filter_cons, Nat.lt_succ_self, decide_true, Nat.lt_irrefl, decide_false,
        List.length_cons, ite_true]
      simp only [Bool.false_eq_true, ite_false]
      omega
    · have e := ih hl hm
      have hne : x ≠ t := fun e => hxl (e ▸ hm)
      unfold rank at e ⊢
      simp only [List.filter_cons]
      by_cases hx : x < t
      · have hx' : x < t + 1 := by omega
        simp only [hx, hx', decide_true, ite_true, List.length_cons]; omega
      · have hx' : ¬ x < t + 1 := by omega
        simp only [hx, hx', decide_false, Bool.false_eq_true, ite_false]; omega

theorem rank_eq_zero {hts : List Nat} {t : Nat} (h : ∀ x ∈ hts, t ≤ x) : rank hts t = 0 := by
  unfold rank
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx
  have := h x hx
  simp only [decide_eq_true_eq]; omega

theorem rank_eq_length {hts : List Nat} {t : Nat} (h : ∀ x ∈ hts, x < t) : rank hts t = hts.length := by
  unfold rank
  rw [List.filter_eq_self.mpr]
  intro x hx
  simpa using h x hx

theorem filter_length_lt {l : List Nat} {p : Nat → Bool} {a : Nat} (ha : a ∈ l) (hp : p a = false) :
    (l.filter p).length < l.length := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    have hle := List.length_filter_le p l
    rcases List.mem_cons.mp ha with rfl | hm
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ite_false, List.length_cons]; omega
    · have := ih hm
      simp only [List.filter_cons, List.length_cons]
      split <;> (try simp only [List.length_cons]) <;> omega

theorem rank_lt_length {hts : List Nat} {t : Nat} (h : t ∈ hts) : rank hts t < hts.length :=
  filter_length_lt h (by simp)

theorem thread_of_lt {hts : List Nat} {σc : Nat → St} {t : Nat} (h : t < P) :
    thread hts σc t = σc (rank hts t) := by
  unfold thread; rw [Nat.mod_eq_of_lt h]

/-- The thread reads a STATE time through its field element. -/
theorem thread_cast (hts : List Nat) (σc : Nat → St) (t : Nat) :
    thread hts σc (((t : Nat) : F)).toNat = thread hts σc t := by
  unfold thread
  have : (((t : Nat) : F)).toNat = t % P := Fp.toNat_ofNat t
  rw [this, Nat.mod_mod]

/-- **Constant across a non-host time.** -/
theorem thread_keep {hts : List Nat} {σc : Nat → St} {t : Nat} (h : t ∉ hts) (ht : t + 1 < P) :
    thread hts σc (t + 1) = thread hts σc t := by
  rw [thread_of_lt ht, thread_of_lt (by omega), rank_succ_of_not_mem h]

/-- **At a host time the thread steps from `σc j` to `σc (j + 1)`**, `j` the call's rank. -/
theorem thread_host {hts : List Nat} {σc : Nat → St} {t : Nat} (hnd : hts.Nodup) (h : t ∈ hts)
    (ht : t + 1 < P) :
    thread hts σc t = σc (rank hts t) ∧ thread hts σc (t + 1) = σc (rank hts t + 1) := by
  rw [thread_of_lt ht, thread_of_lt (by omega), rank_succ_of_mem hnd h]
  exact ⟨rfl, rfl⟩

/-- **In-pin**: before every host call the thread is `σc 0`. -/
theorem thread_in {hts : List Nat} {σc : Nat → St} {t : Nat} (h : ∀ x ∈ hts, t ≤ x) (ht : t < P) :
    thread hts σc t = σc 0 := by
  rw [thread_of_lt ht, rank_eq_zero h]

/-- **Out-pin**: after every host call the thread is `σc m`, `m` the number of calls. -/
theorem thread_out {hts : List Nat} {σc : Nat → St} {t : Nat} (h : ∀ x ∈ hts, x < t) (ht : t < P) :
    thread hts σc t = σc hts.length := by
  rw [thread_of_lt ht, rank_eq_length h]

theorem mod_of_cast {t u : Nat} (h : ((t : Nat) : F) = ((u : Nat) : F)) : t % P = u % P := by
  have := congrArg Fp.toNat h
  have e1 : (((t : Nat) : F)).toNat = t % P := Fp.toNat_ofNat t
  have e2 : (((u : Nat) : F)).toNat = u % P := Fp.toNat_ofNat u
  rw [e1, e2] at this; exact this

theorem thread_mod {hts : List Nat} {σc : Nat → St} {t u : Nat} (h : t % P = u % P) :
    thread hts σc t = thread hts σc u := by
  unfold thread; rw [h]

theorem mod_succ {t u : Nat} (h : t % P = u % P) : (t + 1) % P = (u + 1) % P := by
  rw [Nat.add_mod, h, ← Nat.add_mod]

/-! ## 2. The contract -/

/-- **A HOST row's post-condition from pre-state `s`**: the body of `RowSpecSegJ` (after its
hypotheses) with the continuing post-state's host side pinned to `b`. -/
def HostPost (X : Ctx) (b : St) (outS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat)
    (s : St) (f : Frame) (tps tpl : Nat → Nat) (t S : Nat) (live : Msg → Prop) : Prop :=
  ∃ k' pc' fee hb sb' cid',
    fee ≤ X.maxFee ∧ hb ≤ 2 ∧
    outS = stMsg (X.offOf k' + pc') (t + 1) (S + fee) hb sb' cid' ∧
    (X.R * (S + fee - sgin.1) ≤ sgin.2 →
      (hb = 0 → ∃ s', step X.cfg X.p s = .cont s' ∧
        Rel X s' (t + 1) k' pc' (S + fee) sb' cid' (stepLive live cons prod) sgout.1 sgout.2 ∧
        sideR s' = b) ∧
      (hb = 1 → ∃ sN, step X.cfg X.p s = .fin sN ∧ sN.frames = [] ∧
        X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2 ∧
        ∃ G : Msg → Prop, (∀ x, G x → x.space ≠ 0 ∧ x.space ≠ 16) ∧
        ∀ x, stepLive live cons prod x ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView 16 f.locals tpl ∨ G x) ∧
      (hb = 2 → ∃ sN e, step X.cfg X.p s = .abort sN e ∧
        X.R * (S + fee - sgout.1) + sN.gas.g = sgout.2))

/-- **A pre-state of a row**: related at the row's in-segment, entering the row's STATE message, with
the row's consumed messages live (so its stack arguments, the HOSTB bytes it reads and the REG-C
entries it reads are the state's), at a STATE time below `P`. -/
def RowPre (X : Ctx) (inS : List F) (cons : List Msg) (sgin : Nat × Nat) (E : Env) (s : St) (f : Frame)
    (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) : Prop :=
  RelW X E s f tps tpl t pc S live sgin.1 sgin.2 ∧ inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid ∧
    (∀ x ∈ cons, live x) ∧ t + 1 < P

/-- **The row is answered from host side `a` to host side `b`**: some pre-state of the row with host
side `a` satisfies the row's post-condition with out-pin `b`.  (The honest prover's witness is the
actual state before the call.) -/
def HostWit (X : Ctx) (a b : St) (inS outS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat) :
    Prop :=
  ∃ (E : Env) (w : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop),
    RowPre X inS cons sgin E w f tps tpl t pc S live ∧ sideR w = a ∧
    HostPost X b outS cons prod sgin sgout w f tps tpl t S live

/-- **The REG-C traffic of a row moves the register view from `R` to `R'`**: a bus view of the
register file `R` (`RegBusSound`, any producer times) containing the row's consumed messages
becomes, after the row's consumption/production, a bus view of `R'`.  Messages and `σ` only. -/
def RegStep (cons prod : List Msg) (R R' : Array (Nat × ByteArray)) : Prop :=
  ∀ (live : Msg → Prop) (tpr : Nat → Nat), Register.RegBusSound live R tpr → (∀ x ∈ cons, live x) →
    ∃ tpr', Register.RegBusSound (stepLive live cons prod) R' tpr'

/-- An active HOST row. -/
def HAct (tr : Trace) (pub : List F) (r : Nat) : Prop := r < tr.height 22 ∧ rowAct Host.table tr pub 22 r

/-- **`HostIf`: the bus-level host contract of a segment** (m6 README §3).  `hts` the active HOST
rows' STATE times, `σc j` the host side before the `j`-th call (by rank). -/
structure HostIf (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) (hts : List Nat)
    (σc : Nat → St) : Prop where
  nodup : hts.Nodup
  lt : ∀ t ∈ hts, t + 1 < P
  times : ∀ r, HAct tr pub r → rowNat tr 22 r 1 ∈ hts
  onto : ∀ t ∈ hts, ∃ r, HAct tr pub r ∧ rowNat tr 22 r 1 = t
  /-- the row's bus traffic is the answer from `σc j` to `σc (j + 1)` -/
  ans : ∀ r, HAct tr pub r →
    HostWit X (σc (rank hts (rowNat tr 22 r 1))) (σc (rank hts (rowNat tr 22 r 1) + 1))
      (rowInM tr pub (22, r)) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
      (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1))
  /-- the row's REG-C traffic moves `σc j`'s register file to `σc (j + 1)`'s -/
  reg : ∀ r, HAct tr pub r →
    RegStep (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
      (σc (rank hts (rowNat tr 22 r 1))).registers (σc (rank hts (rowNat tr 22 r 1) + 1)).registers
  /-- every host side's registers are below the register-size cap -/
  cap : ∀ j, ∀ e ∈ (σc j).registers.toList, e.2.size < Register.cap

/-! ## 3. The spec half (FOOT2), named -/

/-- **Two-run transfer of a row's post-condition**: from a pre-state `w` satisfying it to any other
pre-state `s` of the row with the same host side. -/
def HostTransfer (X : Ctx) (b : St) (inS outS : List F) (cons prod : List Msg) (sgin sgout : Nat × Nat) :
    Prop :=
  ∀ (E : Env) (w : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop)
    (E' : Env) (s : St) (f' : Frame) (tps' tpl' : Nat → Nat) (t' pc' S' : Nat) (live' : Msg → Prop),
    RowPre X inS cons sgin E w f tps tpl t pc S live →
    RowPre X inS cons sgin E' s f' tps' tpl' t' pc' S' live' →
    S' + X.maxFee < P → X.g0 < 2 ^ 64 → sideR w = sideR s →
    HostPost X b outS cons prod sgin sgout w f tps tpl t S live →
    HostPost X b outS cons prod sgin sgout s f' tps' tpl' t' S' live'

/-- **The register effect of a row**: from any related pre-state of the row (any gas segment) with
host side `a` and the consumed messages live, a continuing step has register file `b.registers`. -/
def HostRegFoot (X : Ctx) (a b : St) (inS : List F) (cons : List Msg) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop)
    (a' b' : Nat) (s' : St),
    RelW X E s f tps tpl t pc S live a' b' → sideR s = a → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    (∀ x ∈ cons, live x) → step X.cfg X.p s = .cont s' → s'.registers = b.registers

/-- **`HostFootprint`: the spec half of the host contract** (named; FOOT2's `callHost_two_run` and its
bridge to the row relation discharge it). -/
structure HostFootprint (X : Ctx) (tr : Trace) (pub : List F) (sg : Nat → Nat × Nat) (hts : List Nat)
    (σc : Nat → St) : Prop where
  post : ∀ r, HAct tr pub r →
    HostTransfer X (σc (rank hts (rowNat tr 22 r 1) + 1))
      (rowInM tr pub (22, r)) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
      (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1))
  regs : ∀ r, HAct tr pub r →
    HostRegFoot X (σc (rank hts (rowNat tr 22 r 1))) (σc (rank hts (rowNat tr 22 r 1) + 1))
      (rowInM tr pub (22, r)) (consCHS tr pub (22, r))

/-- **The HOST rows' flat row facts** (AIR side: halt flag, `ts + 1`, `S + fee`, producer/consumer
times, no duplicate productions), the half of `HoldRowSσ` that is not about host semantics. -/
def HostRowsFlat (X : Ctx) (tr : Trace) (pub : List F) : Prop :=
  ∀ r, HAct tr pub r →
    RowFactsFlat X (rowInM tr pub (22, r)) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))

/-! ## 4. The thread is pinned at every HOST row -/

/-- A pre-state of HOST row `r` at time `t` has `t ≡ ts_r (mod P)`. -/
theorem host_time_mod {X : Ctx} {tr : Trace} {pub : List F} {r : Nat} {E : Env} {t pc S : Nat}
    (hin : rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid) :
    t % P = rowNat tr 22 r 1 % P := by
  have e1 : lvl (rowInM tr pub (22, r)) = ((t : Nat) : F) := by rw [hin]; rfl
  rw [host_lvl] at e1
  exact (mod_of_cast e1).symm

/-- **The thread at a HOST row's pre- and post-time** is `σc j`, `σc (j + 1)`. -/
theorem thread_at_host {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {hts : List Nat}
    {σc : Nat → St} (hI : HostIf X tr pub sg hts σc) {r : Nat} (ha : HAct tr pub r) {t : Nat}
    (hmod : t % P = rowNat tr 22 r 1 % P) :
    thread hts σc t = σc (rank hts (rowNat tr 22 r 1)) ∧
      thread hts σc (t + 1) = σc (rank hts (rowNat tr 22 r 1) + 1) := by
  have hT := hI.times r ha
  obtain ⟨e0, e1⟩ := thread_host (σc := σc) hI.nodup hT (hI.lt _ hT)
  exact ⟨(thread_mod hmod).trans e0, (thread_mod (mod_succ hmod)).trans e1⟩

/-! ## 5. (c) `HoldRowSσ` and `HostRelyσ` from `HostIf` + `HostFootprint` -/

/-- **`HoldRowSσ` from the host contract.**  `HostIf` gives a witness pre-state with host side
`σc j`; `HostFootprint.post` transfers its post-condition to every pre-state on the thread. -/
theorem holdRowSσ_of_hostIf {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {hts : List Nat}
    {σc : Nat → St} (hI : HostIf X tr pub sg hts σc) (hF : HostFootprint X tr pub sg hts σc)
    (hfl : HostRowsFlat X tr pub) : HoldRowSσ X tr pub sg (thread hts σc) := by
  intro r hr ha
  have hA : HAct tr pub r := ⟨hr, ha⟩
  refine ⟨?_, hfl r hA⟩
  intro E s f tps tpl t pc S live R hJ hin hl h1 h2 h3
  obtain ⟨e0, e1⟩ := thread_at_host hI hA (host_time_mod hin)
  have hJ' : sideR s = σc (rank hts (rowNat tr 22 r 1)) := by
    have : sideR s = thread hts σc t := hJ
    rw [this, e0]
  obtain ⟨E0, w, f0, tps0, tpl0, t0, pc0, S0, live0, hpre0, hw, hpost⟩ := hI.ans r hA
  obtain ⟨k', pc', fee, hb, sb', cid', a1, a2, a3, a4⟩ :=
    hF.post r hA E0 w f0 tps0 tpl0 t0 pc0 S0 live0 E s f tps tpl t pc S live hpre0 ⟨R, hin, hl, h1⟩ h2 h3
      (hw.trans hJ'.symm) hpost
  refine ⟨k', pc', fee, hb, sb', cid', a1, a2, a3, fun hg => ?_⟩
  obtain ⟨c0, c1, c2⟩ := a4 hg
  refine ⟨fun e => ?_, c1, c2⟩
  obtain ⟨s', hs', hR, hσ⟩ := c0 e
  exact ⟨s', hs', hR, show sideR s' = thread hts σc (t + 1) by rw [hσ, e1]⟩

/-- **`HostRelyσ` from the host contract**: the register clause is `HostIf.reg` read at the thread's
register files (`sideR` carries them; `HostFootprint.regs` for the post-state), `RegWF` is
`step_regIds` + `HostIf.cap`. -/
theorem hostRelyσ_of_hostIf {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {hts : List Nat}
    {σc : Nat → St} (hI : HostIf X tr pub sg hts σc) (hF : HostFootprint X tr pub sg hts σc) :
    HostRelyσ X tr pub (thread hts σc) := by
  have key : ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 → ∃ r, ρ = (22, r) ∧ HAct tr pub r := by
    intro ρ hρ h22
    obtain ⟨t, r⟩ := ρ
    simp only at h22
    subst h22
    rcases mem_actListM2 hρ with ⟨-, hr, ha⟩ | ⟨htI, -, -⟩
    · exact ⟨r, rfl, hr, ha⟩
    · exfalso; rcases htI with ⟨_, h⟩ | h | h | h <;> simp_all
  -- the register files at a HOST row's pre-state and continuing post-state
  have regs : ∀ r, HAct tr pub r → ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat)
      (live : Msg → Prop) (a b : Nat) (s' : St), RelW X E s f tps tpl t pc S live a b →
      SigJ (thread hts σc) t s → rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
      (∀ x ∈ consCHS tr pub (22, r), live x) → step X.cfg X.p s = .cont s' →
      s.registers = (σc (rank hts (rowNat tr 22 r 1))).registers ∧
        s'.registers = (σc (rank hts (rowNat tr 22 r 1) + 1)).registers := by
    intro r hA E s f tps tpl t pc S live a b s' R hJ hin hl hs
    obtain ⟨e0, -⟩ := thread_at_host hI hA (host_time_mod hin)
    have hJ' : sideR s = σc (rank hts (rowNat tr 22 r 1)) := by
      have : sideR s = thread hts σc t := hJ
      rw [this, e0]
    refine ⟨?_, hF.regs r hA E s f tps tpl t pc S live a b s' R hJ' hin hl hs⟩
    have : (sideR s).registers = s.registers := rfl
    rw [← this, hJ']
  refine ⟨fun ρ hρ h22 => ?_, fun ρ hρ h22 => ?_⟩
  · obtain ⟨r, rfl, hA⟩ := key ρ hρ h22
    intro E s f tps tpl t pc S live a b s' R hJ hin hl hs hQ
    obtain ⟨e1, e2⟩ := regs r hA E s f tps tpl t pc S live a b s' R hJ hin hl hs
    obtain ⟨tpr, htpr⟩ := hQ
    rw [e1] at htpr
    obtain ⟨tpr', h'⟩ := hI.reg r hA live tpr htpr hl
    exact ⟨tpr', by rw [e2]; exact h'⟩
  · obtain ⟨r, rfl, hA⟩ := key ρ hρ h22
    intro E s f tps tpl t pc S live a b s' R hJ hin hl hs hw
    obtain ⟨-, e2⟩ := regs r hA E s f tps tpl t pc S live a b s' R hJ hin hl hs
    refine ⟨step_regIds hs hw.1, ?_⟩
    rw [e2]; exact hI.cap _

/-! ## 6. (a) The thread is constant between host rows: `SigKeep` -/

/-- **`SigKeep` from `HostIf`**, given that instruction rows' STATE times differ from the HOST rows'
and are below `P - 1`. -/
theorem sigKeep_of_hostIf {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {hts : List Nat}
    {σc : Nat → St} (hI : HostIf X tr pub sg hts σc)
    (hdist : ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → ∀ r, HAct tr pub r →
      lvl (rowInM tr pub ρ) ≠ lvl (rowInM tr pub (22, r)))
    (hlv : ∀ ρ ∈ actListM2 tr pub, (lvl (rowInM tr pub ρ)).toNat + 1 < P) :
    SigKeep tr pub (thread hts σc) := by
  intro ρ hρ hne
  refine thread_keep (fun hm => ?_) (hlv ρ hρ)
  obtain ⟨r, hA, he⟩ := hI.onto _ hm
  apply hdist ρ hρ hne r hA
  rw [host_lvl, show rowNat tr 22 r cTs = rowNat tr 22 r 1 from rfl, he, Fp.cast_toNat]

/-- The STATE times of a segment's rows lie in `(t_in, t_in + n]` (`seg_row_lvl` with the lower
bound). -/
theorem seg_row_lvl_range {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P) :
    ∀ ρ ∈ actListM2 tr pub, (pub.getD pubTIn 0).toNat + 1 ≤ (lvl (rowInM tr pub ρ)).toNat ∧
      (lvl (rowInM tr pub ρ)).toNat ≤ (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length := by
  intro ρ hρ
  let act := actListM2 tr pub
  let g : Nat × Nat → List F × List F := fun r => (rowInM tr pub r, rowOutM tr pub r)
  have hE1 : (act.map g).map Prod.snd = act.map (rowOutM tr pub) := by simp [g, List.map_map]
  have hE2 : (act.map g).map Prod.fst = act.map (rowInM tr pub) := by simp [g, List.map_map]
  have hstepE : ∀ e ∈ act.map g, lvl e.2 = lvl e.1 + 1 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact hts r hr
  obtain ⟨es, hes, hpath⟩ := chain (act.map g) (segM0 tr pub) (segMF tr pub) lvl
    (by rw [hE1, hE2]; exact seg_hst H) hstepE (by simp [act]; omega)
  obtain ⟨lk, -⟩ := path_levels lvl es _ _ hpath (fun e he => hstepE e (hes.subset he))
  have hl : es.length = act.length := by rw [hes.length_eq]; simp
  have hal : act.length = (actListM2 tr pub).length := rfl
  have hmem : g ρ ∈ es := hes.symm.subset (List.mem_map_of_mem hρ)
  obtain ⟨k, hk, hek⟩ := List.getElem_of_mem hmem
  have e := lk k hk
  rw [hek] at e
  have e0 : lvl (segM0 tr pub) = pub.getD pubTIn 0 + 1 := by rw [segM0_eq]; rfl
  rw [e0] at e
  have e' : lvl (rowInM tr pub ρ) = (((pub.getD pubTIn 0).toNat + 1 + k : Nat) : F) := by
    rw [show (g ρ).1 = rowInM tr pub ρ from rfl] at e
    rw [e, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_add, Fp.cast_toNat]; rfl
  rw [e', Fp.toNat_cast_of_lt (by omega)]
  omega

/-- **`SigKeep` from `HostIf` on a segment trace**: the distinct-times and size side conditions from
the STATE chain (`seg_lvl_inj`, `seg_row_lvl_range`). -/
theorem sigKeep_of_hostIf_seg {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P)
    {sg : Nat → Nat × Nat} {hts' : List Nat} {σc : Nat → St} (hI : HostIf X tr pub sg hts' σc) :
    SigKeep tr pub (thread hts' σc) := by
  refine sigKeep_of_hostIf hI (fun ρ hρ hne r hA he => hne ?_) (fun ρ hρ => ?_)
  · have := seg_lvl_inj H hts hsz ρ hρ _ (host_mem_actListM2 hA.1 hA.2) he
    rw [this]
  · have := (seg_row_lvl_range H hts hsz ρ hρ).2
    omega

/-- The host times of a segment lie in `(t_in, t_in + n]`. -/
theorem hostTimes_range {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P)
    {sg : Nat → Nat × Nat} {hts' : List Nat} {σc : Nat → St} (hI : HostIf X tr pub sg hts' σc) :
    ∀ x ∈ hts', (pub.getD pubTIn 0).toNat + 1 ≤ x ∧ x ≤ (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length := by
  intro x hx
  obtain ⟨r, hA, rfl⟩ := hI.onto x hx
  have h := seg_row_lvl_range H hts hsz _ (host_mem_actListM2 hA.1 hA.2)
  have e : (lvl (rowInM tr pub (22, r))).toNat = rowNat tr 22 r 1 := by
    rw [host_lvl]; exact Fp.toNat_cast_of_lt (rowNat_lt tr 22 r 1)
  rw [e] at h
  exact h

/-! ## 7. (b) The bus messages of a HOST row are the thread's run -/

/-- **Host-bus messages ↔ σ entries.**  From any pre-state of HOST row `r` on the thread (host side
`σc j`, `j` the call's rank), whose gas fits the row's in-segment: the row's STATE output is
`(·, t + 1, S + fee, hb, ·, ·)`; when it continues (`hb = 0`) the spec step continues to a state
`s'` with host side `σc (j + 1)` (registers included), gas register on the out-segment (`g_after`),
**every message the row produced** (result word, HOSTB bytes written, REG-C entries written, gas
register) in `s'`'s view, every message it consumed in `s`'s view, and the space-6 part of the
post-view a bus view of `σc (j + 1)`'s register file. -/
theorem host_msgs_of_thread {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {hts : List Nat}
    {σc : Nat → St} (hI : HostIf X tr pub sg hts σc) (hF : HostFootprint X tr pub sg hts σc)
    (hfl : HostRowsFlat X tr pub) {r : Nat} (hA : HAct tr pub r)
    {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat} {live : Msg → Prop}
    (R : RelW X E s f tps tpl t pc S live (sg (rowNat tr 22 r 1)).1 (sg (rowNat tr 22 r 1)).2)
    (hσ : sideR s = σc (rank hts (rowNat tr 22 r 1)))
    (hin : rowInM tr pub (22, r) = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid)
    (hl : ∀ x ∈ consCHS tr pub (22, r), live x)
    (h1 : t + 1 < P) (h2 : S + X.maxFee < P) (h3 : X.g0 < 2 ^ 64)
    (hreg : RegC live s) :
    (∀ x ∈ consCHS tr pub (22, r), x ∈ stackView s.stack tps ∨ x ∈ localView E.lsp f.locals tpl ∨ E.live x) ∧
    ∃ k' pc' fee hb sb' cid', fee ≤ X.maxFee ∧
      rowOutM tr pub (22, r) = stMsg (X.offOf k' + pc') (t + 1) (S + fee) hb sb' cid' ∧
      (X.R * (S + fee - (sg (rowNat tr 22 r 1)).1) ≤ (sg (rowNat tr 22 r 1)).2 → hb = 0 →
        ∃ s', step X.cfg X.p s = .cont s' ∧ sideR s' = σc (rank hts (rowNat tr 22 r 1) + 1) ∧
          ∃ (E' : Env) (f' : Frame) (tps' tpl' : Nat → Nat),
            RelW X E' s' f' tps' tpl' (t + 1) pc' (S + fee) (stepLive live (consCHS tr pub (22, r)) (prodCHS tr pub (22, r)))
              (sg (rowNat tr 22 r 1 + 1)).1 (sg (rowNat tr 22 r 1 + 1)).2 ∧
            X.R * (S + fee - (sg (rowNat tr 22 r 1 + 1)).1) + s'.gas.g = (sg (rowNat tr 22 r 1 + 1)).2 ∧
            (∀ x ∈ prodCHS tr pub (22, r),
              x ∈ stackView s'.stack tps' ∨ x ∈ localView E'.lsp f'.locals tpl' ∨ E'.live x) ∧
            RegC (stepLive live (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))) s') := by
  have hmod := host_time_mod hin
  obtain ⟨e0, e1⟩ := thread_at_host hI hA hmod
  have hJ : SigJ (thread hts σc) t s := by show sideR s = _; rw [hσ, e0]
  refine ⟨fun x hx => (R.live x).mp (hl x hx), ?_⟩
  obtain ⟨k', pc', fee, hb, sb', cid', a1, -, a3, a4⟩ :=
    (holdRowSσ_of_hostIf hI hF hfl r hA.1 hA.2).spec E s f tps tpl t pc S live R hJ hin hl h1 h2 h3
  refine ⟨k', pc', fee, hb, sb', cid', a1, a3, fun hg h0 => ?_⟩
  obtain ⟨s', hs', ⟨E', f', tps', tpl', -, -, -, R'⟩, hJ'⟩ := (a4 hg).1 h0
  have hσ' : sideR s' = σc (rank hts (rowNat tr 22 r 1) + 1) := by
    have : sideR s' = thread hts σc (t + 1) := hJ'
    rw [this, e1]
  have hRC := (hostRelyσ_of_hostIf hI hF).reg (22, r) (host_mem_actListM2 hA.1 hA.2) rfl E s f tps tpl t pc S live
    _ _ s' R hJ hin hl hs' hreg
  refine ⟨s', hs', hσ', E', f', tps', tpl', R', ?_, fun x hx => (R'.live x).mp (Or.inr hx), hRC⟩
  · exact R'.gas

/-! ## 8. Segment soundness from the host contract -/

/-- **`seg_sound_hostIf`: `seg_sound_σ` with its σ-premises discharged by the host contract.**
`SigKeep`, `HoldRowSσ`, `HostRelyσ` and the in-pin come from `HostIf` (+ `HostFootprint`, the HOST
rows' flat facts); the state enters at host side `σc 0` and leaves at `σc m`, `m` the number of
host calls of the segment. -/
theorem seg_sound_hostIf (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {hts : List Nat} {σc : Nat → St} (hI : HostIf X.toCtx tr pub sg hts σc)
    (hF : HostFootprint X.toCtx tr pub sg hts σc) (hfl : HostRowsFlat X.toCtx tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    (hT : TombDead tr pub (finS tr pub))
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) (hσ0 : sideR s0 = σc 0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ sideR sN = σc hts.length := by
  have hP := P_val
  have hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P := by omega
  have hInstr : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have htsO : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1 := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · obtain ⟨t, r⟩ := ρ
      simp only at h22
      subst h22
      rcases mem_actListM2 hρ with ⟨-, hr, ha⟩ | ⟨htI, -, -⟩
      · exact (hfl r ⟨hr, ha⟩).tsOut
      · exfalso; rcases htI with ⟨_, h⟩ | h | h | h <;> simp_all
    · exact (RowFactsSeg.toFlat (rowFactsSegMap_instr X.toCtx hInstr hkeep hρ h22)).tsOut
  have hrange := hostTimes_range H htsO hsz hI
  have hin : sideR s0 = thread hts σc ((pub.getD pubTIn 0).toNat + 1) := by
    rw [hσ0, thread_in (fun x hx => (hrange x hx).1) (by omega)]
  obtain ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, hσN⟩ :=
    seg_sound_σ X H hC hl hcode hfunc hb hg hkeep (sigKeep_of_hostIf_seg H htsO hsz hI)
      (holdRowSσ_of_hostIf hI hF hfl) (hostRelyσ_of_hostIf hI hF) hst0 hlen htin hfeeN hstepgas hg64 hinit hT
      h0 hw0 hin
  refine ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, ?_⟩
  rw [hσN, thread_out (fun x hx => by have := (hrange x hx).2; omega) (by omega)]

#print axioms thread_keep
#print axioms thread_host
#print axioms holdRowSσ_of_hostIf
#print axioms hostRelyσ_of_hostIf
#print axioms sigKeep_of_hostIf
#print axioms sigKeep_of_hostIf_seg
#print axioms hostTimes_range
#print axioms host_msgs_of_thread
#print axioms seg_sound_hostIf

end HostIf
end WasmBase
