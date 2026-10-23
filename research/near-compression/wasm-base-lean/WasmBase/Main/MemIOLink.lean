import WasmBase.Main.MemIOBus
import WasmBase.Main.HostRel
import WasmBase.Main.RegSend
/-!
# WasmBase.Main.MemIOLink — the `(ptr, len)` → linear-memory link, closed

`Main/MemIOBus` proved the *bus* half of the HOSTB memory link: a request byte's space-3 recv/send
pair is folded onto its host call and the CH decomposition absorbs the re-timing.  This file closes
the two obligations `results/pq-host-memio/RESULTS.md` §3.5 named as open:

* **`hostb_mem_distinct`** — `mtp ≠ ts` as a *derived* fact about the trace.  The AIR's `timeChk`
  pair (`r16 (ts − mtp − 1 − 2^16·hp)`, `r16 (4·hp)`) counted `memCnt = 1` gives
  `mtp + 1 + n ≡ ts (mod P)` with `n < 2^30 + 2^16`; since `mtp, ts < P` and `1 + n < P`, the only
  possibilities are `mtp + 1 + n = ts` or `mtp + 1 + n = ts + P`, and both contradict `mtp = ts`.
  So the recv message `encB a bv mtp` and the send `encB a bv ts` **differ**, i.e. the pair is not
  the vacuous same-time self-cancellation (`MemIO.ch_pair_vacuous`) — this is the non-vacuity the
  AIR's space-3 link needs, and it is now a theorem about `Holds`, not a generator assertion.
* **`hostb_mem_consumed`** — the memory-content half: given that the request byte's consumed message
  is live in the row's pre-heap, `StepMem.heap_read` gives `memory[ptr + pos] = byte` and the
  address in bounds.  The liveness itself is the *interface* obligation the CH decomposition
  supplies for a row's consumed messages, exactly as `RowFactsSeg` supplies `hin` for action rows.
* **`host_step_rely_buf`** / **`host_rel_restart_buf`** — the wiring of `MemIO.heap_retime` into
  `HostStepRely.heap`: a request read's post-heap obligation is *discharged* rather than assumed.

The remaining statement-level bound is `MemIO.BufOK` (`ptr + len ≤ memBytes`), as before.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The base tables' row constraints on a host trace

Tables 0–21 of `wasmBaseHostAir` are `wasmBaseAir`'s by index, so `Holds` of the host AIR gives the
base AIR's row constraints verbatim.  This is the host-AIR counterpart of `Main/RegSend.reg_base_constr`
(the REG lane needed it to reuse the constraint-only chip lemmas). -/

theorem host_base_constr {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) :
    ∀ t (ht : t < (wasmBaseAir nloc ngl).tables.length) r, r < tr.height t →
      ∀ e ∈ ((wasmBaseAir nloc ngl).tables[t]'ht).constraints,
        e.eval (natRow (rowNat tr t r) (tr.row pub t r)) = 0 := by
  intro t ht r hr e he
  have h22 : t < 22 := by simpa [air_len] using ht
  have he' : e ∈ ((wasmBaseHostAir nloc ngl).tables[t]'(by rw [host_air_len]; omega)).constraints := by
    rw [host_air_get nloc ngl t h22]; exact he
  exact table_constr H (by rw [host_air_len]; omega) hr e he'

/-! ## The bits of a `HOSTB` row -/

/-- A `bool`-constrained column of `HOSTB` is a bit on a host trace's HOSTB row. -/
theorem hostb_bit {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 25)
    {c : Nat} (hc : Chips.bool (v c) ∈ HostB.table.constraints) :
    rowNat tr 25 r c = 0 ∨ rowNat tr 25 r c = 1 := by
  have ht : 25 < (wasmBaseHostAir nloc ngl).tables.length := by simp [wasmBaseHostAir, air_len]
  have hb := table_constr H ht hr (Chips.bool (v c)) hc
  simp only [Chips.bool, Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col,
    Expr.eval_ofNat', natRow] at hb
  exact bool_nat (rowNat_lt tr 25 r c) hb

/-- The un-folded R16 count `act · (1 − reg)` of a HOSTB row is ≤ 1. -/
theorem hostb_act_one_minus_reg_le {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 25) :
    ((v HostB.act * (1 - v HostB.reg)).eval (tr.row pub 25 r)).toNat ≤ 1 := by
  have hact := hostb_bit (H := H) hr (c := HostB.act)
    (by simp [HostB.table, HostB.constraints, HostB.cAct])
  have hreg := hostb_bit (H := H) hr (c := HostB.reg)
    (by simp [HostB.table, HostB.constraints, HostB.cReg])
  have e : ((v HostB.act * (1 - v HostB.reg)).eval (tr.row pub 25 r)).toNat =
      (rowNat tr 25 r HostB.act * (1 - rowNat tr 25 r HostB.reg)) := by
    simp only [Chips.v, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', Expr.eval_col, Trace.row]
    rw [cell_cast tr 25 r HostB.act, cell_cast tr 25 r HostB.reg]
    rcases hact with h | h <;> rcases hreg with h' | h' <;> rw [h, h'] <;> decide
  rw [e]
  rcases hact with h | h <;> rcases hreg with h' | h' <;> rw [h, h'] <;> decide


/-! ## The R16 send bound for `wasmBaseHostAir`

This is the host-AIR counterpart of `Main/RegSend.reg_hsend_r16`: the *per-bus* send bound at
`busR16`, which is what `Bus.lookup_sound` actually needs.  The unrestricted statement is false —
`HOSTO`'s free column `mult` counts its `HOSTR` send (`hosto_no_count_bound`). -/

/-- **Every R16 send of the base tables on a host trace has count ≤ 1.** -/
theorem host_send_base {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr)
    {t r : Nat} (ht : t < 22) (hr : r < tr.height t) {i : Inter}
    (hi : i ∈ ((wasmBaseAir nloc ngl).tables[t]'(by simp [air_len]; exact ht)).inters)
    (hs : i.send = true) :
    (i.count.eval (tr.row pub t r)).toNat ≤ 1 :=
  occ_bits_of hpub CF.counts (host_base_constr H) _
    (mem_occs.mpr ⟨t, by simp [air_len]; exact ht, r, hr, i, hi, rfl⟩) (Or.inl hs)

/-- **The R16 send-side bound for `wasmBaseHostAir`.**  This is the hypothesis
`Main/HostLinks.host_r16_sound` consumes, proved from `Holds` alone (given the public-input layout
and the base chips' row facts). -/
theorem host_hsend_r16 {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr) :
    ∀ o ∈ occs (wasmBaseHostAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1 := by
  intro o ho hb hs
  rcases occ_table_host ho with ⟨t, ht, r, hr, i, hi, rfl⟩ | ⟨r, hr, i, hi, rfl⟩ |
    ⟨r, hr, i, hi, rfl⟩ | ⟨r, hr, i, hi, rfl⟩ | ⟨r, hr, i, hi, rfl⟩
  · exact host_send_base H hpub CF ht hr hi hs
  · -- HOST (22): the R16 count is `act` or some `pf j`
    simp only at hb hs
    rcases host_r16_cases hi hb with h | ⟨j, hj, h⟩
    · rw [h]; rw [col_eval]; exact host_act_bit H hr
    · rw [h]; rw [col_eval]; exact host_pf_le H hr hj
  · -- HOSTO (23): no R16 send
    simp only at hb hs
    exact absurd (no_r16_send hosto_no_r16 hi hb hs) not_false
  · -- HOSTT (24): no R16 send
    simp only at hb hs
    exact absurd (no_r16_send hostT_no_r16 hi hb hs) not_false
  · -- HOSTB (25): `memCnt` or its un-folded `act·(1−reg)`
    simp only at hb hs
    rcases hostb_r16_cases hi hb with h | h
    · rw [h]; exact hostb_memCnt_bit H hr
    · rw [h]; exact hostb_act_one_minus_reg_le H hr

/-! ## The R16 answer for a host trace, per bus -/

/-- The RANGE16-answer characterisation for a host trace: an R16 **receive** is a single value
`< 2^16`.  Mirrors `Main/RegWalk.reg_r16_recv`. -/
theorem host_r16_recv {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) :
    ∀ o ∈ occs (wasmBaseHostAir nloc ngl) tr pub, o.1 = busR16 → o.2.1 = false →
      o.2.2.2 ≠ 0 → ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 := by
  intro o ho hb hs hc
  obtain ⟨t, ht', r', hr', i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb hs hc
  -- every table other than RANGE16 sends R16, so a receive must be RANGE16's
  have hT : (wasmBaseHostAir nloc ngl).tables[t]'ht' = Range16.table := by
    rcases Classical.em ((wasmBaseHostAir nloc ngl).tables[t]'ht' = Range16.table) with he | hne
    · exact he
    · exact absurd (host_recv_only_range16 nloc ngl _ (List.getElem_mem _) hne i hi hb) (by simp [hs])
  obtain ⟨hh, hv⟩ := range16_values H ht' hT
  rw [hT] at hi
  simp only [Range16.table, List.mem_cons, List.mem_nil_iff, or_false] at hi
  subst hi
  refine ⟨((r' : Nat) : F), ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [row_eq_natRow]
    simp only [v, Expr.eval_col, natRow, Range16.val]
    have e : rowNat tr t r' Range16.val = r' := hv r' hr'
    simp only [Range16.val] at e ⊢
    simpa using congrArg (fun n => ((n : Nat) : F)) e
  · rw [Fp.toNat_cast_of_lt (by rw [P_val]; omega)]; omega

/-- **R16 soundness on a host trace, per bus.**  `lookup_sound` at `busR16` with the send bound
`host_hsend_r16` and the receive characterisation `host_r16_recv`. -/
theorem host_r16_sound_at {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr)
    {o : Occ} (ho : o ∈ occs (wasmBaseHostAir nloc ngl) tr pub) (hb : o.1 = busR16)
    (hs : o.2.1 = true) (hc : o.2.2.2 = 1) :
    ∃ x : F, o.2.2.1 = [x] ∧ x.toNat < 65536 :=
  lookup_sound H busR16 (fun m => ∃ x : F, m = [x] ∧ x.toNat < 65536)
    (host_r16_recv H) (host_hsend_r16 H hpub CF) ho hb hs hc

/-! ## The `timeChk` pair of a HOSTB row

The AIR's `timeChk` gadget on a request byte is two `R16` queries counted `memCnt`:
`r16 (ts − mtp − 1 − 2^16·hp)` and `r16 (4·hp)`.  With `memCnt = 1` both are count-1 queries, so
`host_r16_sound_at` turns them into 16-bit values, and the two equations combine to
`mtp + 1 + n ≡ ts (mod P)` with `n < 2^30 + 2^16` — the host-AIR counterpart of
`Main/Rows.time_chk`. -/

theorem host_time_chk {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr)
    {ts tp hi : F}
    (h1 : (busR16, true, [ts - tp - ((1 : Nat) : F) - ((65536 : Nat) : F) * hi], 1) ∈
      occs (wasmBaseHostAir nloc ngl) tr pub)
    (h2 : (busR16, true, [((4 : Nat) : F) * hi], 1) ∈ occs (wasmBaseHostAir nloc ngl) tr pub) :
    ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((tp.toNat + 1 + n : Nat) : F) = ts := by
  obtain ⟨x, hx, hxl⟩ := host_r16_sound_at H hpub CF h1 rfl rfl rfl
  obtain ⟨y, hy, hyl⟩ := host_r16_sound_at H hpub CF h2 rfl rfl rfl
  simp only [List.cons.injEq, and_true] at hx hy
  refine ⟨x.toNat + 16384 * y.toNat, by omega, ?_⟩
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat]
  rw [← hx, ← hy]
  have : ((65536 : Nat) : F) = ((16384 : Nat) : F) * ((4 : Nat) : F) := by
    rw [← Lean.Grind.Semiring.natCast_mul]
  rw [this]; grind

/-! ## `mtp ≠ ts` — the space-3 pair is not a same-time self-cancellation -/

/-- The row's two `timeChk` queries, as occurrences of the host AIR. -/
theorem hostb_timechk_occ {nloc ngl : Nat} {pub : List F} {tr : Trace} {r : Nat}
    (hr : r < tr.height 25)
    (hm1 : (HostB.memCnt.eval (tr.row pub 25 r)).toNat = 1) :
    (busR16, true, [((rowNat tr 25 r HostB.ts : Nat) : F) - ((rowNat tr 25 r HostB.mtp : Nat) : F) -
        ((1 : Nat) : F) - ((65536 : Nat) : F) * ((rowNat tr 25 r HostB.hp : Nat) : F)], 1) ∈
      occs (wasmBaseHostAir nloc ngl) tr pub ∧
    (busR16, true, [((4 : Nat) : F) * ((rowNat tr 25 r HostB.hp : Nat) : F)], 1) ∈
      occs (wasmBaseHostAir nloc ngl) tr pub := by
  have hmem1 : r16 (v HostB.ts - v HostB.mtp - 1 - B16 * v HostB.hp) HostB.memCnt ∈ HostB.table.inters :=
    List.mem_of_getElem? (i := 7) (by decide)
  have hmem2 : r16 (4 * v HostB.hp) HostB.memCnt ∈ HostB.table.inters :=
    List.mem_of_getElem? (i := 8) (by decide)
  have eTs : Expr.eval (tr.row pub 25 r) (v HostB.ts) = ((rowNat tr 25 r HostB.ts : Nat) : F) := by
    simp only [Chips.v, Expr.eval_col, Trace.row, cell_cast]
  have eMtp : Expr.eval (tr.row pub 25 r) (v HostB.mtp) = ((rowNat tr 25 r HostB.mtp : Nat) : F) := by
    simp only [Chips.v, Expr.eval_col, Trace.row, cell_cast]
  have eHp : Expr.eval (tr.row pub 25 r) (v HostB.hp) = ((rowNat tr 25 r HostB.hp : Nat) : F) := by
    simp only [Chips.v, Expr.eval_col, Trace.row, cell_cast]
  constructor
  · refine mem_occs.mpr ⟨25, by rw [host_air_len]; decide, r, hr,
      r16 (v HostB.ts - v HostB.mtp - 1 - B16 * v HostB.hp) HostB.memCnt, hmem1, ?_⟩
    simp only [r16, List.map_cons, List.map_nil, B16, eTs, eMtp, eHp, hm1, Expr.eval_sub',
      Expr.eval_mul', Expr.eval_ofNat']
  · refine mem_occs.mpr ⟨25, by rw [host_air_len]; decide, r, hr,
      r16 (4 * v HostB.hp) HostB.memCnt, hmem2, ?_⟩
    simp only [r16, List.map_cons, List.map_nil, eHp, hm1, Expr.eval_mul', Expr.eval_ofNat']

/-- **`mtp ≠ ts` on an active `HOSTB` row.**  The two `timeChk` queries give
`mtp + 1 + n ≡ ts (mod P)` with `n < 2^30 + 2^16`; since `mtp, ts < P` and `1 + n < P`, the only
possibilities are `mtp + 1 + n = ts` or `mtp + 1 + n = ts + P`, and both contradict `mtp = ts`.
So the recv message `encB a bv mtp` and the send `encB a bv ts` **differ**: the AIR's space-3 pair
is a genuine re-timing and not the vacuous same-time cancellation of `MemIO.ch_pair_vacuous`. -/
theorem hostb_mem_distinct {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace} {r : Nat}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr)
    (hr : r < tr.height 25) (hact : rowAct HostB.table tr pub 25 r) :
    rowNat tr 25 r HostB.mtp ≠ rowNat tr 25 r HostB.ts := by
  have hm1 : (HostB.memCnt.eval (tr.row pub 25 r)).toNat = 1 := hostb_rowAct_iff.mp hact
  obtain ⟨h1, h2⟩ := hostb_timechk_occ (nloc := nloc) (ngl := ngl) hr hm1
  obtain ⟨n, hn, heq⟩ := host_time_chk H hpub CF h1 h2
  intro heqts
  have hm : rowNat tr 25 r HostB.mtp < P := rowNat_lt tr 25 r HostB.mtp
  have hts : rowNat tr 25 r HostB.ts < P := rowNat_lt tr 25 r HostB.ts
  have hcast : ((rowNat tr 25 r HostB.mtp + 1 + n : Nat) : F) = ((rowNat tr 25 r HostB.ts : Nat) : F) := by
    simpa [Fp.toNat_cast_of_lt hm] using heq
  rw [heqts] at hcast
  have h1n : 1 + n < P := by have := P_val; omega
  have hmod : (rowNat tr 25 r HostB.ts + 1 + n) % P = rowNat tr 25 r HostB.ts := by
    have := congrArg Fp.toNat hcast
    rwa [Fp.toNat_cast, Fp.toNat_cast_of_lt hts] at this
  by_cases hlt : rowNat tr 25 r HostB.ts + 1 + n < P
  · rw [Nat.mod_eq_of_lt hlt] at hmod; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega


/-! ## The memory-content half

`hostb_mem_distinct` says the recv/send pair is a genuine re-timing.  The *content* claim is
`hostb_mem_consumed`: once the row's consumed message is known to be live in the pre-heap — the
interface obligation the CH decomposition carries for a row's consumed messages, exactly as
`RowFactsSeg` carries `hin` for action rows — `StepMem.heap_read` gives the memory byte and its
bound. -/

/-- **A request byte's consumed message is the live memory byte.**  `hostbMemRecv tr r` is
definitionally `encB (ptr + pos) byte mtp`, so `StepMem.heap_read` applies directly: the byte read
out of memory is the row's committed `byte`, and the address is in bounds. -/
theorem hostb_mem_consumed {E : Env} {s : St} {t : Nat} {tr : Trace} {r : Nat}
    (H : HeapOK E s t) (hl : E.live (hostbMemRecv tr r)) :
    (readByte s (hostbAddr tr r)).toNat = rowNat tr 25 r HostB.bv ∧
      hostbAddr tr r < memBytes s :=
  heap_read H hl

/-- **The buffer byte is inside memory.**  With the statement-level bound `BufOK` (`ptr + len ≤
memBytes`) and `pos < len` (`reg_pos_lt_len`'s HOSTB counterpart), the re-timed address is in bounds.
This is the form the `(ptr, len)` → memory link consumes. -/
theorem hostb_addr_lt {s : St} {tr : Trace} {r len : Nat}
    (hb : BufOK s (rowNat tr 25 r HostB.ptrLo + 65536 * rowNat tr 25 r HostB.ptrHi) len)
    (hp : rowNat tr 25 r HostB.pos < len) :
    hostbAddr tr r < memBytes s := by
  unfold BufOK at hb
  unfold hostbAddr
  omega

/-! ## Wiring `heap_retime` into `HostStepRely.heap`

`Main/HostRel.host_rel_restart` takes `HostStepRely` as its rely condition, whose `heap` field is
`HeapOK E os (t + 1)` — the post-call heap.  For a request read that obligation is not an
assumption: `MemIO.heap_retime` produces it from the pre-heap plus "the bytes are live at their old
times".  The two theorems below are that wiring: `host_step_rely_buf` builds the `HostStepRely` with
`heap := heap_retime …`, and `host_rel_restart_buf` is `host_rel_restart` applied to it. -/

/-- The environment after re-timing the bytes `[ea, ea + w)` to time `t`. -/
def retimedEnv (E : Env) (ea w t : Nat) (bv tb : Nat → Nat) : Env :=
  { E with live := (stepLive E.live ((List.range w).map fun i => encB (ea + i) (bv i) (tb i))
      ((List.range w).map fun i => encB (ea + i) (bv i) t)) }

/-- Re-timing leaves non-memory messages alone: if every consumed and produced message has space 3,
then `stepLive` agrees with `live` on every message outside space 3. -/
theorem stepLive_space {live : Msg → Prop} {cons prod : List Msg}
    (hcons : ∀ x ∈ cons, x.space = 3) (hprod : ∀ x ∈ prod, x.space = 3)
    {x : Msg} (hx : x.space = 4 ∨ x.space = 5 ∨ 16 ≤ x.space) :
    stepLive live cons prod x ↔ live x := by
  unfold stepLive
  constructor
  · rintro (⟨h, _⟩ | h)
    · exact h
    · exact absurd (hprod x h) (by omega)
  · intro h
    refine Or.inl ⟨h, ?_⟩
    intro hc
    exact absurd (hcons x hc) (by omega)

/-- **The `HostStepRely` of a request read**, with its heap field discharged by `heap_retime`.

Every field except `heap` and `calls` is supplied by the interface (the same obligations a host call
carries); `heap` comes from `heap_retime` + `HeapOK.mono`, and `calls` from `CallsOK.mono` since the
re-timed messages are all space 3 and the call chain's messages are not. -/
theorem host_step_rely_buf {X : Ctx} {E : Env} {s os : St} {sb h' t : Nat} {ea w : Nat}
    {tpsN : Nat → Nat} (bv tb : Nat → Nat)
    (H : HeapOK E s t) (hlive : ∀ i, i < w → E.live (encB (ea + i) (bv i) (tb i)))
    (hpg : os.pages = s.pages) (hgl : os.globals = s.globals)
    (hsb : sb ≤ os.stack.size) (hheight : os.stack.size - sb = h')
    (hnum : ∀ i, i < os.stack.size → isNum (os.stack[i]?.getD default))
    (htps : ∀ i, i < os.stack.size → tpsN i < t + 1)
    (hcalls : CallsOK X E s t) (hrem : os.stackRem = s.stackRem) :
    HostStepRely X (retimedEnv E ea w t bv tb) os sb h' tpsN (t + 1) where
  sbLe := hsb
  height := hheight
  numS := hnum
  tpsLt := htps
  heap := HeapOK.mono (heap_retime H bv tb hlive) hpg hgl (Nat.le_refl _)
  calls := by
    refine CallsOK.mono hcalls (Nat.le_succ t) rfl rfl rfl rfl ?_ hrem
    intro x hx
    refine stepLive_space ?_ ?_ hx
    · rintro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨i, -, rfl⟩ := hy
      rfl
    · rintro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨i, -, rfl⟩ := hy
      rfl


/-! ## The end-to-end restart for a request read

`Main/HostRel.host_rel_restart` produces the full `RelW` at the restarted segment from a
`HostStepRely`.  Its `heap` field is the one obligation a request read discharges structurally, so
this is the composed form: the pre-heap plus the read facts replace `HostStepRely.heap`, and
everything else is carried exactly as in `host_rel_restart`.

Note the environment: the read *re-times* the bytes it touches, so the post-state's live set is
`retimedEnv`'s — the pre-state's `live` cannot be reused.  That is why this is a separate theorem
and not a direct application of `host_rel_restart` (which uses one `Env` on both sides). -/
theorem host_rel_restart_buf {X : Ctx} {E : Env} {s os : St} {f : Frame} {tps : Nat → Nat}
    {tpl tps' : Nat → Nat}
    {t pc S : Nat} {live live' : Msg → Prop} {S_seg segb fee segb' : Nat} {ls : List Label}
    {ea w : Nat} (bv tb : Nat → Nat)
    (R : RelW X E s f tps tpl t pc S live S_seg segb)
    (H : HeapOK E s t) (hliveM : ∀ i, i < w → E.live (encB (ea + i) (bv i) (tb i)))
    (hpg : os.pages = s.pages) (hgl : os.globals = s.globals)
    (hof : os.frames = { f with pc := f.pc + 1 } :: E.rest)
    (hsbLe : E.sb ≤ os.stack.size) (hheight : os.stack.size - E.sb = (X.ckOf E.k).heights.getD (f.pc + 1) 0)
    (hnum : ∀ i, i < os.stack.size → isNum (os.stack[i]?.getD default))
    (htps : ∀ i, i < os.stack.size → tps' i < t + 1)
    (hrem : os.stackRem = s.stackRem)
    (hlive' : ∀ x, live' x ↔
      x ∈ stackView os.stack tps' ∨ x ∈ localView E.lsp f.locals tpl ∨
        (retimedEnv E ea w t bv tb).live x)
    (hpcLt : f.pc + 1 < (X.pfOf E.k).code.size)
    (hlab' : (X.ckOf E.k).labels[f.pc + 1]? = (X.ckOf E.k).labels[pc]?)
    (hh' : (X.ckOf E.k).heights[f.pc + 1]? = some ((X.ckOf E.k).heights.getD (f.pc + 1) 0))
    (hgas : os.gas.g = segb') (hgA : segb' < 2 ^ 64) :
    RelW X (retimedEnv E ea w t bv tb) os { f with pc := f.pc + 1 } tps' tpl (t + 1) (f.pc + 1)
      (S + fee) live' (S + fee) segb' where
  frames := hof
  kLt := R.kLt
  fn := R.fn
  pcEq := rfl
  pcLt := hpcLt
  labels := by
    obtain ⟨ls0, hl0, hls0⟩ := R.labels
    exact ⟨ls0, by show (X.ckOf E.k).labels[f.pc + 1]? = some ls0; rw [hlab', hl0], hls0⟩
  base := R.base
  sbLe := hsbLe
  height := by show (X.ckOf E.k).heights[f.pc + 1]? = some (os.stack.size - E.sb); rw [hh', hheight]
  nloc := by rw [R.pcEq]; exact R.nloc
  gas := by show X.R * (S + fee - (S + fee)) + os.gas.g = segb'; rw [hgas]; simp
  segLt := Nat.le_refl _
  segbLt := hgA
  numS := hnum
  numL := R.numL
  tpsLt := htps
  tplLt := fun j hj => by have := R.tplLt j hj; omega
  envSep := by
    intro x hx
    unfold retimedEnv at hx
    simp only [stepLive] at hx
    rcases hx with ⟨hl, -⟩ | hmem
    · have := R.envSep x hl
      exact ⟨this.1, this.2⟩
    · -- a produced byte: space 3, so neither 0 nor `16 + cid`
      simp only [List.mem_map, List.mem_range] at hmem
      obtain ⟨i, hi, rfl⟩ := hmem
      refine ⟨by simp [encB], ?_⟩
      intro hsp
      simp only [encB, Env.lsp, retimedEnv] at hsp
      have hc : E.cid < 2 ^ 28 := R.cidLt
      omega
  entry := by
    intro hc
    have := R.entry hc
    exact ⟨this.1, this.2⟩
  sbLt := R.sbLt
  cidLt := R.cidLt
  heap := HeapOK.mono (heap_retime H bv tb hliveM) hpg hgl (Nat.le_refl _)
  calls := by
    refine CallsOK.mono R.calls (Nat.le_succ t) rfl rfl rfl rfl ?_ hrem
    intro x hx
    exact stepLive_space (fun y hy => by
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨i, -, rfl⟩ := hy
      rfl) (fun y hy => by
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨i, -, rfl⟩ := hy
      rfl) hx
  live := hlive'

end WasmBase
