import WasmBase.Main.Exec
import WasmBase.Main.HostLinks
import WasmBase.Main.RowHostSpec
/-!
# WasmBase.Main.ExecHost — the bus decomposition for `wasmBaseHostAir` (piece 2)

`wasmBaseHostAir nloc ngl = wasmBaseAir nloc ngl ++ [HOST, HOSTO, HOSTT]`, so every bus of a host
trace is the base trace's messages **plus** the messages of tables 22/23/24.  This file proves that
decomposition for the buses the execution theorem reads:

* `host_msgs_air`: every bus `b` splits as `msgs wasmBaseAir ++ (HOST ++ HOSTO ++ HOSTT)`;
* `host_occs_air`: the same for the occurrence list;
* `msgs_state_host` / `msgs_ch_host`: the STATE and CH decompositions in the shape
  `Exec.msgs_state` / `Exec.msgs_ch` have for the base AIR.  The HOST row's STATE interactions are
  the standard `pc`/`pc + 1` pair (`host_part_state_T` / `host_part_state_F`), and its CH messages
  are the row's `rowMsgs … busStk` (`host_part_ch_recv` / `host_part_ch_send` decode them to
  `rowCons`/`rowProd`);
* `host_part_nil_env`: the response oracle (23) and the cached host table (24) carry no STATE or CH
  interaction, so they contribute nothing to those two buses;
* `host_arg_stack` / `host_word_stack`: the two halves of piece 1 (live arguments, response word)
  restated at the trace/`RelW` boundary.

## The constraint gap is closed (HOST row gating)

The HOST row's CH receives are counted with `pf j`, not `act · pf j` (`host_inters_stk`), and the
send with `nres`.  Without an `act` link an **inactive** HOST row (`act = 0`, `pf 0 = 1`) would
still emit count-1 CH receives, so the base `ChipFacts.inactive` premise would fail for table 22.

`Host.constraints` now carries the gating (`Host.cActPf j`, `Host.cActNres`):

```
(1 − act) · pf j = 0   (j = 0, 1)        (1 − act) · nres = 0
```

so an inactive row emits no CH message at all, and `ChipFacts.inactive` holds for table 22.  Note
the direction: the tempting `act · (1 − pf j)` is **wrong** — it would force active rows to have
`pf j = 1`, but an argument may legitimately be absent and an aborting call has `nres = 0` (it
failed the KAT on 4 host programs before being corrected).

Consequently the CH decomposition is available in the active-rows form the induction needs:
`host_trace_ok` (`Main/HostChipFacts.lean`) derives `HostTraceOK` from `Holds`, and
`host_part_ch_recv_active` / `host_part_ch_send_active` below use it.  `msgs_ch_host` itself stays
unconditional, which is sound and is what `Main/HostBus.host_hch` starts from.

## The remaining statement (the induction)

The induction `exec_of_rows` re-run for the host AIR, threading `S_seg`/`segb`.  Every base row
keeps the segment (`RowSpec`'s `RelW` at `S_seg segb`); each HOST row restarts it
(`(S_seg, segb) ↦ (S + fee, g_after)`, `StepHost.host_seg`).  The honest statement is:

```
theorem wasm_base_exec_host_holds (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)          -- NOT implied by H (bus balance is joined)
    (hpub : PubOK X nloc ngl pub) (hcode : CodeOK X tr) (hfunc : FuncOK X tr)
    (seg) (hkeep : SegKeep tr pub seg) (hhold : HoldRow X tr pub seg)  -- HoldRow = the missing
                                                                      -- host row's RowSpecSeg
    (st) (hstStatus : (st : F) = pub.pubStatus) (hlen) (boundary: init/entry/gas) :
    (actListHost tr pub).length + 1 = (pub.pubN).toNat ∧
    (st = 1 → ∃ sN, run X.cfg X.p (#rows) s0 = .fin sN ∧ sN.frames = [] ∧
      X.R * (pubS − S_seg_final) + sN.gas.g = segb_final) ∧
    (st = 2 → ∃ sN e, run … = .abort sN e ∧ …)
```

It lives in `WasmBase/Main/SoundHost.lean`.  The bus premises `hst`/`hch` are **discharged** from
`Holds` + `H0` (`host_hst`/`host_hch`), and the instruction rows' row facts from
`Main.Final.chipFacts`; `HostOK`/`HostResp` are not parameters (their content is inside
`HoldRow`'s `RowSpecSeg`).  What is still assumed is stated there: `H0` (which the host trace's
`Holds` does not give, because the joined bus balance does not split), `HoldRow` (the active HOST
rows' segment-aware row facts — no lemma for it exists), `SegKeep`, `hstepgas`, `hlen`, and the
boundary/entry facts.  `SoundHost.lean` also records, with kernel-checked refutations, that the
previously published harness was vacuous over host traces (`hstepgas` unsatisfiable, `h2` excluding
host rows, `RowFactsSegMap` indexed by list position).  What is already available:

* `host_rowspec` (the HOST row's `RowSpec` at the trace level) and `RowHostSpec.host_arg_stack` /
  `host_word_stack` (piece 1 at the `RelW` boundary);
* `StepHost.step_host_ok` / `step_host_ok_seg` / `host_seg` (the spec step and its successor
  segment) and `Main.Host.host_row_seg` (the row's successor segment from `HostOK`);
* `host_msgs_air`, `msgs_state_host`, `msgs_ch_host`, `host_occs_air` (the bus decomposition).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## The table split -/

/-- Every bus of the host AIR is the base AIR's plus the HOST, HOSTO and HOSTT parts. -/
theorem host_msgs_air (nloc ngl : Nat) (tr : Trace) (pub : List F) (b : Nat) (s : Bool) :
    msgs (wasmBaseHostAir nloc ngl) tr pub b s =
      msgs (wasmBaseAir nloc ngl) tr pub b s ++
      (part Host.table tr pub 22 b s ++ (part HostO.table tr pub 23 b s ++
        (part HostTab.table tr pub 24 b s ++ part HostB.table tr pub 25 b s))) := by
  rw [msgs_flatMap, msgs_flatMap]
  have e : (wasmBaseHostAir nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [Host.table, HostO.table, HostTab.table, HostB.table] := rfl
  rw [e, List.zipIdx_append]
  simp only [List.flatMap_append, List.length_map, air_len, Nat.zero_add, part, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.zipIdx_cons, Nat.reduceAdd]
  rw [show ([].zipIdx 26 : List (Table × Nat)) = [] from rfl]
  simp only [List.flatMap_nil, List.append_nil]

/-- The occurrence list of the host AIR is the base AIR's plus the HOST table's. -/
theorem host_occs_air (nloc ngl : Nat) (tr : Trace) (pub : List F) :
    occs (wasmBaseHostAir nloc ngl) tr pub =
      occs (wasmBaseAir nloc ngl) tr pub ++
      ((List.range (tr.height 22)).flatMap fun r => rowOccs Host.table tr pub 22 r) ++
      (((List.range (tr.height 23)).flatMap fun r => rowOccs HostO.table tr pub 23 r) ++
        (((List.range (tr.height 24)).flatMap fun r => rowOccs HostTab.table tr pub 24 r) ++
          ((List.range (tr.height 25)).flatMap fun r => rowOccs HostB.table tr pub 25 r))) := by
  unfold occs
  have e : (wasmBaseHostAir nloc ngl).tables =
      (wasmBaseAir nloc ngl).tables ++ [Host.table, HostO.table, HostTab.table, HostB.table] := rfl
  rw [e, List.zipIdx_append]
  simp only [List.flatMap_append, List.length_map, air_len, Nat.zero_add, List.zipIdx_cons,
    List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, rowOccs, Nat.reduceAdd]
  have h0 : ([].zipIdx 26 : List (Table × Nat)) = [] := rfl
  simp only [show ([].zipIdx 26 : List (Table × Nat)) = [] from rfl, List.flatMap_nil,
    List.append_nil, List.append_assoc]

/-! ## The HOST row's STATE messages -/

theorem rowMsgs_host_state (tr : Trace) (pub : List F) (r : Nat) :
    rowMsgs Host.table tr pub 22 r busState true =
      (if rowAct Host.table tr pub 22 r then [rowOut Host.table tr pub 22 r] else []) ∧
    rowMsgs Host.table tr pub 22 r busState false =
      (if rowAct Host.table tr pub 22 r then [rowIn Host.table tr pub 22 r] else []) := by
  have h1 : Host.inters.filter (fun i => i.bus = busState ∧ i.send = true) =
      [Host.inters.getD 1 default] := by
    rw [host_inters_state.2]; rfl
  have h0 : Host.inters.filter (fun i => i.bus = busState ∧ i.send = false) =
      [Host.inters.getD 0 default] := by
    rw [host_inters_state.1]; rfl
  constructor
  · rw [rowMsgs_single Host.table tr pub 22 r busState true _ h1]; unfold rowAct rowOut; rfl
  · rw [rowMsgs_single Host.table tr pub 22 r busState false _ h0]; unfold rowAct rowIn; rfl

/-- The HOST table's STATE sends: the active rows' outputs, in order. -/
theorem host_part_state_T (tr : Trace) (pub : List F) :
    part Host.table tr pub 22 busState true =
      (List.range (tr.height 22)).flatMap fun r =>
        (if rowAct Host.table tr pub 22 r then [rowOut Host.table tr pub 22 r] else []) := by
  unfold part
  congr 1
  funext r
  rw [(rowMsgs_host_state tr pub r).1]

/-- The HOST table's STATE receives: the active rows' inputs, in order. -/
theorem host_part_state_F (tr : Trace) (pub : List F) :
    part Host.table tr pub 22 busState false =
      (List.range (tr.height 22)).flatMap fun r =>
        (if rowAct Host.table tr pub 22 r then [rowIn Host.table tr pub 22 r] else []) := by
  unfold part
  congr 1
  funext r
  rw [(rowMsgs_host_state tr pub r).2]

/-! ## The oracle and the cached host table carry no STATE or CH interaction

`HOSTB` *does* carry CH interactions since the MEMIO link (`Chips.HostB.memCnt`): a request byte
receives and re-sends the space-3 message of `ptr + pos`.  Its block is therefore part of
`msgs_ch_host` below, and `Main/MemIOBus` proves it is exactly the active `HOSTB` rows' messages. -/

theorem host_part_nil_env {nloc ngl : Nat} (tr : Trace) (pub : List F) (b : Nat) (s : Bool)
    (hb : b = busState ∨ b = busStk) :
    part HostO.table tr pub 23 b s = [] ∧ part HostTab.table tr pub 24 b s = [] := by
  refine ⟨?_, ?_⟩ <;> (unfold part; rw [List.flatMap_eq_nil_iff]; intro r _)
  · rw [rowMsgs_eq]
    rcases hb with rfl | rfl <;> cases s <;>
      simp [HostO.table, busState, busStk, busR16, busHostQ, busHostR]
  · rw [rowMsgs_eq]
    rcases hb with rfl | rfl <;> cases s <;>
      simp [HostTab.table, busState, busStk, busR16, busHostT, busHostQ, busHostR, busHostB]

/-- `HOSTB` carries no STATE interaction, so it contributes nothing to the STATE bus. -/
theorem hostb_part_nil_state (tr : Trace) (pub : List F) (s : Bool) :
    part HostB.table tr pub 25 busState s = [] := by
  unfold part; rw [List.flatMap_eq_nil_iff]; intro r _
  rw [rowMsgs_eq]
  rw [show (HostB.table.inters.filter (fun i => i.bus = busState ∧ i.send = s)) = [] by
    cases s <;> decide]
  rfl

/-! ## The STATE and CH messages of a host trace -/

/-- The STATE bus of a host trace: base boundary + base instruction rows, then the HOST rows. -/
theorem msgs_state_host {nloc ngl : Nat} (tr : Trace) (pub : List F) :
    msgs (wasmBaseHostAir nloc ngl) tr pub busState true =
      msgs (wasmBaseAir nloc ngl) tr pub busState true ++
        (List.range (tr.height 22)).flatMap (fun r =>
          if rowAct Host.table tr pub 22 r then [rowOut Host.table tr pub 22 r] else []) ∧
    msgs (wasmBaseHostAir nloc ngl) tr pub busState false =
      msgs (wasmBaseAir nloc ngl) tr pub busState false ++
        (List.range (tr.height 22)).flatMap (fun r =>
          if rowAct Host.table tr pub 22 r then [rowIn Host.table tr pub 22 r] else []) := by
  have h := host_part_nil_env (nloc := nloc) (ngl := ngl) tr pub
  constructor
  · obtain ⟨e1, e2⟩ := h busState true (Or.inl rfl)
    rw [host_msgs_air, e1, e2, hostb_part_nil_state, host_part_state_T]
    simp
  · obtain ⟨e1, e2⟩ := h busState false (Or.inl rfl)
    rw [host_msgs_air, e1, e2, hostb_part_nil_state, host_part_state_F]
    simp

/-- The CH bus of a host trace: base boundary + base instruction rows, then the HOST rows' messages
(`rowMsgs … busStk`) **and the HOSTB rows'** (the MEMIO link's space-3 messages), on each side. -/
theorem msgs_ch_host {nloc ngl : Nat} (tr : Trace) (pub : List F) :
    msgs (wasmBaseHostAir nloc ngl) tr pub busStk true =
      msgs (wasmBaseAir nloc ngl) tr pub busStk true ++
        (part Host.table tr pub 22 busStk true ++ part HostB.table tr pub 25 busStk true) ∧
    msgs (wasmBaseHostAir nloc ngl) tr pub busStk false =
      msgs (wasmBaseAir nloc ngl) tr pub busStk false ++
        (part Host.table tr pub 22 busStk false ++ part HostB.table tr pub 25 busStk false) := by
  have h := host_part_nil_env (nloc := nloc) (ngl := ngl) tr pub
  constructor
  · obtain ⟨e1, e2⟩ := h busStk true (Or.inr rfl)
    rw [host_msgs_air, e1, e2]
    rfl
  · obtain ⟨e1, e2⟩ := h busStk false (Or.inr rfl)
    rw [host_msgs_air, e1, e2]
    rfl

/-! ## The HOST rows' CH messages, decoded -/

/-- The decoded CH receives of a HOST row are its `rowCons` (definitional). -/
theorem host_row_recv_eq (tr : Trace) (pub : List F) (r : Nat) :
    (rowMsgs Host.table tr pub 22 r busStk false).map decMsg = rowCons Host.table tr pub 22 r := rfl

/-- The decoded CH sends of a HOST row are its `rowProd` (definitional). -/
theorem host_row_send_eq (tr : Trace) (pub : List F) (r : Nat) :
    (rowMsgs Host.table tr pub 22 r busStk true).map decMsg = rowProd Host.table tr pub 22 r := rfl

/-- The HOST table's CH receives, decoded, row by row. -/
theorem host_part_ch_recv (tr : Trace) (pub : List F) :
    (part Host.table tr pub 22 busStk false).map decMsg =
      (List.range (tr.height 22)).flatMap fun r => rowCons Host.table tr pub 22 r := by
  unfold part
  rw [List.map_flatMap]
  rfl

/-- The HOST table's CH sends, decoded, row by row. -/
theorem host_part_ch_send (tr : Trace) (pub : List F) :
    (part Host.table tr pub 22 busStk true).map decMsg =
      (List.range (tr.height 22)).flatMap fun r => rowProd Host.table tr pub 22 r := by
  unfold part
  rw [List.map_flatMap]
  rfl

/-- `flatMap` congruence when the functions are pointwise equal on the list. -/
theorem flatMap_congr_on {α β : Type} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-! ## A trace-level side condition making the HOST rows behave like chips

As noted above, the HOST table's CH receives use `pf j` rather than `act · pf j`, so an inactive
row can still carry count-1 CH messages.  `HostTraceOK` is the exact trace-level condition under
which inactive HOST rows carry **no** CH interaction, i.e. under which the decomposition is the
base one plus the active HOST rows: `HostTraceOK` now follows from `Holds`, because the gating
constraints `Host.cActPf`/`Host.cActNres` force inactive rows to emit nothing. -/

/-- No inactive HOST row carries a CH message (all `pf j` and `nres` are zero off the active rows). -/
def HostTraceOK (tr : Trace) (pub : List F) : Prop :=
  ∀ r, r < tr.height 22 → ¬ rowAct Host.table tr pub 22 r →
    (∀ j, j < Host.nArgs → rowNat tr 22 r (Host.pf j) = 0) ∧ rowNat tr 22 r Host.nres = 0

/-- Under `HostTraceOK`, `rowCons` vanishes on inactive HOST rows. -/
theorem host_row_cons_inactive {tr : Trace} {pub : List F} {r : Nat}
    (h : ∀ j ∈ Host.argRange, rowNat tr 22 r (Host.pf j) = 0) :
    rowCons Host.table tr pub 22 r = [] := by
  rw [host_row_cons]
  rw [List.flatMap_eq_nil_iff]
  intro j hj
  rw [h j hj]
  rfl

/-- Under `HostTraceOK`, `rowProd` vanishes on inactive HOST rows. -/
theorem host_row_prod_inactive {tr : Trace} {pub : List F} {r : Nat}
    (hn : rowNat tr 22 r Host.nres = 0) :
    rowProd Host.table tr pub 22 r = [] := by
  rw [host_row_prod, if_neg (by omega)]

/-- **The CH receives of a host trace, restricted to active HOST rows.**  Under `HostTraceOK` the
inactive rows contribute nothing, so the decoded CH receives are the active HOST rows' arguments
(the base rows' contribution is `msgs wasmBaseAir …` of `msgs_ch_host`). -/
theorem host_part_ch_recv_active {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (HT : HostTraceOK tr pub) :
    (part Host.table tr pub 22 busStk false).map decMsg =
      (List.range (tr.height 22)).flatMap fun r =>
        (if rowAct Host.table tr pub 22 r then
          (Host.argRange.flatMap fun j =>
            (if rowNat tr 22 r (Host.pf j) = 1 then [argMsg tr r j] else []))
        else []) := by
  rw [host_part_ch_recv]
  refine flatMap_congr_on _ _ _ ?_
  intro r hr
  rw [List.mem_range] at hr
  by_cases ha : rowAct Host.table tr pub 22 r
  · rw [if_pos ha]
    -- the active row's consumed messages are exactly its present arguments
    exact host_row_cons
  · obtain ⟨h0, hn⟩ := HT r hr ha
    rw [if_neg ha, host_row_cons_inactive (fun j hj => h0 j (argRange_lt hj))]

/-- **The CH sends of a host trace, restricted to active HOST rows.** -/
theorem host_part_ch_send_active {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (HT : HostTraceOK tr pub) :
    (part Host.table tr pub 22 busStk true).map decMsg =
      (List.range (tr.height 22)).flatMap fun r =>
        (if rowAct Host.table tr pub 22 r then
          (if rowNat tr 22 r Host.nres = 1 then [wordMsg tr r] else []) else []) := by
  rw [host_part_ch_send]
  refine flatMap_congr_on _ _ _ ?_
  intro r hr
  rw [List.mem_range] at hr
  by_cases ha : rowAct Host.table tr pub 22 r
  · rw [if_pos ha, host_row_prod]
  · obtain ⟨h0, hn⟩ := HT r hr ha
    rw [if_neg ha, host_row_prod_inactive hn]

/-! ## The HOST rows' arguments as live stack messages (piece 1 composed with the trace)

The two halves of `RESULTS.md` §3.1 compose here: an active HOST row whose STATE input is the one a
`RelW` is related to consumes exactly its `argMsg`s (`RowHostSpec.cons`), and those are the live
stack messages at slots `size − np + j` (`host_arg_view` + `host_arg_slot`). -/

/-- **The consumed arguments are live stack messages.**  For an active HOST row at the STATE input
of a `RelW`-related state, each present argument message is one of the messages in `stackView`. -/
theorem host_arg_stack {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    {tr : Trace} {r j : Nat} (hr : r < tr.height 22)
    (hsb : rowNat tr 22 r Host.kSb = E.sb) (h3 : rowNat tr 22 r cH = s.stack.size - E.sb)
    (hnp : rowNat tr 22 r Host.np ≤ s.stack.size) (hj : j < rowNat tr 22 r Host.np)
    (hj2 : j < Host.nArgs)
    (hin : live (argMsg tr r j)) :
    argMsg tr r j ∈ stackView s.stack tps :=
  (host_arg_view R (host_arg_slot R hsb h3 hnp hj2) hj hnp hin).1

/-- **The produced result word is the response's.**  The `HOSTR` result message of an active row
with `ar = 1` is the encoding of the response's single result word as an `i64`. -/
theorem host_word_stack {nloc ngl : Nat} {pub : List F} {tr : Trace} {resp : Nat → HostAnswer}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (HOK : HostOK tr resp)
    (hsend : ∀ o ∈ occs (wasmBaseHostAir nloc ngl) tr pub, o.2.1 = true → o.2.2.2 ≤ 1)
    {r : Nat} (hr : r < tr.height 22) (hact : rowAct Host.table tr pub 22 r) {ts : Nat}
    (har : rowNat tr 22 r Host.ar = 1) (hnw : (resp ts).results.length = 1) :
    wordMsg tr r = enc 0 (hostSlot tr r 0) (.i64 (UInt64.ofNat ((resp ts).results.headD 0)))
      (rowNat tr 22 r cTs) :=
  host_word_is_resp H HOK hsend hr hact har hnw

end WasmBase
