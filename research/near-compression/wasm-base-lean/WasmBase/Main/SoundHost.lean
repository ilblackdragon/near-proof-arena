import WasmBase.Main.SegHarness
import WasmBase.Main.HostRel
import WasmBase.Main.HostBus
import WasmBase.Main.MemIOBus
import WasmBase.Main.Final
import WasmBase.StepHost

/-!
# WasmBase.Main.SoundHost — `wasm_base_sound_host`: the statement, and the trust boundary

Lane `pq-nv-faithful`, 2026-10-21.  `Main/SegHarness.lean:wasm_base_exec_host` is the host-aware
execution theorem, parameterised by the whole per-row instantiation (`seg`, `hrows`, `hst`, `hch`,
`hstepgas`, `hinit`, `h0`, `hlen`, `hfee`).  This file packages those into a statement about
`Holds (wasmBaseHostAir …)` and states precisely what is left.

## Three defects in the inherited harness (fixed in `Main/SegHarness.lean`)

The published `wasm_base_exec_host` was **vacuous over host traces**, for three independent reasons:

1. **`hstepgas` was unsatisfiable.**  It read `∀ t S, R·(S + maxFee − (segs t).1) ≤ (segs t).2`; at
   `S := (segs t).2 + (segs t).1 + maxFee + 1` the left side exceeds the right for every `R ≥ 1`,
   and `X.R = X.cfg.regularOpCost ≠ 0` (`CheckFacts.regPos`), so *no* instantiation existed.  It is
   now the machine fact `R·(S − S_seg) + g = segb → R·(S + maxFee − S_seg) ≤ segb`; the old form's
   refutation is `hstepgas_unsat` below.
2. **`h2 : RowFacts2` excluded every host trace.**  `RowFacts2.spec` is a `RowSpec2` at one *fixed*
   segment; the HOST row's successor `Rel` lives at `(S + fee, g_after)`, so no host row can satisfy
   it.  The premise is removed; every field it carried is a field of `RowFactsSeg`
   (`RowFactsSeg.toFlat`).
3. **`RowFactsSegMap` was indexed by list position, not STATE time.**  It quantified over *every*
   `k : Nat`, demanding `RowSpecSeg` at `seg (k+1) (k+2)` for a row whose STATE time is unrelated to
   `k`; nothing in a trace implies that.  It is now indexed by the row's own STATE time.

Without these the theorem could only be applied to traces with no host row — i.e. never to the AIR
it names.  `pq-hch/RESULTS.md`'s claim that the join's remaining work was "only the instantiation
layer" therefore understated it: the harness itself was not applicable.

## The statement that now exists

`wasm_base_exec_host_holds` takes `Holds (wasmBaseHostAir …)`, the base AIR's `Holds`, `PubOK`,
`CodeOK`, `FuncOK`, `HostOK`, `HostResp` and the boundary facts, and derives the segmented
execution.  Discharged inside: `hst`/`hch` (`host_buses`), `st` (`PubOK.status`), `hlen` (height
caps), `hrows` on instruction rows (`Main.Final.chipFacts` + `SegKeep`).  Still named:

* `H0 : Holds (wasmBaseAir nloc ngl) pub tr` — **does not follow from the host trace's `Holds`**:
  the joined balance reads `base + host = base' + host'` and does not split.  (Constraints, heights
  and booleanity do transfer, the base tables being a prefix.)  "`hst`/`hch` from `Holds` alone" is
  therefore an overstatement: it is from `Holds` **plus** `H0`.
* `hhold : HoldRow` — the active HOST rows' segment-aware row facts.  **No lemma exists** for this.
  `Main/RowHostSpec.lean:24` advertises `host_step_spec` and `Main/SegHarness.lean:92` advertises
  `RowSpecSeg.ofHost`; **neither identifier is in the tree** (`grep` finds only the docstrings).  The
  ingredients are present (`host_rowfacts`, `host_arg_view`, `host_word_is_resp`,
  `step_host_ok_seg`, `host_rel_restart`) but were never assembled — this is the one real proof debt
  on the host row, and it is `HoldRow` below.
* `hstStatus` — the trace's status cell `st` is the public status word (the harness's `st` and
  `host_hst`'s `pubStatus` are the same field, but nothing in `Holds` links the two spellings);
* `hsegKeep` (the thread moves only at host rows), `hstepgas` (the fee fits), `hlen` (the step
  count fits the field: the height caps give only `< 2^28 + 2^24`, `actListHost_length`, so the
  tighter `2^28` is a genuine statement-level premise exactly as in the classical `wasm_base_exec`),
  and the boundary
  (`hinitTp`, `hinitNd`, `h0`, `hg64`, `hfeeN`) which is `Main/Exec.lean:init_rel`'s instantiation.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## Defect 1, recorded -/

/-- **The old `hstepgas` form was unsatisfiable** for any `R ≥ 1`, i.e. for every real instance.
With `S = (segs t).2 + (segs t).1 + maxFee + 1` it claims
`R·(segs t).2 + 2·R·maxFee + R ≤ (segs t).2`. -/
theorem hstepgas_unsat_aux (R maxFee : Nat) (hR : 1 ≤ R) (seg : Nat → Nat × Nat) :
    ¬ (∀ t S : Nat, R * (S + maxFee - (seg t).1) ≤ (seg t).2) := by
  intro h
  have h0 := h 0 ((seg 0).2 + (seg 0).1 + maxFee + 1)
  have e : (seg 0).2 + (seg 0).1 + maxFee + 1 + maxFee - (seg 0).1
      = (seg 0).2 + 2 * maxFee + 1 := by omega
  rw [e] at h0
  have h1 : (seg 0).2 + 2 * maxFee + 1 ≤ R * ((seg 0).2 + 2 * maxFee + 1) := by
    calc (seg 0).2 + 2 * maxFee + 1 = 1 * ((seg 0).2 + 2 * maxFee + 1) := by rw [Nat.one_mul]
      _ ≤ R * ((seg 0).2 + 2 * maxFee + 1) := Nat.mul_le_mul_right _ hR
  omega

/-- `X.R ≥ 1` for every checked module (`CheckFacts.regPos`). -/
theorem ctx_R_pos (X : Ctx) : 1 ≤ X.R :=
  Nat.one_le_iff_ne_zero.mpr X.facts.regPos

/-- **The old `hstepgas` was vacuous because nothing satisfied it.** -/
theorem old_hstepgas_unsat (X : Ctx) (seg : Nat → Nat × Nat) :
    ¬ (∀ t S : Nat, X.R * (S + X.maxFee - (seg t).1) ≤ (seg t).2) :=
  hstepgas_unsat_aux X.R X.maxFee (ctx_R_pos X) seg

/-! ## The premises about the thread and the HOST rows -/

/-- **The active HOST rows' segment-aware row facts.**  At STATE time `ts` a HOST row runs in
`seg ts` and leaves `seg (ts+1)`.  No `run` appears, so this is a premise about the trace, not a
restatement of the conclusion.  It is exactly what a `RowSpecSeg.ofHost` would prove from
`host_rowfacts`, `host_arg_view`, `host_word_is_resp`, `step_host_ok_seg` and
`host_rel_restart` — the missing lemma named above. -/
def HoldRow (X : Ctx) (tr : Trace) (pub : List F) (seg : Nat → Nat × Nat) : Prop :=
  ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
    RowFactsSeg X (rowInH tr pub (22, r)) (rowOutH tr pub (22, r))
      (consCH tr pub (22, r)) (prodCH tr pub (22, r))
      (seg (rowNat tr 22 r 1)) (seg (rowNat tr 22 r 1 + 1))

/-- **The thread is constant at instruction rows** — true of any `seg` that only host rows move. -/
def SegKeep (tr : Trace) (pub : List F) (seg : Nat → Nat × Nat) : Prop :=
  ∀ ρ ∈ actListHost tr pub, ρ.1 ≠ 22 →
    seg ((lvl (rowInH tr pub ρ)).toNat + 1) = seg ((lvl (rowInH tr pub ρ)).toNat)

/-- **Assembling `hrows`.**  Instruction rows keep the segment (`SegKeep`) and their `RowFacts2`
becomes a `RowFactsSeg` at `seg t`/`seg t = seg t`/`seg (t+1)`; HOST rows are `HoldRow` verbatim.
The instruction rows' accessors are `chipT`'s because `chipTHost` is the identity off table 22. -/
theorem rowFactsSegMap_of {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub)
    (hcode : CodeOK X tr) (hfunc : FuncOK X tr)
    {seg : Nat → Nat × Nat} (hkeep : SegKeep tr pub seg) (hhold : HoldRow X tr pub seg) :
    ∀ r ∈ actListHost tr pub,
      RowFactsSegMap X (rowInH tr pub r) (rowOutH tr pub r) (consCH tr pub r) (prodCH tr pub r) seg := by
  intro ρ hρ
  unfold RowFactsSegMap
  rcases List.mem_append.mp hρ with hinstr | hhost
  · obtain ⟨h1, h9, hr, ha⟩ := mem_actList hinstr
    have hne : ρ.1 ≠ 22 := by omega
    have hRF : RowFacts2 X (rowIn (chipT ρ.1) tr pub ρ.1 ρ.2) (rowOut (chipT ρ.1) tr pub ρ.1 ρ.2)
        (rowCons (chipT ρ.1) tr pub ρ.1 ρ.2) (rowProd (chipT ρ.1) tr pub ρ.1 ρ.2) :=
      (chipFacts X H0).rows
        (looks_of H0 hcode hfunc (fun o ho hs => occ_bits H0 hpub (chipFacts X H0) o ho (Or.inl hs)))
        hpub ρ.1 h1 h9 ρ.2 hr ha
    have hIH : rowInH tr pub ρ = rowIn (chipT ρ.1) tr pub ρ.1 ρ.2 ∧
        rowOutH tr pub ρ = rowOut (chipT ρ.1) tr pub ρ.1 ρ.2 ∧
        rowConsH tr pub ρ = rowCons (chipT ρ.1) tr pub ρ.1 ρ.2 ∧
        rowProdH tr pub ρ = rowProd (chipT ρ.1) tr pub ρ.1 ρ.2 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [rowInH, rowOutH, rowConsH, rowProdH, chipTHost, hne]
    obtain ⟨e1, e2, e3, e4⟩ := hIH
    have hpc : hostbProdH tr pub ρ = [] := by simp only [hostbProdH, hne, if_false]
    have hcc : hostbConsH tr pub ρ = [] := by simp only [hostbConsH, hne, if_false]
    have hP : prodCH tr pub ρ = rowProd (chipT ρ.1) tr pub ρ.1 ρ.2 := by
      simp only [prodCH, hpc, List.append_nil]; rw [e4, show chipT ρ.1 = chipTHost ρ.1 from by
        simp [chipTHost, hne]]
    have hC : consCH tr pub ρ = rowCons (chipT ρ.1) tr pub ρ.1 ρ.2 := by
      simp only [consCH, hcc, List.append_nil]; rw [e3, show chipT ρ.1 = chipTHost ρ.1 from by
        simp [chipTHost, hne]]
    rw [e1, e2, hC, hP]
    have hs := hkeep ρ (List.mem_append_left _ hinstr) hne
    rw [e1] at hs
    rw [← hs]
    exact hRF.toSeg
  · have h22 : ρ.1 = 22 := hostActRows_eq_host hhost
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hhost
    have hrt : r < tr.height 22 := List.mem_range.mp (List.mem_filter.mp hr).1
    have hra : rowAct Host.table tr pub 22 r := by
      have := (List.mem_filter.mp hr).2; simpa using this
    exact hhold r hrt hra

/-! ## The packaged theorem -/

/-- `actListHost`'s length bound from the height caps: instruction rows are `< 14 · 2^24` and the
HOST rows `< 2^24`. -/
theorem actListHost_length {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) :
    (actListHost tr pub).length < 2 ^ 29 := by
  have h1 := actList_length H0
  have hh : (hostActRows tr pub).length ≤ 2 ^ 24 := by
    unfold hostActRows
    rw [List.length_map]
    have := List.length_filter_le (fun r => decide (rowAct Host.table tr pub 22 r))
      (List.range (tr.height 22))
    refine Nat.le_trans this ?_
    rw [List.length_range]
    have hlt := H.heightLe 22 (by simp [wasmBaseHostAir, air_len])
    simp only [maxLogHeight] at hlt
    exact hlt
  unfold actListHost
  rw [List.length_append]
  omega

/-- **`wasm_base_sound_host`.**  The host-AIR execution theorem with everything the tree can supply
already discharged: the bus perms (`host_hst`/`host_hch`), the segment-free row facts, the step
count, the status and the height bound.  What remains is stated, not hidden:

* `H0` — the base AIR's `Holds`, which does not follow from the host trace's (see the header);
* `HoldRow` — the active HOST rows' segment-aware row facts: **the missing `host_step_spec`**.
  Note that `HostOK`/`HostResp` are *not* parameters: their content (the response the row produced,
  and its `g_after`) is part of `HoldRow`'s `RowSpecSeg`, so the packaged theorem reads
  `Holds`-plus-`H0`-plus-`HoldRow` and nothing else about the host table;
* `SegKeep` — the thread moves only at host rows;
* `hstepgas` — the fee fits in the remaining budget;
* `hfeeN` — `N · (maxFee + 1) < p`, the statement-level bound `wasm_base_exec` also takes;
* the boundary (`hinitTp`, `hinitNd`, `h0`) and `hg64`.

The conclusion reports the **last** segment, because a host call re-synchronises the budget. -/
theorem wasm_base_exec_host_holds (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {resp : Nat → HostAnswer} {s0 : St} {f0 : Frame}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hb : HostBLinked tr pub)
    (hpub : PubOK X nloc ngl pub) (hcode : CodeOK X tr) (hfunc : FuncOK X tr)
    (seg : Nat → Nat × Nat) (hkeep : SegKeep tr pub seg) (hhold : HoldRow X tr pub seg)
    (st : Nat) (hst12 : st = 1 ∨ st = 2)
    (hstStatus : (st : F) = pub.getD Boundary.pubStatus 0)
    (hlen : (actListHost tr pub).length < 2 ^ 28)
    (hinitTp : ∀ x ∈ (initRaw nloc pub).map decMsg ++
        ((globRaw nloc ngl pub).map decMsg ++ ((budRaw nloc ngl pub).map decMsg ++
          (memRaw tr pub).map decMsg)), x.tp = 0)
    (hinitNd : ((initRaw nloc pub).map decMsg ++
        ((globRaw nloc ngl pub).map decMsg ++ ((budRaw nloc ngl pub).map decMsg ++
          (memRaw tr pub).map decMsg))).Nodup)
    (hfeeN : (pub.getD Boundary.pubN 0).toNat * (X.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (seg t).1) + g = (seg t).2 →
      X.R * (S + X.maxFee - (seg t).1) ≤ (seg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    (h0 : RelW X ⟨0, 0, [], (fun x => x ∈
        (initRaw nloc pub).map decMsg ++ ((globRaw nloc ngl pub).map decMsg ++
          ((budRaw nloc ngl pub).map decMsg ++ (memRaw tr pub).map decMsg))), 0⟩ s0 f0
      (fun _ => 0) (fun _ => 0) 1 0 0
      (· ∈ (initRaw nloc pub).map decMsg ++ ((globRaw nloc ngl pub).map decMsg ++
        ((budRaw nloc ngl pub).map decMsg ++ (memRaw tr pub).map decMsg)))
      (seg 1).1 (seg 1).2) :
    (actListHost tr pub).length + 1 = (pub.getD Boundary.pubN 0).toNat ∧
    (st = 1 → ∃ (sN : St),
      run X.cfg X.p (actListHost tr pub).length s0 = .fin sN ∧ sN.frames = [] ∧
      X.R * ((pub.getD Boundary.pubS 0).toNat - (seg ((actListHost tr pub).length + 1)).1) +
        sN.gas.g = (seg ((actListHost tr pub).length + 1)).2) ∧
    (st = 2 → ∃ (sN : St) (e : String),
      run X.cfg X.p (actListHost tr pub).length s0 = .abort sN e ∧
      X.R * ((pub.getD Boundary.pubS 0).toNat - (seg ((actListHost tr pub).length + 1)).1) +
        sN.gas.g = (seg ((actListHost tr pub).length + 1)).2) := by
  have hrows := rowFactsSegMap_of H0 hpub hcode hfunc hkeep hhold
  have hbuses := host_buses H H0 hpub (chipFacts X H0) hb
  have hstPerm : (stMsg 0 1 0 0 0 0 :: (actListHost tr pub).map (rowOutH tr pub)).Perm
      ([tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
        (st : F), tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
        (actListHost tr pub).map (rowInH tr pub)) := by
    have h := hbuses.1
    rw [← hstStatus] at h
    exact h
  have hfee : ((actListHost tr pub).length + 1) * (X.maxFee + 1) < ZkFormal.Algebra.P := by
    have hN : (actListHost tr pub).length + 1 = (pub.getD Boundary.pubN 0).toNat :=
      chain_len (actListHost tr pub) (rowInH tr pub) (rowOutH tr pub)
        (tr.cell 0 0 Boundary.pcf) (pub.getD Boundary.pubN 0) (pub.getD Boundary.pubS 0)
        (st : F) (tr.cell 0 0 Boundary.sbf) (tr.cell 0 0 Boundary.cidf)
        (fun r _ => (hrows r ‹_›).tsOut) hstPerm hlen
    rw [hN]; exact hfeeN
  obtain ⟨hN, h1, h2⟩ := wasm_base_exec_host (nloc := nloc) (ngl := ngl) X seg
    ((initRaw nloc pub).map decMsg ++
      ((globRaw nloc ngl pub).map decMsg ++ ((budRaw nloc ngl pub).map decMsg ++
        (memRaw tr pub).map decMsg)))
    (((if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then
        [resRaw pub tr] else []).map decMsg ++ (finRaw nloc tr).map decMsg) ++
      (drainRaw tr pub).map decMsg)
    st hst12 hrows (tr.cell 0 0 Boundary.sbf) (tr.cell 0 0 Boundary.cidf)
    hstPerm hbuses.2 hinitNd hinitTp hlen hfee hstepgas hg64
    ⟨rfl, rfl, rfl⟩ h0
  refine ⟨hN, fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨sN, _, _, _, hrun, hfr, hgas⟩ := h1 hs
    exact ⟨sN, hrun, hfr, hgas⟩
  · obtain ⟨sN, e, hrun, hgas⟩ := h2 hs
    exact ⟨sN, e, hrun, hgas⟩

/-! ## Axiom guards -/

#print axioms hstepgas_unsat_aux
#print axioms ctx_R_pos
#print axioms old_hstepgas_unsat
#print axioms rowFactsSegMap_of
#print axioms actListHost_length
#print axioms wasm_base_exec_host_holds

end WasmBase
