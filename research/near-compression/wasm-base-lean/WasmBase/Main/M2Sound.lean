import WasmBase.Main.M2Bus
/-!
# WasmBase.Main.M2Sound — `wasm_base_sound_m2`: the soundness theorem for `wasmBaseM2Air`

`exec_of_rows_seg` (`Main/SegHarness.lean`) instantiated against `Holds (wasmBaseM2Air …)` and an
`M2Ctx` (the M2 checker's context), with the segment-aware HOST row facts as the one remaining
row-level premise.  The statement has the shape of `wasm_base_exec_host_holds`
(`Main/SoundHost.lean`); unlike that theorem it does **not** take the base AIR's `Holds` (`H0`):
everything is derived from the M2 trace's own `Holds`.

## What is discharged

* **the STATE bus** (`hst`): `m2_hst` (`Main/M2Bus.lean`), from `Holds` alone;
* **the CH bus** (`hch`): `m2_hch`, from `Holds`, `HostBLinked` and `RegCLinked`;
* **the instruction rows** (tables 1–14, IF 26, CONV 28, UNREACH 29): `m2_rowfacts`
  (`Main/M2Dispatch.lean`), from `Holds`, the M2 checker, `PubOK`, `CodeOK`, `FuncOK`;
* the step count `N = #rows + 1` (`chain_len`), hence `hfee` from `hfeeN`.

## Named premises (all stated, none hidden)

* `CodeOK X.toCtx tr`, `FuncOK X.toCtx tr` — the commitment bindings of the CODE and FUNC tables to
  the checker's records (as in every `wasm_base_sound*` theorem);
* `HostBLinked tr pub` — every active `HOSTB` row carries the `(ts, hid)` key of an active HOST row,
  and HOST keys are distinct (`Main/SegHarness.lean`);
* **`RegCLinked tr pub`** (`Main/M2Bus.lean`) — every active REG-C row carries the `(ts, hid)` key of
  an active HOST row.  The register analogue of `HostBLinked.linked`; see "REG-C" below;
* **`HoldRowM2 X tr pub seg`** — the active HOST rows' segment-aware row facts, with the row's CH
  traffic fused with its call's `HOSTB` bytes **and its REG-C net traffic** (`consCHM2`/`prodCHM2`).
  This is where the host semantics is trusted: the HOSTO answers (`HostOK`/`HostResp` content, the
  response and `g_after`) and the register/memory effect of the call are inside its `RowSpecSeg`.
  It is the M2 form of `SoundHost.HoldRow` (no lemma proves either);
* `SegKeepM2` — the gas segment moves only at HOST rows;
* `hstStatus` (the status cell is the public status), `hlen` (`#rows < 2^28`), `hfeeN`,
  `hstepgas` (the fee fits the current segment), `hg64`, and the boundary/entry facts `hinitTp`,
  `hinitNd`, `h0` — exactly those of `wasm_base_exec_host_holds`.

## REG-C

REG-C rows are not action rows (they do not advance STATE time).  Their CH traffic is folded into
the host call whose `(ts, hid)` they carry, as `HOSTB`'s is.  Two facts make that fold sound and
non-vacuous:

* the **clear pairs cancel** (`regc_prod_split`/`regc_cons_split`): a clear row's two extra receives
  consume exactly the messages the row re-produces at `ts`, so they are removed from both sides of
  the CH balance; only the *net* traffic (`regNetProd`/`regNetCons`) is folded.  Without the
  cancellation `HoldRowM2` would ask a refill's host step to consume a message produced at its own
  time, which `RowFactsSeg.consT` forbids, and the premise would be unsatisfiable on honest refills;
* the grouping is a partition (`m2_reg_partition`): given `RegCLinked` and the distinct HOST keys of
  `HostBLinked.unique`, grouping the active REG-C rows by call permutes the table's net traffic
  (inactive rows have none: `regc_inactive_nil`).

`RegCLinked` is a named premise rather than a proof through the REG group walk: the walk
(`Main/RegWalk*.lean`) constrains a group's rows among themselves (key constancy, `pos`/`len`), but
nothing in `wasmBaseM2Air` looks a REG-C row's `(ts, hid)` up against a HOST row — fills are tied to
`HOSTB` bytes (bus `busHostB`) and `read_register` writes to HOST' (bus `busRegRd`), and neither
lookup's soundness is composed with `HostBLinked` here.

**The refill gap.**  At `wasmBaseM2Air` a fill may overwrite a live register without a clear group
(`m2/README.md`, "Update: absent-register header": the double-fill mutant verifies).  That gap does
not touch the bus decomposition proved here; it is a fact a proof of `HoldRowM2` would need (the
register messages of the call's `RowSpecSeg`), and `wasmBaseM2rAir` closes it at the AIR level
(`M2RegAbsent.lean`, header messages).
-/
namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-- **The active HOST rows' segment-aware row facts, M2 form.**  As `SoundHost.HoldRow`, with the
row's CH traffic fused with its call's `HOSTB` bytes and REG-C net traffic. -/
def HoldRowM2 (X : Ctx) (tr : Trace) (pub : List F) (seg : Nat → Nat × Nat) : Prop :=
  ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
    RowFactsSeg X (rowInM tr pub (22, r)) (rowOutM tr pub (22, r))
      (consCHM2 tr pub (22, r)) (prodCHM2 tr pub (22, r))
      (seg (rowNat tr 22 r 1)) (seg (rowNat tr 22 r 1 + 1))

/-- **The thread is constant at instruction rows** (M2 action list). -/
def SegKeepM2 (tr : Trace) (pub : List F) (seg : Nat → Nat × Nat) : Prop :=
  ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 →
    seg ((lvl (rowInM tr pub ρ)).toNat + 1) = seg ((lvl (rowInM tr pub ρ)).toNat)

theorem mem_actListM2 {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ ∈ actListM2 tr pub) :
    (ρ.1 = 22 ∧ ρ.2 < tr.height 22 ∧ rowAct Host.table tr pub 22 ρ.2) ∨
    (IsInstrM2 ρ.1 ∧ ρ.2 < tr.height ρ.1 ∧ rowAct (chipM2 ρ.1) tr pub ρ.1 ρ.2) := by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨h1, h9, hr, ha⟩ := mem_actList h
      refine Or.inr ⟨Or.inl ⟨h1, h9⟩, hr, ?_⟩
      have e : chipM2 ρ.1 = chipT ρ.1 := by
        simp only [chipM2]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [e]; exact ha
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hr
      exact Or.inl ⟨rfl, hr.1, hr.2⟩
  · simp only [tailActRows, List.mem_append, List.mem_map] at h
    rcases h with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;> rw [mem_actRowsT] at hr
    · exact Or.inr ⟨Or.inr (Or.inl rfl), hr.1, by simpa [chipM2] using hr.2⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inl rfl)), hr.1, by simpa [chipM2] using hr.2⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr rfl)), hr.1, by simpa [chipM2] using hr.2⟩

/-- **Assembling `hrows` for the M2 AIR.**  Instruction rows: `m2_rowfacts` (+ `SegKeepM2`);
HOST rows: `HoldRowM2` verbatim. -/
theorem rowFactsSegMap_m2 (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X.toCtx nloc ngl pub)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {seg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub seg) (hhold : HoldRowM2 X.toCtx tr pub seg) :
    ∀ ρ ∈ actListM2 tr pub,
      RowFactsSegMap X.toCtx (rowInM tr pub ρ) (rowOutM tr pub ρ) (consCHM2 tr pub ρ)
        (prodCHM2 tr pub ρ) seg := by
  intro ρ hρ
  obtain ⟨t, r⟩ := ρ
  rcases mem_actListM2 hρ with ⟨h22, hr, ha⟩ | ⟨htI, hr, ha⟩
  · simp only at h22 hr ha
    subst h22
    exact hhold r hr ha
  · simp only at htI hr ha
    have hne : t ≠ 22 := by rcases htI with ⟨_, h⟩ | h | h | h <;> omega
    have hRF := m2_rowfacts X H hpub hcode hfunc htI hr ha
    have ec : chipTM2 t = chipM2 t := by simp [chipTM2, hne]
    have hC : consCHM2 tr pub (t, r) = rowCons (chipM2 t) tr pub t r := by
      simp [consCHM2, rowConsM, hostbConsH, regConsH, hne, ec]
    have hP : prodCHM2 tr pub (t, r) = rowProd (chipM2 t) tr pub t r := by
      simp [prodCHM2, rowProdM, hostbProdH, regProdH, hne, ec]
    have hI : rowInM tr pub (t, r) = rowIn (chipM2 t) tr pub t r := by simp [rowInM, ec]
    have hO : rowOutM tr pub (t, r) = rowOut (chipM2 t) tr pub t r := by simp [rowOutM, ec]
    unfold RowFactsSegMap
    have hs := hkeep (t, r) hρ hne
    rw [hC, hP, hI, hO]
    rw [hI] at hs
    rw [hs]
    exact hRF.toSeg

/-- **`wasm_base_sound_m2`.**  A satisfied `wasmBaseM2Air` trace, for a function the M2 checker
accepted, is a run of the spec interpreter: the step count is `N − 1`; status 1 is a normal finish
with an empty frame stack, status 2 an abort; in both cases the gas of the final state is the last
segment's.  The named premises are listed in the module header. -/
theorem wasm_base_sound_m2 (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {s0 : St} {f0 : Frame}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr)
    (hpub : PubOK X.toCtx nloc ngl pub) (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    (seg : Nat → Nat × Nat) (hkeep : SegKeepM2 tr pub seg) (hhold : HoldRowM2 X.toCtx tr pub seg)
    (st : Nat) (hst12 : st = 1 ∨ st = 2)
    (hstStatus : (st : F) = pub.getD Boundary.pubStatus 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28)
    (hinitTp : ∀ x ∈ (initRaw nloc pub).map decMsg ++
        ((globRaw nloc ngl pub).map decMsg ++ ((budRaw nloc ngl pub).map decMsg ++
          (memRaw tr pub).map decMsg)), x.tp = 0)
    (hinitNd : ((initRaw nloc pub).map decMsg ++
        ((globRaw nloc ngl pub).map decMsg ++ ((budRaw nloc ngl pub).map decMsg ++
          (memRaw tr pub).map decMsg))).Nodup)
    (hfeeN : (pub.getD Boundary.pubN 0).toNat * (X.toCtx.maxFee + 1) < ZkFormal.Algebra.P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (seg t).1) + g = (seg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (seg t).1) ≤ (seg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (h0 : RelW X.toCtx ⟨0, 0, [], (fun x => x ∈
        (initRaw nloc pub).map decMsg ++ ((globRaw nloc ngl pub).map decMsg ++
          ((budRaw nloc ngl pub).map decMsg ++ (memRaw tr pub).map decMsg))), 0⟩ s0 f0
      (fun _ => 0) (fun _ => 0) 1 0 0
      (· ∈ (initRaw nloc pub).map decMsg ++ ((globRaw nloc ngl pub).map decMsg ++
        ((budRaw nloc ngl pub).map decMsg ++ (memRaw tr pub).map decMsg)))
      (seg 1).1 (seg 1).2) :
    (actListM2 tr pub).length + 1 = (pub.getD Boundary.pubN 0).toNat ∧
    (st = 1 → ∃ (sN : St),
      run X.cfg X.p (actListM2 tr pub).length s0 = .fin sN ∧ sN.frames = [] ∧
      X.toCtx.R * ((pub.getD Boundary.pubS 0).toNat - (seg ((actListM2 tr pub).length + 1)).1) +
        sN.gas.g = (seg ((actListM2 tr pub).length + 1)).2) ∧
    (st = 2 → ∃ (sN : St) (e : String),
      run X.cfg X.p (actListM2 tr pub).length s0 = .abort sN e ∧
      X.toCtx.R * ((pub.getD Boundary.pubS 0).toNat - (seg ((actListM2 tr pub).length + 1)).1) +
        sN.gas.g = (seg ((actListM2 tr pub).length + 1)).2) := by
  have hrows := rowFactsSegMap_m2 X H hpub hcode hfunc hkeep hhold
  have hbuses := m2_buses (X := X.toCtx) H hpub hb hg
  have hstPerm : (stMsg 0 1 0 0 0 0 :: (actListM2 tr pub).map (rowOutM tr pub)).Perm
      ([tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
        (st : F), tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
        (actListM2 tr pub).map (rowInM tr pub)) := by
    have h := hbuses.1
    rw [← hstStatus] at h
    exact h
  have hfee : ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < ZkFormal.Algebra.P := by
    have hN : (actListM2 tr pub).length + 1 = (pub.getD Boundary.pubN 0).toNat :=
      chain_len (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub)
        (tr.cell 0 0 Boundary.pcf) (pub.getD Boundary.pubN 0) (pub.getD Boundary.pubS 0)
        (st : F) (tr.cell 0 0 Boundary.sbf) (tr.cell 0 0 Boundary.cidf)
        (fun r hr => (hrows r hr).tsOut) hstPerm hlen
    rw [hN]; exact hfeeN
  obtain ⟨hN, h1, h2⟩ := exec_of_rows_seg X.toCtx (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub)
    (consCHM2 tr pub) (prodCHM2 tr pub)
    ((initRaw nloc pub).map decMsg ++
      ((globRaw nloc ngl pub).map decMsg ++ ((budRaw nloc ngl pub).map decMsg ++
        (memRaw tr pub).map decMsg)))
    (((if X.toCtx.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then
        [resRaw pub tr] else []).map decMsg ++ (finRaw nloc tr).map decMsg) ++
      (drainRaw tr pub).map decMsg)
    (tr.cell 0 0 Boundary.pcf) (pub.getD Boundary.pubN 0) (pub.getD Boundary.pubS 0) seg st hst12
    hrows (tr.cell 0 0 Boundary.sbf) (tr.cell 0 0 Boundary.cidf)
    hstPerm hbuses.2 hinitNd hinitTp hlen hfee hstepgas hg64 ⟨rfl, rfl, rfl⟩ h0
  refine ⟨hN, fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨sN, _, _, _, hrun, hfr, hgas, _⟩ := h1 hs
    exact ⟨sN, hrun, hfr, hgas⟩
  · obtain ⟨sN, e, hrun, hgas⟩ := h2 hs
    exact ⟨sN, e, hrun, hgas⟩

#print axioms m2_hst
#print axioms m2_hch
#print axioms m2_buses
#print axioms rowFactsSegMap_m2
#print axioms wasm_base_sound_m2

end WasmBase
