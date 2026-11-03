import WasmBase.Main.SegSoundX

/-!
# WasmBase.Main.SegLinkage — the linking premises of `seg_sound` (E2E M4c, CORE)

`seg_sound` names four trace-level premises that are not bus balances: `HostBLinked` (two fields),
`RegCLinked`, `CodeOK`, `FuncOK`.  This file settles which follow from `HoldsX` of the current
segment AIR.

## `HostBLinked.unique` — a theorem (`hostB_unique`)

Two active HOST rows with the same `ts` are the same row: every action row's input STATE time is
its position on the STATE chain (`seg_hst`, `chain`, `path_levels`), and distinct rows have distinct
positions (`seg_lvl_inj`; the chain is a permutation of the action rows, `perm_map_lift`).  A HOST
row's STATE time is its `ts` column.  So `HostBLinked` reduces to its `linked` field
(`HostBLinkedL`, `hostBLinked_of`), using only the row facts' `tsOut` and the size bound that
`seg_sound` already has.

## `HostBLinked.linked`, `RegCLinked` — not consequences of `HoldsX`

No bus carries a `HOSTB` row's or a `REG-C` row's call key `(ts, hid)` to a HOST row:
* `HOSTB` (table 25) talks on bus 210 (`busHostB`: for `reg = 0` a send/receive pair of the same
  message with the same count — a self-cancellation —, for `reg = 1` a send received by `REG-C`), on
  CH (the request byte's memory read/re-produce pair), and on R16/BYTE.  HOST (22) talks to `HOSTO`
  on 208/209 (`HOSTQ`/`HOSTR`) and to `REG-C` on 211 (`busRegRd`).  So a `HOSTB` group whose key
  matches no HOST row satisfies every constraint and every bus (e.g. a response group `dir = 1`,
  `reg = 0`, placed as its own group `f = 1` in a padding slot: its bus-210 pair cancels, its
  BYTE/R16 lookups are absorbed by the lookup tables' multiplicity witnesses, it has no CH traffic).
* `REG-C` (27) receives on 211 only on `wr` rows (`act·kind·wr`, message `[ts, rid, 0, ptr, 0]`:
  no `hid`), and its other rows talk only to `HOSTB` (210) and CH.  So a register group with a
  foreign key is likewise unconstrained.

**Minimal AIR change that makes both derivable** (proposal, not applied): a call-key lookup bus
`busHKey` (new id, e.g. 212) with
* HOST (table 22, `HostG`): one new column `nk` with the constraint `(1 − act)·nk = 0` and the
  interaction `⟨busHKey, false, v nk, [v cTs, v Host.hid]⟩` (HOST *offers* its key with a witness
  multiplicity, as `CIDMAP`'s `mm`);
* HOSTB (25): `⟨busHKey, true, v act, [v HostB.ts, v HostB.hid]⟩` (or count `memCnt` if only the
  CH-active request bytes need linking — that is all `hostb_partition` uses);
* REG-C (27): `⟨busHKey, true, v Reg.act, [v Reg.ts, v Reg.hid]⟩`.
The balance (counts of each key summed over rows, all heights `< 2^24`, so no wrap) gives: a key sent
by an active HOSTB/REG-C row is offered by a HOST row with `nk ≠ 0`, which is active; that is
`linked` for both.  `unique` is `hostB_unique`.  Honest prover: `nk` = number of active HOSTB +
REG-C rows of the call (one `HashMap` count in `tracegen.rs`).  Degree: unchanged (counts are
columns).

## `CodeOK`, `FuncOK` — the verifier's cached-commitment check

CODE (17) and FUNC (21) are **cached** tables: their contents are whatever matrix the proof's cached
commitment opens to; `HoldsX` constrains nothing in them except the bus multiplicities.  The verifier
(`native/wasm-base/src/main.rs:check_code_root`) recomputes `code_root`/`func_root` from the
contract code as commitments to the canonical matrices (`tracegen.rs:code_rows`, `func_rows`: the
records / function-table rows in order, padded to a power of two by repeating the last row) and
compares them with the proof's cached commitments.  Under the binding of the commitment that is
exactly `CodeIs X tr` / `FuncIs X tr` below (row `r` is record `min r (len − 1)`), and
`codeOK_of_codeIs` / `funcOK_of_funcIs` reduce `CodeOK`/`FuncOK` to it.  So the premise is the
verifier-side fact "the cached matrix is the canonical one", nothing else.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Distinct action rows have distinct STATE times -/

/-- **Row times are injective** on the action list of a segment trace: the STATE chain visits every
row once, at time `t_in + 1 + k` for its position `k`. -/
theorem seg_lvl_inj {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P) :
    ∀ ρ ∈ actListM2 tr pub, ∀ ρ' ∈ actListM2 tr pub, lvl (rowInM tr pub ρ) = lvl (rowInM tr pub ρ') → ρ = ρ' := by
  have hP := P_val
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
  obtain ⟨rs, hrs, rfl⟩ := perm_map_lift g es act hes
  have hlenrs : rs.length = act.length := hrs.length_eq
  have hal : act.length = (actListM2 tr pub).length := rfl
  obtain ⟨lk, -⟩ := path_levels lvl (rs.map g) _ _ hpath (fun e he => hstepE e (hes.subset he))
  simp only [List.length_map, List.getElem_map] at lk
  have e0 : lvl (segM0 tr pub) = (((pub.getD pubTIn 0).toNat + 1 : Nat) : F) := by
    rw [segM0_eq, Lean.Grind.Semiring.natCast_add, Fp.cast_toNat]; rfl
  have lvlk : ∀ k (hk : k < rs.length), lvl (rowInM tr pub rs[k]) =
      (((pub.getD pubTIn 0).toNat + 1 + k : Nat) : F) := by
    intro k hk
    rw [show rowInM tr pub rs[k] = (g rs[k]).1 from rfl, lk k hk, e0, ← Lean.Grind.Semiring.natCast_add]
  intro ρ hρ ρ' hρ' hl
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hrs.symm.subset hρ)
  obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem (hrs.symm.subset hρ')
  rw [lvlk k hk, lvlk k' hk'] at hl
  have := congrArg Fp.toNat hl
  rw [Fp.toNat_cast_of_lt (by omega), Fp.toNat_cast_of_lt (by omega)] at this
  have : k = k' := by omega
  subst this; rfl

#print axioms seg_lvl_inj

/-! ## 2. `HostBLinked.unique` -/

theorem host_mem_actListM2 {tr : Trace} {pub : List F} {r : Nat} (hr : r < tr.height 22)
    (ha : rowAct Host.table tr pub 22 r) : (22, r) ∈ actListM2 tr pub := by
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  simp only [hostActRows, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨r, ⟨hr, ha⟩, rfl⟩

theorem host_lvl (tr : Trace) (pub : List F) (r : Nat) :
    lvl (rowInM tr pub (22, r)) = ((rowNat tr 22 r cTs : Nat) : F) := by
  rw [show rowInM tr pub (22, r) = rowIn Host.table tr pub 22 r from rfl, ← cell_cast]
  show (rowIn Host.table tr pub 22 r).getD 1 0 = _
  rw [← stE_eval]; rfl

/-- **`HostBLinked.unique` from the STATE chain**: two active HOST rows with the same `ts` are the
same row (the `hid` equality is not even needed). -/
theorem hostB_unique {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P) :
    ∀ r r', r < tr.height 22 → rowAct Host.table tr pub 22 r →
      r' < tr.height 22 → rowAct Host.table tr pub 22 r' →
      rowNat tr 22 r cTs = rowNat tr 22 r' cTs → rowNat tr 22 r Host.hid = rowNat tr 22 r' Host.hid →
      r = r' := by
  intro r r' hr ha hr' ha' hts' _
  have := seg_lvl_inj H hts hsz _ (host_mem_actListM2 hr ha) _ (host_mem_actListM2 hr' ha')
    (by rw [host_lvl, host_lvl, hts'])
  simpa using this

/-- The `linked` half of `HostBLinked` (the part that is not a consequence of `HoldsX`). -/
def HostBLinkedL (tr : Trace) (pub : List F) : Prop :=
  ∀ r', r' < tr.height 25 → rowAct HostB.table tr pub 25 r' →
    ∃ r, r < tr.height 22 ∧ rowAct Host.table tr pub 22 r ∧
      rowNat tr 25 r' HostB.ts = rowNat tr 22 r cTs ∧
      rowNat tr 25 r' HostB.hid = rowNat tr 22 r Host.hid

/-- **`HostBLinked` from its `linked` half** on a segment trace. -/
theorem hostBLinked_of {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1)
    (hsz : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 < P)
    (hL : HostBLinkedL tr pub) : HostBLinked tr pub :=
  ⟨hL, hostB_unique H hts hsz⟩

#print axioms hostB_unique
#print axioms hostBLinked_of

/-! ## 3. `CodeOK` / `FuncOK` from the canonical cached matrices -/

/-- **The cached CODE matrix is the canonical one** (what V_d's `code_root` check establishes under
the commitment's binding): row `r` is the global record `min r (codeSize − 1)` (the records in pc
order, padded by repeating the last). -/
def CodeIs (X : Ctx) (tr : Trace) : Prop :=
  0 < X.M.codeSize ∧ ∀ r, r < tr.height 17 →
    (List.range Boundary.recWidth).map (fun k => tr.cell 17 r k) = codeRec X (min r (X.M.codeSize - 1))

/-- **The cached FUNC matrix is the canonical one**: row `r` is the function-table row
`min r (nf − 1)`. -/
def FuncIs (X : Ctx) (tr : Trace) : Prop :=
  0 < X.nf ∧ ∀ r, r < tr.height 21 → (List.range 8).map (fun i => tr.cell 21 r i) = funcRec X (min r (X.nf - 1))

theorem codeOK_of_codeIs {X : Ctx} {tr : Trace} (h : CodeIs X tr) : CodeOK X tr :=
  fun r hr => ⟨min r (X.M.codeSize - 1), by have := h.1; omega, h.2 r hr⟩

theorem funcOK_of_funcIs {X : Ctx} {tr : Trace} (h : FuncIs X tr) : FuncOK X tr :=
  fun r hr => ⟨min r (X.nf - 1), by have := h.1; omega, h.2 r hr⟩

#print axioms codeOK_of_codeIs
#print axioms funcOK_of_funcIs

end WasmBase
