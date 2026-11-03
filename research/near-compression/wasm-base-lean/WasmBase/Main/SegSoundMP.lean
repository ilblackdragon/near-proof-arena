import WasmBase.Main.SegS.SegSoundX
/-!
# WasmBase.Main.SegSoundMP — segment soundness for the multiproof AIR (E2E M4c, sub-lane MP)

**`seg_sound_mp`**: `seg_sound` (`Main/SegSoundX.lean`) for `wasmBaseSegAirMP` (`SegAirMP.lean`: the
M4 segment AIR with table 20, `MPATH`, replaced by the batched Merkle multiproof).  Same named
premises, same conclusion; `HoldsX`/`ChipIf` are those of the multiproof AIR.

## How

`seg_sound` uses nothing about table 20 or the buses 15, 16, 17, 103 except the bus-103 receives of
the CUT streams (tables 30/31).  `Main/SegHoldsS.lean` isolates that part of the relation:

* `HoldsXS nloc ngl pub tr` — `HoldsX (wasmBaseSegAir …)` without table 20's constraints and without
  the balance / load bound of the buses 15, 16, 17, 103 (`OkBus`).  `HoldsX.toS` (M4 AIR) and
  `HoldsX.toSMP` (MP AIR: `segMP_same` for the tables, `occs_filter_bus` / `segMP_busNat` /
  `segMP_busLoad` for the buses) both give it;
* `SegSha.ChipIfS compress nloc ngl pub tr chip` — the chip contract, the id bound, and "every bus-103
  receive with count 1 of a table `≠ 20` is a chip message".  `SegSha.ChipIf.toS` (M4 AIR, by
  `if_recv_mem`) and `ChipIf.toSMP` (here: the MP AIR's bus 103 has no sends and bit counts,
  `segMP_if_bits`, including the multiproof's node compressions `act`, `act·(1 − ro)`) give it.

The `seg_sound` chain (≈ 115 declarations of `SegRows`, `SegMemb`, `SegSend`, `SegCuto`, `SegLink`,
`SegSha*`, `SegCutWords`, `SegSound`, `SegBus`, `SegRowsX`, `SegRegKeep`, `SegSoundX`) is restated
from `HoldsXS`/`ChipIfS` in `Main/SegS/*.lean` (names `fooS`; the proofs are the originals', with
`t ≠ 20` discharged by the instance `SegT t` and `OkBus b` by `decide`).  `seg_soundS` is the result;
`seg_sound_mp` and `seg_sound_viaS` (the M4 AIR again, as a check) are one-line instances.

## Porting a lemma stated from `HoldsX (wasmBaseSegAir …)`

If its proof uses `H` only through the chain lemmas and generic `HoldsX` lemmas (constraints of
tables `≠ 20`, balance of buses `∉ {15, 16, 17, 103}`), restate it with `(H : HoldsXS nloc ngl pub tr)`
(and `SegSha.ChipIfS` for `ChipIf`), replace each used lemma `foo` by `fooS`, `table_constr_eqX` by
`table_constr_eqXS` etc. (a table index needs an instance `SegT t`: automatic for literals, otherwise
`have : SegT t := ⟨by omega⟩`), and get both AIRs by `H.toS` / `H.toSMP` (`hC.toS H` / `hC.toSMP H`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace SegSha

theorem mpathMP_if_bits :
    MpathMP.table.inters.all (fun i => i.bus != 103 ||
      (!i.send && BitS (bcOf MpathMP.table) (beOf MpathMP.table) i.count)) = true := by
  decide +kernel

/-- Bus 103 at a table `≠ 20`, from `HoldsXS`: a receive with a bit count. -/
theorem seg_if_bitsS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) (h20 : t ≠ 20) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters) (hb : i.bus = extBus) :
    i.send = false ∧ (i.count.eval (tr.row pub t r)).toNat ≤ 1 := by
  obtain ⟨hs, htt⟩ := seg_if_shape nloc ngl t ht i hi hb
  refine ⟨hs, ?_⟩
  have bit_le : ∀ x : F, x = 0 ∨ x = 1 → x.toNat ≤ 1 := by
    intro x hx; rcases hx with rfl | rfl <;> decide
  rcases htt with rfl | rfl | rfl | rfl
  · have hc := List.all_eq_true.mp memb_if_bits i (by rw [← seg_t19 nloc ngl]; exact hi)
    simp only [hb, extBus, bne_self_eq_false, Bool.false_or] at hc
    exact bit_le _ (bitS_soundS H ht hr i.count (by rw [seg_t19]; exact hc))
  · exact absurd rfl h20
  · have hc := List.all_eq_true.mp cuti_if_count i (by rw [← seg_t30 nloc ngl]; exact hi)
    simp only [hb, extBus, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at hc
    rw [hc]; exact bit_le _ (cut_kDkP_rowS H (Or.inl rfl) hr)
  · have hc := List.all_eq_true.mp cuto_if_count i (by rw [← seg_t31' nloc ngl]; exact hi)
    simp only [hb, extBus, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at hc
    have eIO : Cut.c Cut.Out.cols "kD" + Cut.c Cut.Out.cols "kP" = Cut.c Cut.In.cols "kD" + Cut.c Cut.In.cols "kP" := by
      decide
    rw [hc, eIO]; exact bit_le _ (cut_kDkP_rowS H (Or.inr rfl) hr)

/-- **Bus 103 of the multiproof AIR**: every occurrence is a receive with a bit count (the
multiproof's node compressions count `act` and `act·(1 − ro)`, bits by MPATH's constraints). -/
theorem segMP_if_bits {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr) :
    ∀ o ∈ occs (wasmBaseSegAirMP nloc ngl) tr pub, o.1 = extBus → o.2.1 = false ∧ o.2.2.2 ≤ 1 := by
  intro o ho hb
  obtain ⟨t, ht, r, hr, i, hi, rfl⟩ := mem_occs.mp ho
  simp only at hb ⊢
  by_cases h20 : t = 20
  · subst h20
    have e1 : (wasmBaseSegAirMP nloc ngl).tables[20]'ht = MpathMP.table := by
      have := segMP_t20 nloc ngl
      rw [List.getElem?_eq_getElem ht] at this
      exact Option.some.inj this
    have hc := List.all_eq_true.mp mpathMP_if_bits i (by rw [← e1]; exact hi)
    simp only [hb, extBus, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hc
    refine ⟨hc.1, ?_⟩
    rcases bitS_sound H.toC ht hr i.count (by rw [e1]; exact hc.2) with h | h <;> rw [h] <;> decide
  · have ht' : t < (wasmBaseSegAir nloc ngl).tables.length := by rw [← segMP_len']; exact ht
    rw [segMP_tab nloc ngl t h20 ht ht'] at hi
    exact seg_if_bitsS H.toSMP ht' h20 hr hi hb

/-- No table of the multiproof AIR sends on bus 103. -/
theorem segMP_if_send_zero {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
    (m : List F) : busNat (wasmBaseSegAirMP nloc ngl) tr pub extBus true m = 0 :=
  busNat_zero fun o ho hb hs _ => absurd hs (by rw [(segMP_if_bits H o ho hb).1]; decide)

/-- **`ChipIf` of the multiproof AIR implies `ChipIfS`.** -/
theorem ChipIf.toSMP {compress : List Nat → List Nat → List Nat} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {chip : List IfMsg} (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr)
    (hC : ChipIf compress (wasmBaseSegAirMP nloc ngl) pub tr chip) : ChipIfS compress nloc ngl pub tr chip where
  contract := hC.contract
  cidLt := hC.cidLt
  recv t ht h20 r hr i hi hb hc := by
    have ht' : t < (wasmBaseSegAirMP nloc ngl).tables.length := by rw [segMP_len']; exact ht
    rw [← segMP_tab nloc ngl t h20 ht' ht] at hi
    have ho := occ_of_inter ht' hr hi hc
    have hbits := segMP_if_bits H
    have hs : i.send = false := (hbits _ ho hb).1
    have hge := count_le_busNat ho hb hs rfl
    have hlt := busNat_ltX H extBus false (i.msg.map (·.eval (tr.row pub t r)))
      (fun o ho hb _ => (hbits o ho hb).2)
    have hbal := hC.balance (i.msg.map (·.eval (tr.row pub t r)))
    rw [segMP_if_send_zero H, Nat.add_zero, Nat.mod_eq_of_lt hlt] at hbal
    refine List.count_pos_iff.mp ?_
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, Nat.zero_mod] at hbal
    simp only at hge
    omega

end SegSha

/-- **`seg_sound_mp`: segment soundness (cut case) for the multiproof segment AIR.**  `seg_sound`'s
statement with `HoldsX (wasmBaseSegAirMP …)` and `ChipIf compressW (wasmBaseSegAirMP …)`: same named
premises (see `Main/SegSoundX.lean`), same conclusion. -/
theorem seg_sound_mp (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hrely : HostRely X.toCtx tr pub)
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
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      ∀ y ∈ cutView X.toCtx sN, MsgWF y :=
  seg_soundS X H.toSMP (SegSha.ChipIf.toSMP H hC) hl hcode hfunc hb hg hkeep hhold hrely hst0 hlen htin hfeeN
    hstepgas hg64 hinit hT h0 hw0

/-- The M4 AIR through `HoldsXS` (a check that `seg_soundS` is `seg_sound`'s generalisation). -/
theorem seg_sound_viaS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (hrely : HostRely X.toCtx tr pub)
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
      (initS tr pub)) (hw0 : RegWF s0) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      ∀ y ∈ cutView X.toCtx sN, MsgWF y :=
  seg_soundS X H.toS (SegSha.ChipIf.toS H hC) hl hcode hfunc hb hg hkeep hhold hrely hst0 hlen htin hfeeN
    hstepgas hg64 hinit hT h0 hw0

#print axioms HoldsX.toSMP
#print axioms SegSha.ChipIf.toSMP
#print axioms seg_soundS
#print axioms seg_sound_mp
#print axioms seg_sound_viaS

end WasmBase
