import WasmBase.Main.HostCodeFetch

/-!
# WasmBase.Main.HostRowsTimesAir — producer/consumer times of a HOST row's fused traffic (E2E M6, COVER item 1d)

`HostRowsTimes` (`Main/HostIfCover.lean`) bundles three AIR facts about a HOST row's fused CH traffic
(its own argument/result messages, its `HOSTB` bytes, its REG-C net traffic, its gas register):

1. every consumed message was produced earlier: `tp + 1 + n ≡ ts` with `n < 2^30 + 2^16`
   (**`host_cons_times`**, from the `timeChk` pairs of HOST (arguments, `pf j`), `HOSTB` (`memCnt`),
   REG (`act·fresh` for register bytes/lengths, `wcnt` for memory writes) and the gas register (`act`),
   the `HOSTB`/REG rows' `ts` being the call's by their `(ts, hid)` group key);
2. every produced message carries the row's time `ts` (**`host_prod_times`**: every CH send of the four
   tables has the `ts` column as its producer time, `SendTs`, by `decide`);
3. the produced messages are pairwise distinct — **not** derived here: `HostProdNodup` stays named.
   It is a real completeness restriction of the MEMIO link: two request bytes of one call at the same
   address (two overlapping request buffers, e.g. `storage_write` with key and value at the same
   pointer) both consume the live byte at `mtp` and both re-produce it at `ts`; the second consumption
   has no producer (a re-production at `ts` cannot be consumed at `ts`: `timeChk` forces `mtp < ts`),
   so an honest trace of such a call does not balance — overlapping request buffers are outside the
   AIR's domain.  For calls with disjoint request buffers the productions are distinct (different
   spaces/addresses/register slots), which is what the honest prover must ensure.

**`hostRowsTimes_of`**: `HostRowsTimes` from `HoldsX` + the grouping premises + `HostProdNodup`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostIf
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace}

/-! ## 1. The generic time check -/

/-- **A `timeChk` pair with count 1 on a row of the segment AIR** gives `tp + 1 + n ≡ ts`. -/
theorem seg_tchk (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {t r : Nat}
    (ht : t < (wasmBaseSegAir nloc ngl).tables.length) (hr : r < tr.height t) {tsE tpE hiE c : Expr}
    (h1 : r16 (tsE - tpE - 1 - 65536 * hiE) c ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters)
    (h2 : r16 (4 * hiE) c ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters)
    (hc : (c.eval (tr.row pub t r)).toNat = 1) :
    ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ (((tpE.eval (tr.row pub t r)).toNat + 1 + n : Nat) : F) = tsE.eval (tr.row pub t r) := by
  have o1 := row_occ (pub := pub) ht hr h1
  have o2 := row_occ (pub := pub) ht hr h2
  simp only [r16, List.map_cons, List.map_nil, Expr.eval_sub', Expr.eval_mul', Expr.eval_ofNat', hc] at o1 o2
  obtain ⟨n, hn, he⟩ := seg_time_chk H o1 o2
  exact ⟨n, hn, he⟩

theorem decMsg_tp_of_last {l : List F} {e : F} (h8 : l.length = 8) (hl : l.getLast? = some e) :
    (decMsg l).tp = e.toNat := by
  match l, h8 with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hl
    subst hl; rfl

/-! ## 2. Produced times -/

/-- Every CH send of `T` has 8 message fields, the last being the column `c`. -/
def SendTs (T : Table) (c : Nat) : Bool :=
  T.inters.all fun i => !(decide (i.bus = busStk) && i.send) ||
    (decide (i.msg.length = 8) && decide (i.msg.getLast? = some (v c)))

theorem sendTs_host : SendTs Host.table cTs = true := by decide +kernel
theorem sendTs_hostb : SendTs HostB.table HostB.ts = true := by decide +kernel
theorem sendTs_regw : SendTs RegW.table Reg.ts = true := by decide +kernel
theorem sendTs_gas : SendTs GasT cTs = true := by decide +kernel
theorem sendTs_hostbw : SendTs HostBW HostB.ts = true := by decide +kernel

theorem sendTs_rowProd {T : Table} {c : Nat} (hS : SendTs T c = true) {t r : Nat} {x : Msg}
    (hx : x ∈ rowProd T tr pub t r) : x.tp = rowNat tr t r c := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, hi, hb, hs, -, rfl⟩ := mem_rowMsgs_cnt hm
  have h := List.all_eq_true.mp hS i hi
  simp only [hb, hs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h8, hl⟩ := h
  rw [decMsg_tp_of_last (by simp [h8]) (by rw [List.getLast?_map, hl]; rfl)]
  simp only [v, Expr.eval_col, Trace.row]
  rfl

/-- **Produced times** (part 2 of `HostRowsTimes`). -/
theorem host_prod_times (r : Nat) :
    ∀ x ∈ prodCHS tr pub (22, r), x.tp < P ∧ ((x.tp : Nat) : F) = lvl (rowInM tr pub (22, r)) := by
  intro x hx
  rw [host_lvl]
  suffices h : x.tp = rowNat tr 22 r cTs by rw [h]; exact ⟨rowNat_lt tr 22 r _, rfl⟩
  simp only [prodCHS, prodCHM2, rowProdM, hostbProdH, regProdH, gasProdH, hbwProdH, chipTM2, ite_true,
    List.mem_append] at hx
  rcases hx with (((hx | hx | hx) | hx) | hx)
  · exact sendTs_rowProd sendTs_host hx
  · unfold hostbProdOf at hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    rw [sendTs_rowProd sendTs_hostb hx]
    exact (List.mem_filter.mp hr').2 |> fun h => by simpa using (of_decide_eq_true h).1
  · unfold regProdOf at hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    unfold regNetProd at hx
    split at hx
    · simp at hx
    · rw [sendTs_rowProd sendTs_regw hx]
      have := (List.mem_filter.mp hr').2
      simp only [regKey, hostKey, Prod.mk.injEq, decide_eq_true_eq] at this
      exact this.1
  · exact sendTs_rowProd sendTs_gas hx
  · unfold hbwProdOf at hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    rw [sendTs_rowProd sendTs_hostbw hx]
    exact (List.mem_filter.mp hr').2 |> fun h => by simpa using (of_decide_eq_true h).1

end

#print axioms seg_tchk
#print axioms host_prod_times

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace}

/-! ## 3. Consumed times -/

theorem regc_cKind_mem : Reg.cKind ∈ RegC.table.constraints :=
  List.mem_append_left _ (List.mem_append_left _ (by simp [Reg.constraints]))
theorem regc_cFresh_mem : Reg.cFresh ∈ RegC.table.constraints :=
  List.mem_append_left _ (List.mem_append_left _ (by simp [Reg.constraints]))


theorem prod3_toNat {a c : Nat} (ha : a = 0 ∨ a = 1) (hc : c = 0 ∨ c = 1) (y : F)
    (h : (((a : Nat) : F) * y * ((c : Nat) : F)).toNat = 1) : (((a : Nat) : F) * ((c : Nat) : F)).toNat = 1 := by
  rcases ha with rfl | rfl
  · rw [cast_zero, Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.zero_mul] at h
    exact absurd h (by rw [toNat_zero']; decide)
  · rcases hc with rfl | rfl
    · rw [cast_zero, Lean.Grind.Semiring.mul_zero] at h
      exact absurd h (by rw [toNat_zero']; decide)
    · rw [cast_one, Lean.Grind.Semiring.mul_one]; rfl

/-- A consumed message of a row decoded from a known recv inter list. -/
theorem recv_tp {T : Table} {t r : Nat} {x : Msg} (hx : x ∈ rowCons T tr pub t r)
    (L : List Inter) (hL : T.inters.filter (fun i => i.bus = busStk ∧ i.send = false) = L) :
    ∃ i ∈ L, (i.count.eval (tr.row pub t r)).toNat = 1 ∧ x = decMsg (i.msg.map (·.eval (tr.row pub t r))) := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, hi, hb, hs, hc, rfl⟩ := mem_rowMsgs_cnt hm
  refine ⟨i, ?_, hc, rfl⟩
  rw [← hL]; exact List.mem_filter.mpr ⟨hi, by simp [hb, hs]⟩

theorem ev_v (t r c : Nat) : (v c).eval (tr.row pub t r) = tr.cell t r c := by
  simp only [v, Expr.eval_col, Trace.row]

/-- The time bound of a `timeChk` against the row's `ts` column, transported to the call's time. -/
theorem tchk_to {t r' c tsc : Nat} {r : Nat} (hts : rowNat tr t r' tsc = rowNat tr 22 r cTs) {n : Nat}
    (he : (((Expr.eval (tr.row pub t r') (v c)).toNat + 1 + n : Nat) : F) = Expr.eval (tr.row pub t r') (v tsc)) :
    (((rowNat tr t r' c) + 1 + n : Nat) : F) = tr.cell 22 r cTs := by
  rw [ev_v, ev_v] at he
  have e : tr.cell t r' tsc = tr.cell 22 r cTs := by rw [cell_cast, cell_cast, hts]
  rw [e] at he; exact he

/-- **Consumed times** (part 1 of `HostRowsTimes`). -/
theorem host_cons_times (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {r : Nat} (hA : HAct tr pub r) :
    ∀ x ∈ consCHS tr pub (22, r), ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧
      ((x.tp + 1 + n : Nat) : F) = lvl (rowInM tr pub (22, r)) := by
  have hP := P_val
  intro x hx
  rw [host_lvl, ← cell_cast]
  have ht22 : 22 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have ht25 : 25 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have ht27 : 27 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have in22 : ∀ i, i ∈ HostG.inters → i ∈ ((wasmBaseSegAir nloc ngl).tables[22]'ht22).inters := by
    intro i hi; rw [seg_t22]; exact hi
  have in25 : ∀ i, i ∈ Seg.HostBK.inters → i ∈ ((wasmBaseSegAir nloc ngl).tables[25]'ht25).inters :=
    fun i hi => hi
  have in27 : ∀ i, i ∈ Seg.RegCK.inters → i ∈ ((wasmBaseSegAir nloc ngl).tables[27]'ht27).inters :=
    fun i hi => hi
  simp only [consCHS, consCHM2, rowConsM, hostbConsH, regConsH, gasConsH, hbwConsH, chipTM2, ite_true,
    List.mem_append] at hx
  rcases hx with (((hx | hx | hx) | hx) | hx)
  · -- the HOST row's arguments
    rw [host_row_cons] at hx
    obtain ⟨j, hj, hx⟩ := List.mem_flatMap.mp hx
    by_cases hp : rowNat tr 22 r (Host.pf j) = 1
    · rw [if_pos hp, List.mem_singleton] at hx
      subst hx
      have hmem : ∀ i ∈ timeChk (v cTs) (v (Host.tP j)) (v (Host.hP j)) (v (Host.pf j)), i ∈ HostG.inters := by
        intro i hi
        rw [hostG_inters_eq]
        refine List.mem_append_left _ ?_
        unfold Host.inters
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, hj,
          List.mem_append_right _ hi⟩))
      obtain ⟨n, hn, he⟩ := seg_tchk H ht22 hA.1 (in22 _ (hmem _ List.mem_cons_self))
        (in22 _ (hmem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        (by rw [ev_v]; exact hp)
      exact ⟨n, hn, tchk_to rfl he⟩
    · rw [if_neg hp] at hx; simp at hx
  · -- the call's HOSTB bytes
    unfold hostbConsOf at hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨hr'h, hts, -⟩ := mem_hostbOf.mp hr'
    obtain ⟨i, hi, hc, rfl⟩ := recv_tp hx _ hostb_inters_stk.1
    simp only [List.mem_singleton] at hi
    subst hi
    have hm7 : r16 (v HostB.ts - v HostB.mtp - 1 - 65536 * v HostB.hp) HostB.memCnt ∈ Seg.HostBK.inters :=
      List.mem_of_getElem? (i := 7) (by decide)
    have hm8 : r16 (4 * v HostB.hp) HostB.memCnt ∈ Seg.HostBK.inters :=
      List.mem_of_getElem? (i := 8) (by decide)
    obtain ⟨n, hn, he⟩ := seg_tchk H ht25 hr'h (in25 _ hm7) (in25 _ hm8) hc
    rw [decMsg_tp_of_last (e := (v HostB.mtp).eval (tr.row pub 25 r')) rfl rfl]
    exact ⟨n, hn, by rw [ev_v]; exact tchk_to hts he⟩
  · -- the call's REG-C traffic
    unfold regConsOf at hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    have hkey := (List.mem_filter.mp hr').2
    have hr'h : r' < tr.height 27 := List.mem_range.mp (List.mem_filter.mp hr').1
    simp only [regKey, hostKey, Prod.mk.injEq, decide_eq_true_eq] at hkey
    unfold regNetCons at hx
    obtain ⟨i, hi, hc, rfl⟩ := recv_tp hx _ regw_stk_recv
    have hcon := seg_regc_con H hr'h
    have bAct := regc_bool_of hcon regc_cAct_mem
    have bFresh := regc_bool_of hcon regc_cFresh_mem
    have h5 : r16 (v Reg.ts - v Reg.tp - 1 - 65536 * v Reg.hp) (v Reg.act * v Reg.fresh) ∈ Seg.RegCK.inters :=
      List.mem_of_getElem? (i := 5) (by decide)
    have h6 : r16 (4 * v Reg.hp) (v Reg.act * v Reg.fresh) ∈ Seg.RegCK.inters :=
      List.mem_of_getElem? (i := 6) (by decide)
    have h14 : r16 (v Reg.ts - v RegW.mtp - 1 - 65536 * v RegW.mhp) RegW.wcnt ∈ Seg.RegCK.inters :=
      List.mem_of_getElem? (i := 14) (by decide)
    have h15 : r16 (4 * v RegW.mhp) RegW.wcnt ∈ Seg.RegCK.inters :=
      List.mem_of_getElem? (i := 15) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · -- a register byte
      have hc' : ((v Reg.act * v Reg.fresh).eval (tr.row pub 27 r')).toNat = 1 := by
        simp only [Expr.eval_mul', ev_v, cell_cast]
        refine prod3_toNat bAct bFresh (((1 : Nat) : F) - ((rowNat tr 27 r' Reg.kind : Nat) : F)) ?_
        simpa only [chRecv, Reg.isB, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', ev_v, cell_cast] using hc
      obtain ⟨n, hn, he⟩ := seg_tchk H ht27 hr'h (in27 _ h5) (in27 _ h6) hc'
      rw [decMsg_tp_of_last (e := (v Reg.tp).eval (tr.row pub 27 r')) rfl rfl]
      exact ⟨n, hn, by rw [ev_v]; exact tchk_to hkey.1 he⟩
    · -- a register length
      have hc' : ((v Reg.act * v Reg.fresh).eval (tr.row pub 27 r')).toNat = 1 := by
        simp only [Expr.eval_mul', ev_v, cell_cast]
        refine prod3_toNat bAct bFresh ((rowNat tr 27 r' Reg.kind : Nat) : F) ?_
        simpa only [chRecv, Reg.isL, Expr.eval_mul', ev_v, cell_cast] using hc
      obtain ⟨n, hn, he⟩ := seg_tchk H ht27 hr'h (in27 _ h5) (in27 _ h6) hc'
      rw [decMsg_tp_of_last (e := (v Reg.tp).eval (tr.row pub 27 r')) rfl rfl]
      exact ⟨n, hn, by rw [ev_v]; exact tchk_to hkey.1 he⟩
    · -- a memory write's old byte
      obtain ⟨n, hn, he⟩ := seg_tchk H ht27 hr'h (in27 _ h14) (in27 _ h15) hc
      rw [decMsg_tp_of_last (e := (v RegW.mtp).eval (tr.row pub 27 r')) rfl rfl]
      exact ⟨n, hn, by rw [ev_v]; exact tchk_to hkey.1 he⟩
  · -- the gas register
    unfold gasConsOf at hx
    have hL : GasT.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
        [chRecv (Expr.c spaceGas) 0 (v HostG.gS) (limbsOf HostG.gb) (v HostG.gtp) (v Host.act)] := by decide
    obtain ⟨i, hi, hc, rfl⟩ := recv_tp hx _ hL
    simp only [List.mem_singleton] at hi
    subst hi
    have hm : ∀ i ∈ timeChk (v cTs) (v HostG.gtp) (v HostG.ghi) (v Host.act), i ∈ HostG.inters := by
      intro i hi
      rw [hostG_inters_eq]
      refine List.mem_append_right _ (List.mem_append_right _ ?_)
      unfold hostGExtra
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hi))
    obtain ⟨n, hn, he⟩ := seg_tchk H ht22 hA.1 (in22 _ (hm _ List.mem_cons_self))
      (in22 _ (hm _ (List.mem_cons_of_mem _ List.mem_cons_self))) hc
    rw [decMsg_tp_of_last (e := (v HostG.gtp).eval (tr.row pub 22 r)) rfl rfl]
    exact ⟨n, hn, by rw [ev_v]; exact tchk_to rfl he⟩
  · -- the call's `HOSTB` memory writes (A-T1): the old byte, consumed at `mtp < ts`
    unfold hbwConsOf at hx
    obtain ⟨r', hr', hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨hr'h, hts, -⟩ := mem_hostbOf.mp hr'
    have hL : HostBW.inters.filter (fun i => i.bus = busStk ∧ i.send = false) =
        [chRecv 3 HostB.memAddr 0 [v HostBK.ob, 0, 0, 0] (v HostB.mtp) HostBK.wcnt] := by decide
    obtain ⟨i, hi, hc, rfl⟩ := recv_tp hx _ hL
    simp only [List.mem_singleton] at hi
    subst hi
    have hm18 : r16 (v HostB.ts - v HostB.mtp - 1 - 65536 * v HostB.hp) HostBK.wcnt ∈ Seg.HostBK.inters :=
      List.mem_of_getElem? (i := 18) (by decide)
    have hm19 : r16 (4 * v HostB.hp) HostBK.wcnt ∈ Seg.HostBK.inters :=
      List.mem_of_getElem? (i := 19) (by decide)
    obtain ⟨n, hn, he⟩ := seg_tchk H ht25 hr'h (in25 _ hm18) (in25 _ hm19) hc
    rw [decMsg_tp_of_last (e := (v HostB.mtp).eval (tr.row pub 25 r')) rfl rfl]
    exact ⟨n, hn, by rw [ev_v]; exact tchk_to hts he⟩

/-- **The produced messages of a HOST row are pairwise distinct** (named; see the header). -/
def HostProdNodup (tr : Trace) (pub : List F) : Prop :=
  ∀ r, HAct tr pub r → (prodCHS tr pub (22, r)).Nodup

/-- **`HostRowsTimes` from the segment AIR** + `HostProdNodup`. -/
theorem hostRowsTimes_of (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hnd : HostProdNodup tr pub) :
    HostRowsTimes tr pub :=
  fun r hA => ⟨host_cons_times H hA, host_prod_times r, hnd r hA⟩

end

#print axioms host_cons_times
#print axioms hostRowsTimes_of

/-! ## 4. Segment soundness, HOST premises down to the producer contract -/

/-- **`seg_sound_hostIf_air`**: `seg_sound_hostIf''` with every AIR-side HOST premise discharged
(`HostCodeT`, `HostFeeOK` by the FETCH link; `HostRowsTimes` but its no-duplicate part).  Remaining:
the producer contract `HostIf` + `HostAnsCov`; `HostCallsNotLinear` (static module fact);
`HostWritesCovT` (write coverage — fails for the `setU128H` arms, AIR gap); `HostProdNodup`
(distinct productions — fails for overlapping request buffers, AIR domain restriction). -/
theorem seg_sound_hostIf_air (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {hts : List Nat} {σc : Nat → St} {np : Nat} (hI : HostIf X.toCtx tr pub sg hts σc)
    (hans : HostAnsCov X.toCtx tr pub sg hts σc np) (hlin : HostCallsNotLinear X.toCtx)
    (hwr : HostWritesCovT X.toCtx tr pub sg (thread hts σc) np) (hnd : HostProdNodup tr pub)
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
      (initS tr pub)) (hw0 : RegWF s0) (hσ0 : sideR s0 = σc 0) (hp0 : s0.pages.size = np) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ sideR sN = σc hts.length ∧ sN.pages.size = np :=
  seg_sound_hostIf_fetch X H hC hl hcode hfunc hb hg hkeep hI hans hlin hwr (hostRowsTimes_of H hnd)
    hst0 hlen htin hfeeN hstepgas hg64 hinit hT h0 hw0 hσ0 hp0

#print axioms seg_sound_hostIf_air

end WasmBase
