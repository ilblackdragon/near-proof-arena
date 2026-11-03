import WasmBase.Main.HostIfCover2

/-!
# WasmBase.Main.HostCodeFetch — the HOST row's code facts from its FETCH link (E2E M6, COVER item 1d)

The HOST row looks up `[pc, opHost, h, fee, hid, np, ar, 0]` on the FETCH bus (count `act`).  With
`CodeOK` the message is a global code record (`seg_fetchM2`), and a record with opcode `opHost` is
`recordAtM2`'s record of a `call fi` of an import whose name has a HOST-chip entry
(`recordAtM2_host_op`).  Hence, at an active HOST row:

* **`hostFeeOK_of`** — `HostFeeOK` (the fee column is a record fee, `≤ maxFee`): a theorem;
* **`hostCodeT_of`** — `HostCodeT` (the call is a `call` of an import `name` that is a `hostCall`
  arm with `nargs name ≤ np`; at every related pre-state `h = size − sb` and `np ≤ size`), relative
  only to the static module fact **`HostCallsNotLinear`** (a host call's gas entry is not of the
  `linear` kind; the M2 checker's `feeUnits` only checks `fee.l = 0`, so the kind is not pinned by
  the record).  The table facts are by `decide`: every HOST-chip entry of `hostFnsM2` is a
  `hostCall` arm with `nargs = np` (`chipEntries_arm`), and its names are distinct (`hostFnsM2_nodup`,
  so `hostChipM2` and `hostAnyM2` agree, which gives `np ≤ h` from `verifyAtM2`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot TwoRun HostIf
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. The host table -/

/-- The HOST-chip entries of the M2 host table. -/
def chipEntries : List (Nat × String × Nat × Nat) :=
  hostFnsM2.filter (fun x => Chips.hostShapeOk x.2.2.1 x.2.2.2 && Chips.hostArgsI64 x.2.1 && hostResI64 x.2.1)

theorem chipEntries_arm : ∀ x ∈ chipEntries, (hostCall x.2.1).isSome = true ∧ nargs x.2.1 ≤ x.2.2.1 ∧
    x.2.2.1 ≤ 9 := by
  decide +kernel

theorem hostFnsM2_nodup : (hostFnsM2.map (·.2.1)).Nodup := by decide +kernel

theorem find_key_unique {l : List (Nat × String × Nat × Nat)} (hnd : (l.map (·.2.1)).Nodup)
    {x y : Nat × String × Nat × Nat} (hx : x ∈ l) (hy : y ∈ l) (h : x.2.1 = y.2.1) : x = y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd ⟨y, hy', h.symm⟩ hnd.1
    · exact absurd ⟨x, hx', h⟩ hnd.1
    · exact ih hnd.2 hx' hy'

/-- **A HOST-chip name**: an arm of `hostCall`, `nargs ≤ np ≤ 9`, and `hostAnyM2` agrees. -/
theorem hostChipM2_facts {name : String} {hid np ar : Nat} (h : hostChipM2 name = some (hid, np, ar)) :
    (hostCall name).isSome = true ∧ nargs name ≤ np ∧ np ≤ 9 ∧ hostAnyM2 name = some (np, ar) := by
  unfold hostChipM2 at h
  obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.mp h
  have hxm := List.mem_of_find?_eq_some hx
  have hxp := List.find?_some hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hxp
  obtain ⟨⟨⟨hn, hs⟩, ha⟩, hr⟩ := hxp
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨-, rfl, rfl⟩ := hxe
  have hce : x ∈ chipEntries := List.mem_filter.mpr ⟨hxm, by simp [hs, ha, hr, hn]⟩
  obtain ⟨a1, a2, a3⟩ := chipEntries_arm x hce
  rw [← hn]
  refine ⟨a1, a2, a3, ?_⟩
  unfold hostAnyM2
  have hf : ∃ y, hostFnsM2.find? (fun y => y.2.1 = x.2.1) = some y := by
    cases hq : hostFnsM2.find? (fun y => y.2.1 = x.2.1) with
    | some y => exact ⟨y, rfl⟩
    | none =>
      have := List.find?_eq_none.mp hq x hxm
      simp at this
  obtain ⟨y, hy⟩ := hf
  have hym := List.mem_of_find?_eq_some hy
  have hyp := List.find?_some hy
  simp only [decide_eq_true_eq] at hyp
  rw [hy, find_key_unique hostFnsM2_nodup hym hxm hyp]
  rfl

/-! ## 2. Records with the host opcode -/

/-- **The FETCH converse for host calls**: a record with opcode `opHost` is the record of a `call` of
an import with a HOST-chip entry. -/
theorem recordAtM2_host_op {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) (hop : rec.getD 1 0 = Chips.opHost) :
    ∃ fi name hid np ar fee, pf.code[pc]? = some (.call fi) ∧ fi < p.m.imports.size ∧
      importName p fi = some name ∧ hostChipM2 name = some (hid, np, ar) ∧
      feeUnits cfg pf.gas[pc]? = some fee ∧ rec = [off + pc, Chips.opHost, H[pc]?.getD 0, fee, hid, np, ar, 0] := by
  unfold recordAtM2 at hr
  repeat' split at hr
  all_goals first
    | (have := recordOf_op_lt_opIf hr; rw [hop] at this; simp [IfC.opIf, Chips.opHost] at this; done)
    | (simp at hr; done)
    | (simp only [Option.some.injEq] at hr; subst hr
       simp_all [Chips.IfC.opIf, Chips.Ctrl.opJump, Chips.opHost, opHostX, opUnreach, opMemGrowX,
         opMemSizeX, isConvOp]; done)
    | (rename_i fee hfee _ fi hc hfi _ hid np ar hb
       obtain ⟨name, hn, hch⟩ := Option.bind_eq_some_iff.mp hb
       simp only [Option.some.injEq] at hr
       exact ⟨fi, name, hid, np, ar, fee, hc, hfi, hn, hch, hfee, hr.symm⟩)

/-- At a `call` with a HOST-chip signature, the checker's height covers the arguments: `np ≤ h`. -/
theorem verify_call_np {p : Prepared} {pf : PFunc} {L : Array (List Label)} {H : Array Nat} {pc fi : Nat}
    (hv : verifyAtM2 p pf L H pc = true) (hc : pf.code[pc]? = some (.call fi)) {np ar : Nat}
    (hs : sigOfM2 p fi = some (np, ar)) {h : Nat} (hh : H[pc]? = some h) : np ≤ h := by
  unfold verifyAtM2 at hv
  rw [hc, hh] at hv
  cases hl : L[pc]? with
  | none => rw [hl] at hv; simp at hv
  | some ls =>
    rw [hl] at hv
    simp only [hs, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1

/-! ## 3. The HOST row's FETCH -/

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace}

/-- **The HOST row's record**: at an active HOST row, the FETCH message is the record of a `call fi`
of an import with a HOST-chip entry at some `(k, l)`, and the row's `pc`, `h`, `fee`, `np` columns
are the record's. -/
theorem host_rec (X : M2Ctx) (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOK X.toCtx tr)
    {r : Nat} (hA : HAct tr pub r) :
    ∃ k l fi name hid np ar fee, k < X.nf ∧ l < (X.pfOf k).code.size ∧
      (X.pfOf k).code[l]? = some (.call fi) ∧ fi < X.p.m.imports.size ∧ importName X.p fi = some name ∧
      hostChipM2 name = some (hid, np, ar) ∧ feeUnits X.cfg (X.pfOf k).gas[l]? = some fee ∧ fee ≤ X.maxFee ∧
      rowNat tr 22 r cPc = X.offOf k + l ∧ rowNat tr 22 r cH = (X.ckOf k).heights[l]?.getD 0 ∧
      rowNat tr 22 r cFee = fee ∧ rowNat tr 22 r Host.np = np := by
  have hP := P_val
  have ht : 22 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hi : fetch (v cPc) (Expr.c opHost) (v cH) (v cFee) [v Host.hid, v Host.np, v Host.ar, 0] (v Host.act) ∈
      ((wasmBaseSegAir nloc ngl).tables[22]'ht).inters := by
    rw [seg_t22]
    show _ ∈ HostG.inters
    rw [hostG_inters_eq]
    refine List.mem_append_left _ ?_
    unfold Host.inters
    simp
  have ho := row_occ (pub := pub) ht hA.1 hi
  have hc1 : ((v Host.act).eval (tr.row pub 22 r)).toNat = 1 := by
    simp only [v, Expr.eval_col, Trace.row]
    exact host_act_nat hA.2
  obtain ⟨j, hj, hm⟩ := seg_fetchM2 H X hcode ho rfl rfl hc1
  simp only at hm
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  simp only [codeRecM2, hrj, Option.getD_some, Array.getElem?_eq_getElem hsz] at hm
  have hfeeLe := (X.factsOf hk).feeLe l hl
  rw [Array.getElem?_eq_getElem hsz, Option.getD_some] at hfeeLe
  generalize (X.ckOf k).records[l] = rec at hrec hm hfeeLe
  have hcell : ∀ i, (List.map (fun x => Expr.eval (tr.row pub 22 r) x) (fetch (v cPc) (Expr.c opHost) (v cH)
      (v cFee) [v Host.hid, v Host.np, v Host.ar, 0] (v Host.act)).msg).getD i 0 = ((rec.getD i 0 : Nat) : F) := by
    intro i; rw [hm, getD_map_cast]
  have h1 := hcell 1
  simp only [fetch, List.cons_append, List.nil_append, List.map_cons, List.getD_cons_succ,
    List.getD_cons_zero, Expr.eval_c] at h1
  have hop : rec.getD 1 0 = opHost :=
    (natEq h1 (by simp only [opHost]; omega) (by have := recordAtM2_op_lt hrec; omega)).symm
  obtain ⟨fi, name, hid, np, ar, fee, hcd, hfi, hn, hch, hfee, rfl⟩ := recordAtM2_host_op hrec hop
  obtain ⟨-, -, hnp9, -⟩ := hostChipM2_facts hch
  have hfee16 := feeUnits_lt hfee
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have hoffk := X.off_bound hk
  have hHb := (X.factsOf hk).hBound l hl
  have h0 := hcell 0
  have h2 := hcell 2
  have h3 := hcell 3
  have h5 := hcell 5
  simp only [fetch, List.cons_append, List.nil_append, List.map_cons, List.getD_cons_succ,
    List.getD_cons_zero, v, Expr.eval_col, Trace.row] at h0 h2 h3 h5
  rw [cell_cast] at h0 h2 h3 h5
  refine ⟨k, l, fi, name, hid, np, ar, fee, hk, hl, hcd, hfi, hn, hch, hfee,
    by simpa using Nat.le_trans hfeeLe (X.maxFee_ge hk), ?_, ?_, ?_, ?_⟩
  · exact natEq h0 (rowNat_lt tr 22 r _) (by omega)
  · exact natEq h2 (rowNat_lt tr 22 r _) (by omega)
  · exact natEq h3 (rowNat_lt tr 22 r _) (by omega)
  · exact natEq h5 (rowNat_lt tr 22 r _) (by omega)

/-- **`HostFeeOK` is a theorem** (the fee column is a record fee). -/
theorem hostFeeOK_of (X : M2Ctx) (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOK X.toCtx tr) :
    HostFeeOK X.toCtx tr pub := by
  intro r hA
  obtain ⟨k, l, fi, name, hid, np, ar, fee, -, -, -, -, -, -, -, hle, -, -, hf, -⟩ := host_rec X H hcode hA
  show rowNat tr 22 r cFee ≤ X.maxFee
  rw [hf]; exact hle

/-- **A host call's gas entry is not `linear`** (named; a static fact of the prepared module that the
M2 checker does not record — `feeUnits` accepts any kind with `fee.l = 0`). -/
def HostCallsNotLinear (X : Ctx) : Prop :=
  ∀ k, k < X.nf → ∀ (pc fi : Nat) (kd : IK) (fee : Fee), (X.pfOf k).code[pc]? = some (Instr.call fi) → fi < X.p.m.imports.size →
    (X.pfOf k).gas[pc]? = some (some (kd, fee)) → kd ≠ IK.linear

/-- **`HostCodeT` from the FETCH link** (+ `HostCallsNotLinear`). -/
theorem hostCodeT_of (X : M2Ctx) (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOK X.toCtx tr)
    (hlin : HostCallsNotLinear X.toCtx) : HostCodeT X.toCtx tr pub := by
  have hP := P_val
  intro r hA
  obtain ⟨k, l, fi, name, hid, np, ar, fee, hk, hl, hcd, hfi, hn, hch, -, -, hpc, hh, -, hnp⟩ := host_rec X H hcode hA
  obtain ⟨harm, hna, -, hany⟩ := hostChipM2_facts hch
  refine ⟨name, harm, by rw [hnp]; exact hna, fun E s f tps tpl t pc S live a b R hin => ?_⟩
  -- the row's code position is `(k, l)`
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have hkE : E.k < X.nf := R.kLt
  have hpcE : pc < (X.pfOf E.k).code.size := R.pcLt
  have hoffE := X.off_bound hkE
  have hoffk := X.off_bound hk
  have e0 : (rowInM tr pub (22, r)).getD 0 0 = ((X.offOf E.k + pc : Nat) : F) := by rw [hin]; rfl
  have e0' : (rowInM tr pub (22, r)).getD 0 0 = ((rowNat tr 22 r cPc : Nat) : F) := by
    show (rowIn Host.table tr pub 22 r).getD 0 0 = _; rw [host_rowIn]; rfl
  have epos : X.offOf k + l = X.offOf E.k + pc := by
    rw [← hpc]; exact natEq (e0'.symm.trans e0) (rowNat_lt tr 22 r _) (by omega)
  obtain ⟨rfl, rfl⟩ := X.loc_unique hk hl hkE hpcE epos
  have hfr := R.frames
  have hfn : f.fn = X.fnOf E.k := R.fn
  have hfpc : f.pc = l := R.pcEq
  have hfunc := (X.factsOf hk).func
  obtain ⟨im, him, hkind⟩ : ∃ im, X.p.m.imports[fi]? = some im ∧ im.kind = 0 ∧ im.name = name := by
    unfold importName at hn
    cases h : X.p.m.imports[fi]? with
    | none => rw [h] at hn; simp at hn
    | some im =>
      rw [h] at hn
      simp only [Option.bind_some] at hn
      split at hn
      · cases hn; exact ⟨im, rfl, by assumption, rfl⟩
      · cases hn
  have hht : (X.ckOf E.k).heights[l]? = some (s.stack.size - E.sb) := R.height
  refine ⟨⟨E.rest, X.pfOf E.k, fi, hfr, by rw [hfn]; exact hfunc, by rw [hfpc]; exact hcd, hfi, ?_,
    fun kd fee' hg => hlin E.k hk l fi kd fee' hcd hfi (by rw [hfpc] at hg; exact hg)⟩, ?_, ?_⟩
  · show X.p.m.imports[fi]!.name = name
    rw [getElem!_of_lt hfi]
    have : X.p.m.imports[fi] = im := by rw [Array.getElem?_eq_getElem hfi] at him; exact Option.some.inj him
    rw [this]; exact hkind.2
  · rw [hh, hht]; rfl
  · have hsig : sigOfM2 X.p fi = some (np, ar) := by
      unfold sigOfM2; rw [if_pos hfi, hn]; exact hany
    have := verify_call_np ((X.factsOf hk).verify l hl) hcd hsig hht
    rw [hnp]; omega

end

/-! ## 4. Segment soundness with the code facts discharged -/

/-- **`seg_sound_hostIf_fetch`**: `seg_sound_hostIf''` with `HostCodeT` and `HostFeeOK` discharged by
the HOST row's FETCH link.  Remaining HOST premises: the producer contract (`HostIf`, `HostAnsCov`),
`HostCallsNotLinear` (static module fact), write coverage (`HostWritesCovT`, the AIR gap) and the
producer/consumer times of the fused traffic (`HostRowsTimes`). -/
theorem seg_sound_hostIf_fetch (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {hts : List Nat} {σc : Nat → St} {np : Nat} (hI : HostIf X.toCtx tr pub sg hts σc)
    (hans : HostAnsCov X.toCtx tr pub sg hts σc np) (hlin : HostCallsNotLinear X.toCtx)
    (hwr : HostWritesCovT X.toCtx tr pub sg (thread hts σc) np) (htm : HostRowsTimes tr pub)
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
  seg_sound_hostIf'' X H hC hl hcode hfunc hb hg hkeep hI hans (hostCodeT_of X H hcode hlin) hwr
    (hostFeeOK_of X H hcode) htm hst0 hlen htin hfeeN hstepgas hg64 hinit hT h0 hw0 hσ0 hp0

#print axioms seg_sound_hostIf_fetch
#print axioms chipEntries_arm
#print axioms hostChipM2_facts
#print axioms recordAtM2_host_op
#print axioms host_rec
#print axioms hostFeeOK_of
#print axioms hostCodeT_of

end WasmBase
