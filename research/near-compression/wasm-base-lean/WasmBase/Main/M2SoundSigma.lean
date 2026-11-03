import WasmBase.Main.M2Sound
import WasmBase.Main.SegExecJH
import WasmBase.Main.SegSoundSigma

/-!
# WasmBase.Main.M2SoundSigma — `wasm_base_sound_m2σ`: the M2 whole-call theorem with the host side pinned (E2E M6)

`wasm_base_sound_m2` (`Main/M2Sound.lean`, unchanged) takes the HOST rows' facts `HoldRowM2` over
**every** related pre-state, so it is vacuous on traces with a continuing host call
(`Main/HostVacuity.lean`).  Its σ-pinned restatement, as `seg_sound_σ` is `seg_sound`'s:

* **`HoldRowM2σ`** — the HOST rows' `RowFactsSegJ … (SigJ σ)` with the M2 CH traffic (HOSTB bytes and
  REG-C net traffic fused, `consCHM2`/`prodCHM2`): only from related pre-states whose host side
  (`sideR`, registers included) is `σ t`, landing at `σ (t + 1)`;
* `SigKeep` — `σ` does not move at instruction rows (as `SegKeepM2` for the gas thread);
* the entry pin `sideR s0 = σ 1`.

Instruction rows execute non-host code (`m2_instr_codeNonHost`, the FETCH-op argument on
`wasmBaseM2Air`), so they keep the thread (`rowJKeep_sig`).  The run is `exec_rowsJH`
(`Main/SegExecJH.lean`), so the conclusion is `wasm_base_sound_m2`'s plus the pin of the **last
pre-state**: the state `s` after `n − 1` steps has `sideR s = σ n`, and its step is the terminal
one (`.fin sN` with no frames, or `.abort sN e`), with the gas equation.  (The final state of an
abort is the host's/`sync`'s; the pin is on the state the terminal step starts from.)
-/

namespace WasmBase
open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- **The active HOST rows' segment-aware row facts, M2 form, σ-pinned** (named premise, the
host-chip contract): `HoldRowM2` with the spec restricted to pre-states whose host side is `σ` at
the row's time. -/
def HoldRowM2σ (X : Ctx) (tr : Trace) (pub : List F) (seg : Nat → Nat × Nat) (σ : Nat → St) : Prop :=
  ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
    RowFactsSegJ X (SigJ σ) (rowInM tr pub (22, r)) (rowOutM tr pub (22, r))
      (consCHM2 tr pub (22, r)) (prodCHM2 tr pub (22, r))
      (seg (rowNat tr 22 r 1)) (seg (rowNat tr 22 r 1 + 1))

/-- The old (unrestricted) premise gives the σ-pinned one when the HOST rows keep the thread. -/
theorem HoldRowM2.toσ {X : Ctx} {tr : Trace} {pub : List F} {seg : Nat → Nat × Nat} (h : HoldRowM2 X tr pub seg)
    {σ : Nat → St} (hk : ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
      RowJKeep X (SigJ σ) (rowInM tr pub (22, r))) : HoldRowM2σ X tr pub seg σ :=
  fun r hr ha => RowFactsSeg.toJ (h r hr ha) (hk r hr ha)

/-- The instruction table at `t` of `wasmBaseM2Air` is `chipM2 t`'s (constraints, interactions). -/
theorem m2_instr_tab (nloc ngl t : Nat) (htI : IsInstrM2 t) :
    ∃ ht : t < (wasmBaseM2Air nloc ngl).tables.length,
      ((wasmBaseM2Air nloc ngl).tables[t]'ht).constraints = (chipM2 t).constraints ∧
      ∀ i ∈ (chipM2 t).inters, i ∈ ((wasmBaseM2Air nloc ngl).tables[t]'ht).inters := by
  rcases htI with ⟨h1, h14⟩ | rfl | rfl | rfl
  · rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
      t = 12 ∨ t = 13 ∨ t = 14 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp [m2_air_len], rfl, fun i hi => hi⟩
  all_goals exact ⟨by simp [m2_air_len], rfl, fun i hi => hi⟩

/-- **Every active instruction row of an M2 trace executes a non-host instruction** (at every related
state): `seg_instr_codeNonHost` on `wasmBaseM2Air` (FETCH op `< 0x1FF`, `recordAtM2_nonHost`). -/
theorem m2_instr_codeNonHost (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X.toCtx nloc ngl pub)
    (hcode : CodeOK X.toCtx tr) :
    ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → CodeNonHost X.toCtx (rowInM tr pub ρ) := by
  intro ρ hρ hne
  have hP := P_val
  obtain ⟨t, r⟩ := ρ
  simp only at hne
  rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, ha⟩
  · exact absurd h22 hne
  obtain ⟨ht, hcon, hint⟩ := m2_instr_tab nloc ngl t htI
  have hbit : ∀ i ∈ bcOf (chipM2 t), (tr.cell t r i).toNat ≤ 1 := by
    intro i hi
    have h := H.constr t ht r hr _ (by rw [hcon]; exact bcOf_mem hi)
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row] at h
    have h' : ((rowNat tr t r i : Nat) : F) * (((rowNat tr t r i : Nat) : F) - ((1 : Nat) : F)) = 0 := by
      simp only [rowNat, Fp.cast_toNat]; exact h
    rcases bool_nat (rowNat_lt tr t r i) h' with h0 | h1 <;> (show rowNat tr t r i ≤ 1; omega)
  obtain ⟨i, hi, hb, hs, hc1, hpc, hop⟩ := fetch_op_lt (instr_fetchOpOk t htI) hbit ha
  have ho := row_occ (pub := pub) ht hr (hint i hi)
  obtain ⟨j, hj, hm⟩ := m2_fetch X H hcode (m2_hsend_fetch H hpub) (o := (i.bus, i.send,
    i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat)) ho hb hs hc1
  simp only at hm
  have eI : rowInM tr pub (t, r) = rowIn (chipM2 t) tr pub t r := by
    have ec : chipTM2 t = chipM2 t := by simp [chipTM2, hne]
    simp [rowInM, ec]
  rw [eI]
  intro E s f tps tpl tt pc S live a b R hin ins hins
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  simp only [codeRecM2, hrj, Option.getD_some, Array.getElem?_eq_getElem hsz] at hm
  generalize (X.ckOf k).records[l] = rec at hrec hm
  have hpc0 := recordAtM2_pc hrec
  have hop1 := recordAtM2_op_lt hrec
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have hkE := R.kLt
  have hpcE := R.pcLt
  simp only [toCtx_nf, toCtx_pfOf] at hkE hpcE
  have hoffE := X.off_bound hkE
  have hoffk := X.off_bound hk
  have h0 := congrArg (fun m => m.getD 0 0) hm
  have h1 := congrArg (fun m => m.getD 1 0) hm
  simp only [getD_map_cast] at h0 h1
  rw [hpc, hin, hpc0] at h0
  have e0 : X.offOf k + l = X.offOf E.k + pc :=
    natEq (by simpa [stMsg] using h0.symm) (by omega) (by omega)
  obtain ⟨rfl, rfl⟩ := X.loc_unique hk hl hkE hpcE e0
  have hopN : rec.getD 1 0 < 0x1FF := by
    rw [h1, Fp.toNat_cast_of_lt (by omega)] at hop
    exact hop
  exact recordAtM2_nonHost hrec (by simpa using hins) hopN

/-- **Assembling the σ-pinned row facts for the M2 AIR.**  Instruction rows: `m2_rowfacts`
(+ `SegKeepM2`), restricted by `rowJKeep_sig` (non-host code + `SigKeep`); HOST rows: `HoldRowM2σ`. -/
theorem rowFactsSegMapJ_m2 (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr) (hpub : PubOK X.toCtx nloc ngl pub)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {seg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub seg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowM2σ X.toCtx tr pub seg σ) :
    ∀ ρ ∈ actListM2 tr pub,
      RowFactsSegMapJ X.toCtx (SigJ σ) (rowInM tr pub ρ) (rowOutM tr pub ρ) (consCHM2 tr pub ρ)
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
    have hU : RowFactsSegMap X.toCtx (rowInM tr pub (t, r)) (rowOutM tr pub (t, r)) (consCHM2 tr pub (t, r))
        (prodCHM2 tr pub (t, r)) seg := by
      unfold RowFactsSegMap
      have hs := hkeep (t, r) hρ hne
      rw [hC, hP, hI, hO]
      rw [hI] at hs
      rw [hs]
      exact hRF.toSeg
    exact RowFactsSeg.toJ hU (rowJKeep_sig (m2_instr_codeNonHost X H hpub hcode (t, r) hρ hne) (hsk (t, r) hρ hne))

/-- **`wasm_base_sound_m2σ`.**  `wasm_base_sound_m2` with the HOST premise σ-pinned (`HoldRowM2σ`,
`SigKeep`, the entry pin `sideR s0 = σ 1`): a satisfied `wasmBaseM2Air` trace for a function the M2
checker accepted is a run of the spec interpreter of `n = N − 1` steps, `n > 0`; the state `s` after
`n − 1` steps is on the thread (`sideR s = σ n`) and its step is the terminal one: status 1 a normal
finish with an empty frame stack, status 2 an abort; the gas of the final state is the last
segment's. -/
theorem wasm_base_sound_m2σ (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {s0 : St} {f0 : Frame}
    (H : Holds (wasmBaseM2Air nloc ngl) pub tr)
    (hpub : PubOK X.toCtx nloc ngl pub) (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    (seg : Nat → Nat × Nat) (hkeep : SegKeepM2 tr pub seg)
    (σ : Nat → St) (hsk : SigKeep tr pub σ) (hhold : HoldRowM2σ X.toCtx tr pub seg σ)
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
      (seg 1).1 (seg 1).2)
    (hσ0 : sideR s0 = σ 1) :
    (actListM2 tr pub).length + 1 = (pub.getD Boundary.pubN 0).toNat ∧
    0 < (actListM2 tr pub).length ∧
    ∃ s, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length - 1) s0 = .cont s ∧
      sideR s = σ (actListM2 tr pub).length ∧
    (st = 1 → ∃ sN, step X.toCtx.cfg X.toCtx.p s = .fin sN ∧
      run X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .fin sN ∧ sN.frames = [] ∧
      X.toCtx.R * ((pub.getD Boundary.pubS 0).toNat - (seg ((actListM2 tr pub).length + 1)).1) +
        sN.gas.g = (seg ((actListM2 tr pub).length + 1)).2) ∧
    (st = 2 → ∃ (sN : St) (e : String), step X.toCtx.cfg X.toCtx.p s = .abort sN e ∧
      run X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .abort sN e ∧
      X.toCtx.R * ((pub.getD Boundary.pubS 0).toNat - (seg ((actListM2 tr pub).length + 1)).1) +
        sN.gas.g = (seg ((actListM2 tr pub).length + 1)).2) := by
  have hP := P_val
  have hrows := rowFactsSegMapJ_m2 X H hpub hcode hfunc hkeep hsk hhold
  have hbuses := m2_buses (X := X.toCtx) H hpub hb hg
  have hstPerm : (stMsg 0 1 0 0 0 0 :: (actListM2 tr pub).map (rowOutM tr pub)).Perm
      ([tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
        (st : F), tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
        (actListM2 tr pub).map (rowInM tr pub)) := by
    have h := hbuses.1
    rw [← hstStatus] at h
    exact h
  have hN : (actListM2 tr pub).length + 1 = (pub.getD Boundary.pubN 0).toNat :=
    chain_len (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub)
      (tr.cell 0 0 Boundary.pcf) (pub.getD Boundary.pubN 0) (pub.getD Boundary.pubS 0)
      (st : F) (tr.cell 0 0 Boundary.sbf) (tr.cell 0 0 Boundary.cidf)
      (fun r hr => (hrows r hr).flat.tsOut) hstPerm hlen
  have hfee : 0 + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < ZkFormal.Algebra.P := by
    rw [hN]; omega
  have ht : 0 + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < ZkFormal.Algebra.P := by omega
  have hB0 : Bnd X.toCtx seg s0 0 0 (stMsg 0 1 0 0 0 0)
      ((initRaw nloc pub).map decMsg ++ ((globRaw nloc ngl pub).map decMsg ++
        ((budRaw nloc ngl pub).map decMsg ++ (memRaw tr pub).map decMsg))) := by
    have hb0 := Bnd.of_relW (X := X.toCtx) (sg := seg) (t := 0) h0
    have e : X.toCtx.offOf 0 + 0 = 0 := by rw [Ctx.off_zero]
    simp only [e] at hb0
    exact hb0
  obtain ⟨_, _, hhalt, _⟩ := exec_rowsJH X.toCtx (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub)
    (consCHM2 tr pub) (prodCHM2 tr pub)
    ((initRaw nloc pub).map decMsg ++
      ((globRaw nloc ngl pub).map decMsg ++ ((budRaw nloc ngl pub).map decMsg ++
        (memRaw tr pub).map decMsg)))
    (((if X.toCtx.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then
        [resRaw pub tr] else []).map decMsg ++ (finRaw nloc tr).map decMsg) ++
      (drainRaw tr pub).map decMsg)
    (tr.cell 0 0 Boundary.pcf) (pub.getD Boundary.pubN 0) (pub.getD Boundary.pubS 0) seg st (by omega)
    (SigJ σ) hrows 0 0 (stMsg 0 1 0 0 0 0) (tr.cell 0 0 Boundary.sbf) (tr.cell 0 0 Boundary.cidf)
    hstPerm hbuses.2 hinitNd (fun x hx => Nat.le_of_eq (hinitTp x hx)) ht hfee hstepgas hg64 hB0
    (fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) trivial
    (by show sideR s0 = σ (0 + 1); exact hσ0)
  have hne : st ≠ 0 := by rcases hst12 with h | h <;> (subst h; decide)
  obtain ⟨hpos, s, hrun, hJ, hfin, hab⟩ := hhalt hne
  have eJ : sideR s = σ (actListM2 tr pub).length := by
    have : SigJ σ (0 + (actListM2 tr pub).length) s := hJ
    simpa [SigJ] using this
  refine ⟨hN, hpos, s, hrun, eJ, fun h1 => ?_, fun h2 => ?_⟩
  · obtain ⟨sN, -, -, -, hstep, -, hr, hfr, hgas, -⟩ := hfin h1
    refine ⟨sN, hstep, hr, hfr, ?_⟩
    simpa using hgas
  · obtain ⟨sN, e, hstep, -, hr, hgas⟩ := hab h2
    refine ⟨sN, e, hstep, hr, ?_⟩
    simpa using hgas

#print axioms m2_instr_tab
#print axioms m2_instr_codeNonHost
#print axioms rowFactsSegMapJ_m2
#print axioms wasm_base_sound_m2σ

end WasmBase
