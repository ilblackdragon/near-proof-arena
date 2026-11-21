import WasmBase.Main.SegExecJH
import WasmBase.Main.SegChainSigma
import WasmBase.Main.SegSoundSigmaMP
import WasmBase.Main.SegChainMemMP
import WasmBase.Main.SegMemFrameMP
import WasmBase.Main.SegSoundK

/-!
# WasmBase.Main.SegSoundAll — single-segment σ-pinned pieces for the merged chain (E2E M6)

The single-segment theorems that `Main/SegChainAll.lean` (`Cuti.seg_chain_all_mp`, `Cuti.seg_chain_all`)
chains, all with the σ-pinned HOST premises (`HoldRowSσ`, `HostRelyσ`, `SigKeep`, the in-pin
`sideR s0 = σ (t_in + 1)`; `Main/SegSoundSigma.lean`), proved once over `HoldsXS` (both segment AIRs):

* §1 `seg_tombDead_rowsJS` (`seg_tombDead_rowsJ` from `HoldsXS`), `seg_tombDeadσS`, **`seg_sound_cσS`**
  (`seg_sound_cS` σ-pinned: `TombDead` discharged, `HostBLinkedL`, `RegWF sN`, `InDom`, and
  `sideR sN = σ (t_out + 1)`), **`seg_sound_kσ_mp`** / `seg_sound_kσ` (the same without
  `HostBLinkedL`/`RegCLinked`: the call-key bus 214, `seg_hostBLinkedL`, `seg_regCLinked`);
* §2 the memory interface under the σ-thread: `seg_mem_frameσS` (page count and byte frame, via
  `exec_pagesJ` / `exec_frameJ`, `Main/SegExecJH.lean`), **`seg_mem_soundσ_mp`** /
  `seg_mem_soundσ` (`MemRoot.seg_mem_sound(_mp)` σ-pinned: in-root binds MEMB's bytes, out-root is the
  out-state's root).

The old statements are unchanged; their HOST-row premises are unsatisfiable on host traces
(`Main/HostVacuity.lean`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Single segment, `HoldsXS`, σ-pinned -/

/-- **`TombDead` from the trace, row premises restricted to an invariant `J`** (`seg_tombDead_rows`
over `exec_rowsJ`). -/
theorem seg_tombDead_rowsJS (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (J : Nat → St → Prop)
    (hrows : ∀ ρ ∈ actListM2 tr pub,
      RowFactsSegMapJ X J (rowInM tr pub ρ) (rowOutM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg)
    (st : Nat) (hst2 : st ≤ 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hinit : (initS tr pub).Nodup)
    (ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P)
    (hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} (h0 : Bnd X sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hJ0 : J ((pub.getD pubTIn 0).toNat + 1) s0) :
    TombDead tr pub (finS tr pub) := by
  have hP := P_val
  have hch := seg_hchS H X hb hg
  have hst : (segM0 tr pub :: (actListM2 tr pub).map (rowOutM tr pub)).Perm
      ([pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0, ((st : Nat) : F), pub.getD pubSbOut 0,
        tr.cell 0 0 (ix Segb.cols "cidf")] :: (actListM2 tr pub).map (rowInM tr pub)) := by
    have h := seg_hstS H
    rw [segMF_eq, hstN] at h
    exact h
  obtain ⟨-, -, hnd, hinj, hrel⟩ := exec_rowsJ (X := X) (act := actListM2 tr pub) (inS := rowInM tr pub)
    (outS := rowOutM tr pub) (cons := consCHS tr pub) (prod := prodCHS tr pub) (init := initS tr pub)
    (fin := finS tr pub) (pcf := _) (N := _) (Sf := _) sg st hst2 J hrows _ _ _ _ _ hst hch hinit
    (fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)) ht hfee hstepgas hg64 h0
    (fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) trivial hJ0
  -- every row: its time is `t0 + k + 1` and its activation id is `< 2^28`
  have hrow : ∀ ρ ∈ actListM2 tr pub, ∃ k, k < (actListM2 tr pub).length ∧
      (lvl (rowInM tr pub ρ)).toNat = (pub.getD pubTIn 0).toNat + k + 1 ∧ ((rowInM tr pub ρ).getD 5 0).toNat < 2 ^ 28 := by
    intro ρ hρ
    obtain ⟨k, hk, s, q, pc, S, sb, cid, live, hin, -, ⟨E, f, tps, tpl, -, hcid, -, R⟩, -, -, -⟩ := hrel ρ hρ
    refine ⟨k, hk, ?_, ?_⟩
    · rw [hin]; exact Fp.toNat_cast_of_lt (by omega)
    · rw [hin]
      have := R.cidLt
      show ((cid : Nat) : F).toNat < 2 ^ 28
      rw [Fp.toNat_cast_of_lt (by omega)]; omega
  -- a row's space-4 production is CALL's record, of slot = the row's time
  have hprod : ∀ ρ ∈ actListM2 tr pub, ∀ x ∈ prodCHS tr pub ρ, x.space = 4 →
      ρ.1 = 13 ∧ x = callRecMsg tr pub ρ.2 ∧ x.slot = (lvl (rowInM tr pub ρ)).toNat := by
    intro ρ hρ x hx h4
    obtain ⟨t, r⟩ := ρ
    rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, -⟩
    · simp only at h22; subst h22; exact absurd h4 (host_send_no4 hx)
    · simp only at htI hr ⊢
      have hne : t ≠ 22 := by rcases htI with ⟨_, h⟩ | h | h | h <;> omega
      obtain ⟨-, eP, eI⟩ := consProd_instr (tr := tr) (pub := pub) (r := r) hne
      obtain ⟨k, hk, hl, hc⟩ := hrow (t, r) hρ
      rw [eP] at hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      rw [eI] at hl hc
      obtain ⟨rfl, e⟩ := instr_send4S H htI hr hm (by omega) (by omega) h4
      refine ⟨rfl, e, ?_⟩
      rw [e, callRecMsg_slot, eI]
  intro r hr htk
  have hcon := table_constr_eqXS H (by simp [seg_air_len]) RetT.table (seg_t14' nloc ngl) hr
  obtain ⟨hs, ha, -, htk1⟩ := ret_count_vals_of hcon
  obtain ⟨-, -, -, -, hc0, -, -⟩ := ret_sound (rowNat tr 14 r) (tr.row pub 14 r) (rowNat_lt tr 14 r) hcon
  have htk' : (Ret.tk.eval (tr.row pub 14 r)).toNat = 1 := by omega
  have hmem : (14, r) ∈ actListM2 tr pub := ret_mem_actListM2 hr (by omega)
  -- the activation id is the row's STATE `cid`, `< 2^28`
  have eC : (rowInM tr pub (14, r)).getD 5 0 = tr.cell 14 r Ret.kCid := by
    rw [show rowInM tr pub (14, r) = rowIn Ret.table tr pub 14 r from rfl, ← stE_eval]; rfl
  obtain ⟨-, -, -, hcl⟩ := hrow (14, r) hmem
  rw [eC] at hcl
  refine ⟨hcl, hc0 (by omega), fun x hx h4 hxs => ?_⟩
  -- the count
  let c := rowNat tr 14 r Ret.kCid
  let p : Msg → Bool := fun x => decide (x.space = 4 ∧ x.slot = c)
  have hcnt := hch.countP_eq p
  have e2 : (finS tr pub ++ (actListM2 tr pub).flatMap (consCHS tr pub)).countP p =
      (finS tr pub).countP p + ((actListM2 tr pub).flatMap (consCHS tr pub)).countP p := by
    rw [List.countP_append]
  have hL : (initS tr pub ++ (actListM2 tr pub).flatMap (prodCHS tr pub)).countP p ≤ 1 := by
    refine countP_le_one_of hnd fun x hx y hy px py => ?_
    simp only [p, decide_eq_true_eq] at px py
    have side : ∀ a ∈ initS tr pub, ∀ b ∈ (actListM2 tr pub).flatMap (prodCHS tr pub),
        a.space = 4 → b.space = 4 → a.slot = b.slot → False := by
      intro a ha b hb ha4 hb4 hab
      obtain ⟨ρ, hρ, hbρ⟩ := List.mem_flatMap.mp hb
      obtain ⟨-, -, e⟩ := hprod ρ hρ b hbρ hb4
      obtain ⟨k, -, hl, -⟩ := hrow ρ hρ
      have := (bnd_rec4 h0 a ha ha4).2.1
      omega
    rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
    · exact ((bnd_rec4 h0 x hx px.1).2.2.2 y hy py.1 (py.2.trans px.2.symm)).symm
    · exact (side x hx y hy px.1 py.1 (px.2.trans py.2.symm)).elim
    · exact (side y hy x hx py.1 px.1 (py.2.trans px.2.symm)).elim
    · obtain ⟨ρ, hρ, hxρ⟩ := List.mem_flatMap.mp hx
      obtain ⟨ρ', hρ', hyρ'⟩ := List.mem_flatMap.mp hy
      obtain ⟨-, ex, sx⟩ := hprod ρ hρ x hxρ px.1
      obtain ⟨-, ey, sy⟩ := hprod ρ' hρ' y hyρ' py.1
      have hl : lvl (rowInM tr pub ρ) = lvl (rowInM tr pub ρ') := by
        rw [← Fp.cast_toNat (lvl (rowInM tr pub ρ)), ← Fp.cast_toNat (lvl (rowInM tr pub ρ')), ← sx, ← sy,
          px.2, py.2]
      have := hinj ρ hρ ρ' hρ' hl
      subst this
      rw [ex, ey]
  have hC : 1 ≤ ((actListM2 tr pub).flatMap (consCHS tr pub)).countP p := by
    refine List.countP_pos_iff.mpr ⟨decMsg (retRec.msg.map (·.eval (tr.row pub 14 r))),
      List.mem_flatMap.mpr ⟨(14, r), hmem, ?_⟩, ?_⟩
    · obtain ⟨eC', -, -⟩ := consProd_instr (tr := tr) (pub := pub) (r := r) (t := 14) (by omega)
      rw [eC']
      exact List.mem_map_of_mem (mem_rowMsgs_of retRec_mem rfl rfl htk')
    · simp only [p, decide_eq_true_eq]
      refine ⟨?_, rfl⟩
      simp only [retRec, chRecv, decMsg, List.cons_append, List.map_cons, List.getD_cons_zero, Expr.eval]
      exact Fp.toNat_cast_of_lt (by omega)
  have hF : (finS tr pub).countP p = 0 := by omega
  exact List.countP_eq_zero.mp hF x hx (by simp only [p, decide_eq_true_eq]; exact ⟨h4, hxs⟩)


/-- **`seg_tombDeadσS`**: `seg_tombDeadσ` from `HoldsXS` (any final status `st ≤ 2`). -/
theorem seg_tombDeadσS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ)
    (st : Nat) (hst2 : st ≤ 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1)) :
    TombDead tr pub (finS tr pub) := by
  have hP := P_val
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_of X.toCtx (seg_instr_codeNonHostS X H hcode) hI hkeep hsk hhold
  have hlenEq := seg_lenS H (fun ρ hρ => (hrows ρ hρ).flat.tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  exact seg_tombDead_rowsJS X.toCtx H hb hg (SigJ σ) hrows st hst2 hstN hinit ht hfee hstepgas hg64 h0 hσ0

/-- **`seg_sound_cσS`**: `seg_sound_cS` (TombDead discharged, `HostBLinkedL`, `RegWF sN`, `InDom`) with
the σ-pinned HOST premises; the out-state is on the thread. -/
theorem seg_sound_cσS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIfS SegSha.compressW nloc ngl pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hbL : HostBLinkedL tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ)
    (hrely : HostRelyσ X.toCtx tr pub σ)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1)) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ (MemGeom pub sN → WasmView.InDom X.toCtx sN) ∧
      sideR sN = σ ((pub.getD pubTOut 0).toNat + 1) := by
  have hP := P_val
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_of X.toCtx (seg_instr_codeNonHostS X H hcode) hI hkeep hsk hhold
  have hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).flat.tsOut
  have hb : HostBLinked tr pub := hostBLinked_ofS H hts (by omega) hbL
  have hT := seg_tombDeadσS X H hcode hfunc hb hg hkeep hsk hhold 0 (by omega) (by rw [hst0]; rfl) hlen htin
    hfeeN hstepgas hg64 hinit h0.1 hσ0
  obtain ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, hσN⟩ := seg_sound_σS X H hC hl hcode hfunc hb hg hkeep hsk
    hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit hT h0 hw0 hσ0
  exact ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, fun hG => seg_inDom X h3.1 hwN h6 (pages_lt_of_memGeom hG), hσN⟩

/-- **`seg_sound_kσ_mp`**: the σ-pinned segment theorem for the multiproof AIR **without** the linking
premises `HostBLinkedL`/`RegCLinked` (the call-key bus 214 gives both, `seg_hostBLinkedL`,
`seg_regCLinked`). -/
theorem seg_sound_kσ_mp (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ)
    (hrely : HostRelyσ X.toCtx tr pub σ)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1)) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ (MemGeom pub sN → WasmView.InDom X.toCtx sN) ∧
      sideR sN = σ ((pub.getD pubTOut 0).toNat + 1) :=
  seg_sound_cσS X H.toSMP (SegSha.ChipIf.toSMP H hC) hl hcode hfunc (seg_hostBLinkedL H.toSMP)
    (seg_regCLinked H.toSMP) hkeep hsk hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit h0 hw0 hσ0

/-- **`seg_sound_kσ`**: `seg_sound_kσ_mp` for the base segment AIR `wasmBaseSegAir`. -/
theorem seg_sound_kσ (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ)
    (hrely : HostRelyσ X.toCtx tr pub σ)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : BndC X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hw0 : RegWF s0) (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1)) :
    (pub.getD pubTOut 0).toNat = (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length ∧
    ∃ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN ∧
      (∀ m, run X.toCtx.cfg X.toCtx.p ((actListM2 tr pub).length + m) s0 = run X.toCtx.cfg X.toCtx.p m sN) ∧
      BndC X.toCtx sg sN (pub.getD pubTOut 0).toNat (pub.getD pubSOut 0).toNat (segFinM tr pub) (finS tr pub) ∧
      cutoList tr = cutView X.toCtx sN ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxOut = SegSha.limbsF d ∧
        SegSha.wbytes d = cutDigest (cutView X.toCtx sN)) ∧
      (∀ y ∈ cutView X.toCtx sN, MsgWF y) ∧
      RegWF sN ∧ (MemGeom pub sN → WasmView.InDom X.toCtx sN) ∧
      sideR sN = σ ((pub.getD pubTOut 0).toNat + 1) :=
  seg_sound_cσS X H.toS (SegSha.ChipIf.toS H hC) hl hcode hfunc (seg_hostBLinkedL H.toS)
    (seg_regCLinked H.toS) hkeep hsk hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit h0 hw0 hσ0

/-! ## 2. The memory frame and root, σ-pinned -/

/-- **`seg_mem_frameσS`**: `seg_mem_frameS` (page count and byte frame across a cut segment) with
the σ-pinned HOST premise and the in-pin. -/
theorem seg_mem_frameσS (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsXS nloc ngl pub tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ)
    (hpr : HostPagesRely X.toCtx tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1)) :
    ∀ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN →
      sN.pages.size = s0.pages.size ∧
      ∀ a, (∀ x ∈ initS tr pub, x.space = 3 → x.slot ≠ a) → readByte sN a = readByte s0 a := by
  intro sN hseg
  have hP := P_val
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfactsS X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_of X.toCtx (seg_instr_codeNonHostS X H hcode) hI hkeep hsk hhold
  have hlenEq := seg_lenS H (fun ρ hρ => (hrows ρ hρ).flat.tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  have hst := seg_hstS H
  rw [segMF_eq, hst0] at hst
  have hch := seg_hchS H X.toCtx hb hg
  have hpk : ∀ ρ ∈ actListM2 tr pub, PagesKeep X.toCtx (rowInM tr pub ρ) := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · exact hpr ρ hρ h22
    · exact seg_instr_pagesKeepS X H hcode ρ hρ h22
  have hsz := exec_pagesJ X.toCtx (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub) (consCHS tr pub)
    (prodCHS tr pub) (initS tr pub) (finS tr pub) (pub.getD pubPcOut 0) (pub.getD pubTOut 0 + 1)
    (pub.getD pubSOut 0) sg (SigJ σ) hrows (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat
    (segM0 tr pub) (pub.getD pubSbOut 0) (tr.cell 0 0 (ix Segb.cols "cidf")) hst hch hinit
    (fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)) ht hfee hstepgas hg64 h0 hσ0 hpk hseg
  refine ⟨hsz, fun a ha => ?_⟩
  by_cases hlt : a < memBytes s0
  · exact (exec_frameJ X.toCtx (actListM2 tr pub) (rowInM tr pub) (rowOutM tr pub) (consCHS tr pub)
      (prodCHS tr pub) (initS tr pub) (finS tr pub) (pub.getD pubPcOut 0) (pub.getD pubTOut 0 + 1)
      (pub.getD pubSOut 0) sg (SigJ σ) hrows (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat
      (segM0 tr pub) (pub.getD pubSbOut 0) (tr.cell 0 0 (ix Segb.cols "cidf")) hst hch hinit
      (fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)) ht hfee hstepgas hg64 h0 hσ0 hlt
      (fun y hy h3 => ha y hy h3) hseg).1
  · have hm : memBytes sN = memBytes s0 := by unfold memBytes; rw [hsz]
    rw [readByte_oob (by omega), readByte_oob (by omega)]

/-- **`seg_mem_soundσ_mp`**: `MemRoot.seg_mem_sound_mp` (in-root binds MEMB's bytes; out-root is the
out-state's memory root) with the σ-pinned HOST premise and the in-pin. -/
theorem seg_mem_soundσ_mp (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAirMP nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAirMP nloc ngl) pub tr chip) (hD30 : Dn pub ≤ 30)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ)
    (hpr : HostPagesRely X.toCtx tr pub) (hcu : MemRoot.CutiNoMem tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0)
    (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub) (initS tr pub))
    (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1)) :
    (MembIn tr pub s0 ∨ NearSpecV3.E2E.Bnd.Sha384Coll) ∧
    ∀ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN →
      ∀ {tN SN : Nat} {mN : List F}, Bnd X.toCtx sg sN tN SN mN (finS tr pub) →
      (MemRootOut pub sN ∧ MemGeom pub sN) ∨ NearSpecV3.E2E.Bnd.Sha384Coll := by
  refine ⟨MemRoot.seg_membIn_mp H hC hD30 hG hR, fun sN hseg tN SN mN hN => ?_⟩
  obtain ⟨hpg, hfr⟩ := seg_mem_frameσS X H.toSMP hcode hfunc hb hg hkeep hsk hhold hpr hst0 hlen htin hfeeN
    hstepgas hg64 hinit h0 hσ0 sN hseg
  exact MemRoot.seg_memRootOut_mp H hC hD30 hG hR hpg (fun a ha => hfr a (MemRoot.initS_free hcu ha))
    (MemRoot.membOut_of_bnd hN)

/-- **`seg_mem_soundσ`**: `seg_mem_soundσ_mp` for the base AIR (`MemRoot.seg_membIn` /
`MemRoot.seg_memRootOut`, no depth bound). -/
theorem seg_mem_soundσ (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg)
    {σ : Nat → St} (hsk : SigKeep tr pub σ) (hhold : HoldRowSσ X.toCtx tr pub sg σ)
    (hpr : HostPagesRely X.toCtx tr pub) (hcu : MemRoot.CutiNoMem tr pub)
    (hst0 : pub.getD Boundary.pubStatus 0 = 0)
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (hG : MemGeom pub s0) (hR : MemRootIn pub s0)
    (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub) (initS tr pub))
    (hσ0 : sideR s0 = σ ((pub.getD pubTIn 0).toNat + 1)) :
    (MembIn tr pub s0 ∨ NearSpecV3.E2E.Bnd.Sha384Coll) ∧
    ∀ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN →
      ∀ {tN SN : Nat} {mN : List F}, Bnd X.toCtx sg sN tN SN mN (finS tr pub) →
      (MemRootOut pub sN ∧ MemGeom pub sN) ∨ NearSpecV3.E2E.Bnd.Sha384Coll := by
  refine ⟨MemRoot.seg_membIn H hC hG hR, fun sN hseg tN SN mN hN => ?_⟩
  obtain ⟨hpg, hfr⟩ := seg_mem_frameσS X H.toS hcode hfunc hb hg hkeep hsk hhold hpr hst0 hlen htin hfeeN
    hstepgas hg64 hinit h0 hσ0 sN hseg
  exact MemRoot.seg_memRootOut H hC hG hR hpg (fun a ha => hfr a (MemRoot.initS_free hcu ha))
    (MemRoot.membOut_of_bnd hN)

#print axioms seg_tombDead_rowsJS
#print axioms seg_tombDeadσS
#print axioms seg_sound_cσS
#print axioms seg_sound_kσ_mp
#print axioms seg_sound_kσ
#print axioms seg_mem_frameσS
#print axioms seg_mem_soundσ_mp
#print axioms seg_mem_soundσ

end WasmBase
