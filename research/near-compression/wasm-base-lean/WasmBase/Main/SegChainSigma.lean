import WasmBase.Main.SegChain
import WasmBase.Main.SegSoundSigma

/-!
# WasmBase.Main.SegChainSigma — `TombDead`, `seg_sound_c` and the chained segments, σ-pinned (E2E M6)

The σ-thread restatement (`Main/SegSigma.lean`, `Main/SegSoundSigma.lean`) carried to the chain:

* `seg_tombDead_rowsJ` / **`seg_tombDeadσ`** — `TombDead` at the out-boundary from the σ-pinned row
  facts (`seg_tombDead_rows`' proof over `exec_rowsJ`'s per-row relation);
* **`seg_sound_cσ`** — `seg_sound_c` with `HoldRowSσ`/`HostRelyσ`/`SigKeep` and the in-pin:
  `TombDead` discharged, `HostBLinked` reduced to `HostBLinkedL`, `RegWF sN`, `InDom` given the out
  geometry, and `sideR sN = σ (t_out + 1)`;
* **`Cuti.seg_chain_σ`** / **`Cuti.seg_chain_csteps_σ`** — the chained-segments theorem with one
  global σ-thread: per segment `SegPremσ` (`SegPrem` with the σ-pinned host premises and `SigKeep`),
  in/out relations `InSσ`/`OutSσ` (`InS`/`OutS` plus the pin `sideR s = σ (t + 1)` at the segment's
  in/out time).  The pin crosses a link for free: `LinkPub.t` makes the next segment's `t_in` this
  one's `t_out`.

The old statements (`seg_tombDead`, `seg_sound_c`, `seg_chain`, …) are unchanged; their HOST-row
premises are unsatisfiable on traces with a continuing host call (`Main/HostVacuity.lean`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
open HostFoot StepSide
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. `TombDead`, σ-pinned -/

/-- **`TombDead` from the trace, row premises restricted to an invariant `J`** (`seg_tombDead_rows`
over `exec_rowsJ`). -/
theorem seg_tombDead_rowsJ (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
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
  have hch := seg_hch H X hb hg
  have hst : (segM0 tr pub :: (actListM2 tr pub).map (rowOutM tr pub)).Perm
      ([pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0, ((st : Nat) : F), pub.getD pubSbOut 0,
        tr.cell 0 0 (ix Segb.cols "cidf")] :: (actListM2 tr pub).map (rowInM tr pub)) := by
    have h := seg_hst H
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
      obtain ⟨rfl, e⟩ := instr_send4 H htI hr hm (by omega) (by omega) h4
      refine ⟨rfl, e, ?_⟩
      rw [e, callRecMsg_slot, eI]
  intro r hr htk
  have hcon := table_constr_eqX H (by simp [seg_air_len]) RetT.table (seg_t14' nloc ngl) hr
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


/-- **`seg_tombDeadσ`: `TombDead` at the out-boundary** from `seg_sound_σ`'s hypotheses (any final
status `st ≤ 2`). -/
theorem seg_tombDeadσ (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
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
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_seg X H hcode hI hkeep hsk hhold
  have hlenEq := seg_len H (fun ρ hρ => (hrows ρ hρ).flat.tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  exact seg_tombDead_rowsJ X.toCtx H hb hg (SigJ σ) hrows st hst2 hstN hinit ht hfee hstepgas hg64 h0 hσ0

/-! ## 2. `seg_sound_c`, σ-pinned -/

/-- **`seg_sound_cσ`**: `seg_sound_c` (TombDead discharged, `HostBLinkedL`, `RegWF sN`, `InDom`) with the
σ-pinned HOST premises; the out-state is on the thread. -/
theorem seg_sound_cσ (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) {chip : List StateM5a.Sha512If.IfMsg}
    (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip) (hl : CutoHiLimbs tr)
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
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_seg X H hcode hI hkeep hsk hhold
  have hts : ∀ ρ ∈ actListM2 tr pub, lvl (rowOutM tr pub ρ) = lvl (rowInM tr pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).flat.tsOut
  have hb : HostBLinked tr pub := hostBLinked_of H hts (by omega) hbL
  have hT := seg_tombDeadσ X H hcode hfunc hb hg hkeep hsk hhold 0 (by omega) (by rw [hst0]; rfl) hlen htin
    hfeeN hstepgas hg64 hinit h0.1 hσ0
  obtain ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, hσN⟩ := seg_sound_σ X H hC hl hcode hfunc hb hg hkeep hsk
    hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit hT h0 hw0 hσ0
  exact ⟨hlenEq, sN, h1, h2, h3, h4, h5, h6, hwN, fun hG => seg_inDom X h3.1 hwN h6 (pages_lt_of_memGeom hG), hσN⟩

/-! ## 3. The chained segments, σ-pinned -/

namespace Cuti

/-- **The per-segment named premises, σ-pinned**: `SegPrem` with `HoldRowSσ`/`HostRelyσ` for the global
thread `σ` and `SigKeep`. -/
structure SegPremσ (X : M2Ctx) (nloc ngl : Nat) (sg : Nat → Nat × Nat) (σ : Nat → St) (d : SegD) : Prop where
  H : HoldsX (wasmBaseSegAir nloc ngl) d.pub d.tr
  hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) d.pub d.tr d.chip
  hl : CutoHiLimbs d.tr
  hcode : CodeOK X.toCtx d.tr
  hfunc : FuncOK X.toCtx d.tr
  hbL : HostBLinkedL d.tr d.pub
  hg : RegCLinked d.tr d.pub
  hkeep : SegKeepM2 d.tr d.pub sg
  hsk : SigKeep d.tr d.pub σ
  hhold : HoldRowSσ X.toCtx d.tr d.pub sg σ
  hrely : HostRelyσ X.toCtx d.tr d.pub σ
  hst0 : d.pub.getD Boundary.pubStatus 0 = 0
  hlen : (actListM2 d.tr d.pub).length < 2 ^ 28
  htin : (d.pub.getD pubTIn 0).toNat < 2 ^ 28
  hfeeN : (d.pub.getD pubSIn 0).toNat +
    ((d.pub.getD pubTOut 0).toNat - (d.pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P
  /-- MEM: the in-root binds MEMB's in-side bytes. -/
  memIn : ∀ s, MemRootIn d.pub s → MembIn d.tr d.pub s ∨ NearSpecV3.E2E.Bnd.Sha384Coll
  /-- MEM: a run from a state with the in-root (and its MEMB bytes) ends at a state with the out-root. -/
  memOut : ∀ s0 sN, BndC X.toCtx sg s0 d.tIn d.SIn (segM0 d.tr d.pub) (initS d.tr d.pub) →
    MembIn d.tr d.pub s0 → MemRootIn d.pub s0 → NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s0 = .cont sN →
    BndC X.toCtx sg sN d.tOut d.SOut (segFinM d.tr d.pub) (finS d.tr d.pub) →
    MemRootOut d.pub sN ∨ NearSpecV3.E2E.Bnd.Sha384Coll

/-- The in-relation of a segment, on the thread. -/
def InSσ (X : M2Ctx) (sg : Nat → Nat × Nat) (σ : Nat → St) (d : SegD) (s : St) : Prop :=
  InS X sg d s ∧ sideR s = σ (d.tIn + 1)

/-- The out-relation of a segment, on the thread. -/
def OutSσ (X : M2Ctx) (sg : Nat → Nat × Nat) (σ : Nat → St) (d : SegD) (s : St) : Prop :=
  OutS X sg d s ∧ sideR s = σ (d.tOut + 1)

section
variable (X : M2Ctx) {nloc ngl : Nat} {sg : Nat → Nat × Nat} {σ : Nat → St}
  (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
    X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
  (hg64 : X.toCtx.g0 < 2 ^ 64)

include hstepgas hg64 in
/-- **One segment, σ-pinned** (`seg_sound_cσ`, `seg_cid_out`, MEM's out-root). -/
theorem seg_stepσ {d : SegD} (hp : SegPremσ X nloc ngl sg σ d) {s : St} (hin : InSσ X sg σ d s) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ s', NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p d.n s = .cont s' ∧ OutSσ X sg σ d s' := by
  have hP := P_val
  obtain ⟨⟨h0, hw, hinit, hroot⟩, hσ0⟩ := hin
  obtain ⟨H, hC, hl, hcode, hfunc, hbL, hg, hkeep, hsk, hhold, hrely, hst0, hlen, htin, hfeeN, memIn, memOut⟩ := hp
  obtain ⟨-, sN, h1, -, h3, -, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hwN, hdom, hσN⟩ :=
    seg_sound_cσ X H hC hl hcode hfunc hbL hg hkeep hsk hhold hrely hst0 hlen htin hfeeN hstepgas hg64 hinit h0 hw
      hσ0
  have hI : SegInstrRows X.toCtx d.tr d.pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMapJ_seg X H hcode hI hkeep hsk hhold
  have hts : ∀ ρ ∈ actListM2 d.tr d.pub, lvl (rowOutM d.tr d.pub ρ) = lvl (rowInM d.tr d.pub ρ) + 1 :=
    fun ρ hρ => (hrows ρ hρ).flat.tsOut
  have hb : HostBLinked d.tr d.pub := hostBLinked_of H hts (by omega) hbL
  have hT := seg_tombDeadσ X H hcode hfunc hb hg hkeep hsk hhold 0 (by omega) (by rw [hst0]; rfl) hlen htin
    hfeeN hstepgas hg64 hinit h0.1 hσ0
  have hcid := seg_cid_out H (M2Ctx.toCtx_fns_nodup X) hl hT h3
  rcases memIn s hroot with hmb | hc
  case inr => exact Or.inl hc
  rcases memOut s sN h0 hmb hroot h1 h3 with hro | hc
  case inr => exact Or.inl hc
  exact Or.inr ⟨sN, h1, ⟨h3, hwN, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, hdom⟩, hσN⟩

/-- **One link, σ-pinned** (`link_step`'s argument; the pin moves along `LinkPub.t`). -/
theorem link_stepσ {d d' : SegD} (hp' : SegPremσ X nloc ngl sg σ d') (hL : LinkPub d.pub d'.pub) {s : St}
    (ho : OutSσ X sg σ d s) : NearSpecV3.E2E.Bnd.Sha384Coll ∨ InSσ X sg σ d' s := by
  obtain ⟨⟨hB, hw, ⟨dd, h6, hW, hpub, hsha⟩, hwf, hcid, hro, -⟩, hσ⟩ := ho
  have hctx : PubDigIs d'.pub pubCtxIn (cutDigest (cutView X.toCtx s)) := ⟨dd, h6, hW, by rw [hL.ctx]; exact hpub, hsha⟩
  rcases cuti_view hp'.H hp'.hC hwf hctx with hc | hcuti
  · exact Or.inl hc
  have hroot : MemRootIn d'.pub s := by
    obtain ⟨e, h6', hW', hp'', hs'⟩ := hro
    exact ⟨e, h6', hW', by rw [hL.mem]; exact hp'', hs'⟩
  rcases hp'.memIn s hroot with hmb | hc
  case inr => exact Or.inl hc
  have ht : (d'.pub.getD pubTIn 0).toNat = d.tOut := by rw [hL.t]; rfl
  have hS : (d'.pub.getD pubSIn 0).toNat = d.SOut := by rw [hL.S]; rfl
  have hm := segM0_link (tr := d.tr) (tr' := d'.tr) hL.pc hL.t hL.S hL.sb (by rw [hL.cid]; exact hcid)
  have hB' := seg_reentry (M2Ctx.toCtx_fns_nodup X) hB hp'.H hcuti hmb ht hS hm
  refine Or.inr ⟨⟨hB', hw, initS_nodup hp'.H hw hwf hcuti, hroot⟩, ?_⟩
  show sideR s = σ ((d'.pub.getD pubTIn 0).toNat + 1)
  rw [ht]; exact hσ

include hstepgas hg64 in
/-- **The chained-segments theorem, σ-pinned.**  Cut segments `d0 :: ds`, each with `SegPremσ` for one
global σ-thread, consecutive ones linked by `LinkPub`, and `s0` in the first segment's in-relation on
the thread: either SHA-384 collides, or `foldSegments` runs from `s0` to `sN` in the last segment's
out-relation, with `sideR sN = σ (t_out + 1)`. -/
theorem seg_chain_σ (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremσ X nloc ngl sg σ d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InSσ X sg σ d0 s0) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, foldSegments X.toCtx.cfg X.toCtx.p ((d0 :: ds).map SegD.n) s0 = .cont sN ∧
        OutSσ X sg σ ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN :=
  chain_abs X.toCtx.cfg X.toCtx.p SegD.n (SegPremσ X nloc ngl sg σ) (InSσ X sg σ) (OutSσ X sg σ)
    (fun d d' => LinkPub d.pub d'.pub)
    (fun _ hp _ hin => seg_stepσ X hstepgas hg64 hp hin)
    (fun _ _ _ hp' hL _ ho => link_stepσ X hp' hL ho) ds d0 hok hL s0 h0

include hstepgas hg64 in
open NearSpecV3.Wasm.CallCut in
/-- **The σ-pinned chained-segments theorem on lane E's call machine.** -/
theorem seg_chain_csteps_σ (q : CallArgs) (hq : q.cfg = X.toCtx.cfg) (k : EntK)
    (d0 : SegD) (ds : List SegD) (hok : ∀ d ∈ d0 :: ds, SegPremσ X nloc ngl sg σ d)
    (hL : LinkL (fun d d' => LinkPub d.pub d'.pub) (d0 :: ds)) {s0 : St} (h0 : InSσ X sg σ d0 s0)
    (n : Nat) (hn : ((d0 :: ds).map SegD.n).sum ≤ n) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      ∃ sN, CSteps q (.ent X.toCtx.p k (.cont s0) n) (.ent X.toCtx.p k (.cont sN) (n - ((d0 :: ds).map SegD.n).sum)) ∧
        OutSσ X sg σ ((d0 :: ds).getLast (List.cons_ne_nil _ _)) sN := by
  rcases seg_chain_σ X hstepgas hg64 d0 ds hok hL h0 with hb | ⟨sN, h1, h2⟩
  · exact Or.inl hb
  · rw [← hq] at h1
    exact Or.inr ⟨sN, csteps_foldSegments q X.toCtx.p k _ s0 sN n h1 hn, h2⟩

end

end Cuti

#print axioms seg_tombDead_rowsJ
#print axioms seg_tombDeadσ
#print axioms seg_sound_cσ
#print axioms Cuti.seg_stepσ
#print axioms Cuti.link_stepσ
#print axioms Cuti.seg_chain_σ
#print axioms Cuti.seg_chain_csteps_σ

end WasmBase
