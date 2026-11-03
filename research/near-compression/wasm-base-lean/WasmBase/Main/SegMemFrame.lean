import WasmBase.Main.SegIface

/-!
# WasmBase.Main.SegMemFrame — the memory frame of a cut segment (E2E M4c, sub-lane MEM, item 2)

`RelW`/`HeapOK` track only the touched bytes (space-3 live messages).  Here: bytes outside the
in-boundary's space-3 slots, and the page count, are unchanged across a cut segment.

* `RelW.addByte`: a related state stays related when one more space-3 message, the current byte of an
  in-bounds address with no live message, is added to the live set.
* **`CutSeg.frame`** (no per-row reasoning): run the segment's rows from the in-boundary block
  augmented by that byte's message (and the out-boundary block augmented by the same message: the
  bus balance is unchanged); no row consumes it, so it is live at the cut, where `HeapOK` says it
  carries the final byte.  Since `seg` is deterministic, the final state is the segment's.
* `StepPages.step_pages`: a continuing step whose instruction is neither a host call
  (`StepRegs.NonHostI`) nor `memory.grow` keeps `s.pages.size` (every `exec` arm, as `StepRegs`).
* `seg_instr_pagesKeep`: every active instruction row has `PagesKeep` (its record op is `< 0x1FF`,
  `fetch_op_lt`; `memory.grow`'s record op is `opMemGrowX = 0x240`, `recordAtM2_noGrow`).
* `CutSeg.pages` (via `exec_of_rows_cutQ`), **`seg_mem_frame`** (trace level, `seg_sound`'s
  execution premises): `sN.pages.size = s0.pages.size` and every address without a space-3 message in
  `initS` keeps its byte (out-of-bounds addresses read 0 on both sides).

Named premise: **`HostPagesRely`** — a HOST row's step keeps the page count.  Honest runs satisfy it:
NEAR host functions write memory bytes (`writeByte`/`writeBytes`, which keep the page array's size)
and never grow memory; it is part of the host-chip contract (M6), like `HostRegRely`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Adding an untracked byte to the live set -/

/-- **Adding an untracked memory byte.**  A related state stays related when the live set gets one
more space-3 message carrying the current byte of an in-bounds address that has no live message. -/
theorem RelW.addByte {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) {addr tp : Nat}
    (ha : addr < memBytes s) (hfree : ∀ y, live y → y.space = 3 → y.slot ≠ addr) (htp : tp < t) :
    RelW X { E with live := fun y => E.live y ∨ y = encB addr (readByte s addr).toNat tp } s f tps tpl t pc S
      (fun y => live y ∨ y = encB addr (readByte s addr).toNat tp) a b := by
  obtain ⟨T, tpm, hnd, hlt, htpm, hv⟩ := R.heap.mem
  have hnT : addr ∉ T := by
    intro hT
    have hl : E.live (encB addr (readByte s addr).toNat (tpm addr)) :=
      (hv _ rfl).mpr (mem_memView.mpr ⟨addr, hT, rfl⟩)
    exact hfree _ ((R.live _).mpr (Or.inr (Or.inr hl))) rfl rfl
  have hne3 : ∀ y, y = encB addr (readByte s addr).toNat tp → y.space = 3 := by
    rintro y rfl; rfl
  refine { R with
    envSep := fun y hy => ?_
    heap := ⟨R.heap.pages, ⟨addr :: T, fun c => if c = addr then tp else tpm c, List.nodup_cons.mpr ⟨hnT, hnd⟩,
      fun c hc => ?_, fun c hc => ?_, fun y hy => ?_⟩, ?_⟩
    calls := R.calls.mono (Nat.le_refl _) rfl rfl rfl rfl (fun y hy => ?_) rfl
    live := fun y => ?_ }
  · rcases hy with hy | hy
    · exact R.envSep y hy
    · rw [hne3 y hy]; simp only [Env.lsp]; omega
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact ha
    · exact hlt c hc
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp only [ite_true]; exact htp
    · have : c ≠ addr := fun e => hnT (e ▸ hc)
      simp only [this, ite_false]; exact htpm c hc
  · show E.live y ∨ y = _ ↔ _
    rw [hv y hy]
    simp only [memView, List.map_cons, List.mem_cons, ite_true]
    have hmap : List.map (fun c => encB c (readByte s c).toNat (if c = addr then tp else tpm c)) T =
        List.map (fun c => encB c (readByte s c).toNat (tpm c)) T := by
      apply List.map_congr_left; intro c hc
      have : c ≠ addr := fun e => hnT (e ▸ hc)
      simp only [this, ite_false]
    rw [hmap]; exact Or.comm
  · obtain ⟨tpg, hg, hgv⟩ := R.heap.glob
    refine ⟨tpg, hg, fun y hy => ?_⟩
    show E.live y ∨ _ ↔ _
    rw [← hgv y hy]
    constructor
    · rintro (h | h)
      · exact h
      · rw [hne3 y h] at hy; exact absurd hy (by decide)
    · exact Or.inl
  · show E.live y ∨ _ ↔ E.live y
    constructor
    · rintro (h | h)
      · exact h
      · have := hne3 y h; omega
    · exact Or.inl
  · show live y ∨ _ ↔ _ ∨ _ ∨ (E.live y ∨ _)
    rw [R.live y]
    constructor
    · rintro ((h | h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rintro (h | h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr h

/-! ## 2. The byte frame of a cut segment -/

/-- **Byte frame of a cut segment.**  An in-bounds address with no space-3 message in the
in-boundary block keeps its byte across the segment (and stays in bounds).  Proof: run the same
rows from the in-boundary block augmented by that byte's message (`RelW.addByte`); no row touches
it, so it is in the final live set, where `HeapOK` says it carries the final byte. -/
theorem CutSeg.frame {X : Ctx} {sg : Nat → Nat × Nat} {ρ : Type} [DecidableEq ρ] (c : CutSeg X sg ρ)
    (hc : c.st = 0)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64) {s0 sN : St} (h0 : Bnd X sg s0 c.t0 c.S0 c.m0 c.init)
    {addr : Nat} (ha : addr < memBytes s0) (hfree : ∀ y ∈ c.init, y.space = 3 → y.slot ≠ addr)
    (hseg : NearSpecV3.Wasm.seg X.cfg X.p c.len s0 = .cont sN) :
    readByte sN addr = readByte s0 addr ∧ addr < memBytes sN := by
  let x : Msg := encB addr (readByte s0 addr).toNat c.t0
  have hxi : x ∉ c.init := fun h => hfree x h rfl rfl
  let c' : CutSeg X sg ρ :=
    { c with
      init := c.init ++ [x]
      fin := c.fin ++ [x]
      hch := by
        have e1 : ((c.init ++ [x]) ++ c.act.flatMap c.prod).Perm (x :: (c.init ++ c.act.flatMap c.prod)) := by
          rw [List.append_assoc, List.singleton_append]; exact List.perm_middle
        have e2 : ((c.fin ++ [x]) ++ c.act.flatMap c.cons).Perm (x :: (c.fin ++ c.act.flatMap c.cons)) := by
          rw [List.append_assoc, List.singleton_append]; exact List.perm_middle
        exact e1.trans ((c.hch.cons x).trans e2.symm)
      hinit := List.nodup_append.mpr ⟨c.hinit, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha b hb e => by
        rw [List.mem_singleton] at hb; subst e; subst hb; exact hxi ha⟩
      hinitTp := fun y hy => by
        rcases List.mem_append.mp hy with h | h
        · exact c.hinitTp y h
        · rw [List.mem_singleton] at h; subst h; exact Nat.le_refl _ }
  have h0' : Bnd X sg s0 c'.t0 c'.S0 c'.m0 c'.init := by
    obtain ⟨k, pc, sb, cid, hm, E, f, tps, tpl, hsb, hcid, hk, R⟩ := h0
    refine ⟨k, pc, sb, cid, hm, ?_⟩
    have R' := R.addByte (addr := addr) (tp := c.t0) ha (fun y hy h3 => hfree y hy h3) (Nat.lt_succ_self _)
    refine ⟨{ E with live := fun y => E.live y ∨ y = x }, f, tps, tpl, hsb, hcid, hk, ?_⟩
    have e : (fun y => y ∈ c.init ∨ y = x) = (· ∈ c'.init) := by
      funext y; simp [c', List.mem_append]
    exact e ▸ R'
  obtain ⟨sN', h1, h2⟩ := c'.cut hc hstepgas hg64 h0'
  have hl : c'.len = c.len := rfl
  rw [hl, hseg] at h1
  cases h1
  obtain ⟨k, pc, sb, cid, -, E, f, tps, tpl, -, -, -, R⟩ := h2
  have hx : x ∈ c'.fin := List.mem_append_right _ (List.mem_singleton_self x)
  have hlx : E.live x := R.env_msg hx (by simp [x]) (by simp [x, Env.lsp]; omega)
  obtain ⟨e1, e2⟩ := heap_read R.heap hlx
  exact ⟨UInt8.toNat_inj.mp e1, e2⟩

/-! ## 3. A step that is not `memory.grow` nor a host call keeps the page count -/

namespace StepPages
open StepRegs

def PK (r : Res) (s : St) : Prop := ∀ s', r = .cont s' → s'.pages.size = s.pages.size

theorem setFrame_pages (s : St) (f : Frame) : (setFrame s f).pages = s.pages := by
  unfold setFrame; split <;> rfl
theorem popN_pages (s : St) : (popN s).2.pages = s.pages := by rw [popN_snd]; try rfl
theorem popV_pages (s : St) : (popV s).2.pages = s.pages := rfl
theorem popRef_pages (s : St) : (popRef s).2.pages = s.pages := by rw [popRef_snd]; try rfl
theorem pushV_pages (s : St) (v : Val) : (pushV s v).pages = s.pages := rfl
theorem pushI32_pages (s : St) (v : Nat) : (pushI32 s v).pages = s.pages := rfl
theorem pushI64_pages (s : St) (v : Nat) : (pushI64 s v).pages = s.pages := rfl
theorem pushT_pages (s : St) (t : VT) (v : Nat) : (pushT s t v).pages = s.pages := by
  unfold pushT; split <;> rfl
theorem writeByte_size (s : St) (a : Nat) (v : UInt8) : (writeByte s a v).pages.size = s.pages.size := by
  simp [writeByte]
theorem size_foldl {α : Type} (g : St → α → St) (hg : ∀ b a, (g b a).pages.size = b.pages.size)
    (l : List α) (s : St) : (l.foldl g s).pages.size = s.pages.size :=
  foldl_inv (fun b : St => b.pages.size = s.pages.size) g (fun b a h => (hg b a).trans h) l s rfl
theorem writeLE_size (s : St) (a w v : Nat) : (writeLE s a w v).pages.size = s.pages.size := by
  unfold writeLE; simp; apply size_foldl; intros; exact writeByte_size _ _ _
theorem writeBytes_size (s : St) (a : Nat) (d : ByteArray) : (writeBytes s a d).pages.size = s.pages.size := by
  unfold writeBytes; simp; apply size_foldl; intros; exact writeByte_size _ _ _

attribute [local simp] setFrame_pages popN_pages popV_pages popRef_pages popN_pair popRef_pair popV_pair
  pushV_pages pushI32_pages pushI64_pages pushT_pages writeByte_size writeLE_size writeBytes_size

theorem pk_memFill (s : St) (d v n : Nat) : PK (memFill s d v n) s := by
  intro s' h; unfold memFill at h; split at h
  · cases h
  · simp at h; subst h; apply size_foldl; intros; exact writeByte_size _ _ _

theorem pk_memCopy (s : St) (d src n : Nat) : PK (memCopy s d src n) s := by
  intro s' h; unfold memCopy at h; split at h
  · cases h
  · cases h; simp

theorem pk_memInit (s : St) (seg d src n : Nat) : PK (memInit s seg d src n) s := by
  intro s' h; unfold memInit at h; dsimp only at h; split at h
  · cases h
  · cases h; simp

theorem pk_tableInit (s : St) (seg d src n : Nat) : PK (tableInit s seg d src n) s := by
  intro s' h; unfold tableInit at h; dsimp only at h; split at h
  · cases h
  · injection h with h; subst h; rfl

theorem pk_doReturn (p : Prepared) (s : St) : PK (doReturn p s) s := by
  intro s' h; unfold doReturn at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

theorem pk_doBr (p : Prepared) (s : St) (f : Frame) (l : Nat) : PK (doBr p s f l) s := by
  intro s' h; unfold doBr at h
  split at h
  · exact pk_doReturn p s s' h
  · split at h
    · cases h
    · cases h; simp

theorem pk_charge (s : St) (fee : Fee) (c : Nat) : PK (charge s fee c) s := by
  intro s' h; unfold charge at h; dsimp only at h
  by_cases h1 : c * fee.l + fee.c ≥ u64Bound
  · rw [if_pos h1] at h; split at h
    · cases h
    · split at h <;> cases h
  · rw [if_neg h1] at h
    by_cases h2 : c * fee.l + fee.c > s.gas.g
    · rw [if_pos h2] at h; split at h
      · cases h
      · split at h <;> cases h
    · rw [if_neg h2] at h; cases h; rfl

theorem pk_enter (p : Prepared) (s : St) (fi : Nat) : PK (enter p s fi) s := by
  intro s' h; unfold enter at h; dsimp only at h
  cases hf : p.funcs[fi - p.m.imports.size]? with
  | none => rw [hf] at h; cases h
  | some pf =>
    rw [hf] at h; dsimp only at h
    by_cases hc : s.stackRem < pf.stackCharge
    · rw [if_pos hc] at h; split at h <;> cases h
    · rw [if_neg hc] at h
      split at h
      · rename_i s1 hch
        cases h
        have := pk_charge _ _ _ s1 hch
        simp only at this ⊢; rw [this]
      · simp_all

theorem pk_callFunc (cfg : NearCfg) (p : Prepared) (s : St) (fi : Nat) (h : p.m.imports.size ≤ fi) :
    PK (callFunc cfg p s fi) s := by
  intro s' hs; unfold callFunc at hs; rw [dif_neg (by omega)] at hs; exact pk_enter p s fi s' hs

theorem pk_execNum (s s' : St) (op : Nat) (h : execNum s op = .ok s') : s'.pages.size = s.pages.size := by
  unfold execNum at h
  repeat' (split at h)
  all_goals (try simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; done)
    | (subst h; simp_all; done)

theorem pk_execFloat (s s' : St) (op : Nat) (h : execFloat s op = .ok s') : s'.pages.size = s.pages.size := by
  unfold execFloat at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; done)
    | (subst h; simp_all; done)

/-- The instruction is neither a host call nor `memory.grow`. -/
def NoGrowI (p : Prepared) (i : Instr) : Prop := NonHostI p i ∧ i ≠ .memGrow

set_option maxHeartbeats 4000000 in
theorem exec_pages (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (i : Instr)
    (hi : NoGrowI p i) : PK (exec cfg p s f pf i) s := by
  intro s' h
  obtain ⟨hi, hg⟩ := hi
  cases i <;> simp only [NonHostI] at hi <;> (try exact absurd rfl hg) <;> unfold exec at h <;> dsimp only at h
  all_goals (repeat' (split at h))
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; done)
    | (have := pk_doBr _ _ _ _ _ h; simp_all; done)
    | (have := pk_doReturn _ _ _ h; simp_all; done)
    | (have := pk_callFunc _ _ _ _ hi _ h; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := pk_memFill _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := pk_memCopy _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := pk_memInit _ _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := pk_tableInit _ _ _ _ _ s1 heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := pk_execNum _ _ _ heq; simp_all; done)
    | (rename_i _ s1 heq; injection h with h; subst h; have := pk_execFloat _ _ _ heq; simp_all; done)
    | (rename_i hne; exact (hne _ h).elim)
    | (subst h; simp_all; done)

/-- **A step whose instruction is neither a host call nor `memory.grow` keeps the page count.** -/
theorem step_pages {cfg : NearCfg} {p : Prepared} {s s' : St} (h : step cfg p s = .cont s')
    (hi : ∀ f fs pf i, s.frames = f :: fs → p.funcs[f.fn]? = some pf → pf.code[f.pc]? = some i → NoGrowI p i) :
    s'.pages.size = s.pages.size := by
  unfold step at h
  split at h
  · cases h
  · rename_i f fs hfr
    split at h
    · cases h
    · rename_i pf hpf
      split at h
      · cases h
      · rename_i i hci
        have hn := hi f fs pf i hfr hpf hci
        split at h
        · cases h
        · exact exec_pages cfg p s f pf i hn s' h
        · split at h
          · rename_i s1 hc
            have e1 := pk_charge _ _ _ s1 hc
            rw [exec_pages cfg p s1 f pf i hn s' h, e1]
          · rename_i hne; exact (hne _ h).elim

end StepPages

/-! ## 4. Instruction rows keep the page count -/

/-- A row that, from any related state, keeps the page count (the `RegKeep` analogue). -/
def PagesKeep (X : Ctx) (inS : List F) : Prop :=
  ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat)
    (s' : St), RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
    step X.cfg X.p s = .cont s' → s'.pages.size = s.pages.size

theorem pagesKeep_of_code {X : Ctx} {inS : List F}
    (h : ∀ (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop) (a b : Nat),
      RelW X E s f tps tpl t pc S live a b → inS = stMsg (X.offOf E.k + pc) t S 0 E.sb E.cid →
      ∀ i, (X.pfOf E.k).code[pc]? = some i → StepPages.NoGrowI X.p i) :
    PagesKeep X inS := by
  intro E s f tps tpl t pc S live a b s' R hin hs
  refine StepPages.step_pages hs fun f' fs pf i hfr hpf hci => ?_
  rw [R.frames] at hfr
  obtain ⟨rfl, -⟩ := List.cons.inj hfr
  refine h E s f tps tpl t pc S live a b R hin i ?_
  have e : X.pfOf E.k = pf := by
    unfold Ctx.pfOf; rw [← R.fn, hpf]; rfl
  rw [e, ← R.pcEq]; exact hci

/-- A record below `0x1FF` is not `memory.grow`'s (`opMemGrowX = 0x240`). -/
theorem recordAtM2_noGrow {cfg : NearCfg} {p : Prepared} {pf : PFunc} {L : Array (List Label)}
    {H : Array Nat} {off pc : Nat} {cinfo : Nat → Option Nat} {rec : List Nat}
    (hr : recordAtM2 cfg p pf L H off cinfo pc = some rec) {ins : Instr} (hc : pf.code[pc]? = some ins)
    (hop : rec.getD 1 0 < 0x1FF) : ins ≠ .memGrow := by
  rintro rfl
  unfold recordAtM2 at hr
  rw [hc] at hr
  cases hf : feeUnits cfg pf.gas[pc]? with
  | none => simp only [hf] at hr; cases hr; simp [opMemGrowX] at hop
  | some fee => simp only [hf] at hr; cases hr; simp [opMemGrowX] at hop

/-- **Instruction rows keep the page count** (`seg_instr_regKeep`'s argument: the row's record has
op `< 0x1FF`, so its instruction is neither a host call nor `memory.grow`). -/
theorem seg_instr_pagesKeep (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hcode : CodeOK X.toCtx tr) :
    ∀ ρ ∈ actListM2 tr pub, ρ.1 ≠ 22 → PagesKeep X.toCtx (rowInM tr pub ρ) := by
  intro ρ hρ hne
  have hP := P_val
  obtain ⟨t, r⟩ := ρ
  simp only at hne
  rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, ha⟩
  · exact absurd h22 hne
  obtain ⟨ht, hcon, hint⟩ := seg_instr_tab nloc ngl t htI
  have hbit : ∀ i ∈ bcOf (chipM2 t), (tr.cell t r i).toNat ≤ 1 := by
    intro i hi
    have h := H.constr t ht r hr _ (by rw [hcon]; exact bcOf_mem hi)
    simp only [Chips.bool, v, Expr.eval_mul', Expr.eval_sub', Expr.eval_col, Expr.eval_ofNat', Trace.row] at h
    have h' : ((rowNat tr t r i : Nat) : F) * (((rowNat tr t r i : Nat) : F) - ((1 : Nat) : F)) = 0 := by
      simp only [rowNat, Fp.cast_toNat]; exact h
    rcases bool_nat (rowNat_lt tr t r i) h' with h0 | h1 <;> (show rowNat tr t r i ≤ 1; omega)
  obtain ⟨i, hi, hb, hs, hc1, hpc, hop⟩ := fetch_op_lt (instr_fetchOpOk t htI) hbit ha
  have ho := row_occ (pub := pub) ht hr (hint i hi)
  obtain ⟨j, hj, hm⟩ := seg_fetchM2 H X hcode (o := (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)),
    (i.count.eval (tr.row pub t r)).toNat)) ho hb hs hc1
  simp only at hm
  have eI : rowInM tr pub (t, r) = rowIn (chipM2 t) tr pub t r := by
    have ec : chipTM2 t = chipM2 t := by simp [chipTM2, hne]
    simp [rowInM, ec]
  rw [eI]
  refine pagesKeep_of_code fun E s f tps tpl tt pc S live a b R hin ins hins => ?_
  -- the record of `j` is `recordAtM2` at a location `(k, l)`
  obtain ⟨k, l, hk, hl, hoff, hrj⟩ := X.recG hj
  have hrec := X.rec_at hk hl
  have hsz : l < (X.ckOf k).records.size := by rw [(X.factsOf hk).records]; exact hl
  rw [Array.getElem?_eq_getElem hsz] at hrec
  simp only [codeRecM2, hrj, Option.getD_some, Array.getElem?_eq_getElem hsz] at hm
  generalize (X.ckOf k).records[l] = rec at hrec hm
  -- its pc is the row's pc
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
  exact ⟨recordAtM2_nonHost hrec (by simpa using hins) hopN, recordAtM2_noGrow hrec (by simpa using hins) hopN⟩


/-- **The HOST rows' page-count rely** (host-chip contract, M6): a host call's step keeps the page
count (NEAR host functions write memory bytes, never grow it). -/
def HostPagesRely (X : Ctx) (tr : Trace) (pub : List F) : Prop :=
  ∀ ρ ∈ actListM2 tr pub, ρ.1 = 22 → PagesKeep X (rowInM tr pub ρ)

/-! ## 5. The page count and the frame across a segment -/

/-- **The page count across a cut segment**, given that every row keeps it. -/
theorem CutSeg.pages {X : Ctx} {sg : Nat → Nat × Nat} {ρ : Type} [DecidableEq ρ] (c : CutSeg X sg ρ)
    (hc : c.st = 0)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64) {s0 sN : St} (h0 : Bnd X sg s0 c.t0 c.S0 c.m0 c.init)
    (hpk : ∀ r ∈ c.act, PagesKeep X (c.inS r))
    (hseg : NearSpecV3.Wasm.seg X.cfg X.p c.len s0 = .cont sN) :
    sN.pages.size = s0.pages.size := by
  obtain ⟨-, hcQ⟩ := exec_of_rows_cutQ X c.act c.inS c.outS c.cons c.prod c.init c.fin c.pcf c.N c.Sf sg c.st
    c.hst2 c.hrows c.t0 c.S0 c.m0 c.sbf c.cidf c.hst c.hch c.hinit c.hinitTp c.ht c.hfee hstepgas hg64 h0
    (fun s _ => s.pages.size = s0.pages.size)
    (fun r hr E s f tps tpl t pc S live a b s' R hin _ hs hq => by
      show s'.pages.size = s0.pages.size
      rw [hpk r hr E s f tps tpl t pc S live a b s' R hin hs]; exact hq) rfl
  obtain ⟨sN', h1, -, -, h2⟩ := hcQ hc
  have hl : c.len = c.act.length := rfl
  rw [← hl, hseg] at h1
  cases h1
  exact h2

theorem readByte_oob {s : St} {a : Nat} (h : memBytes s ≤ a) : readByte s a = 0 := by
  unfold readByte
  have hps : 0 < pageSize := by decide
  have : s.pages.size ≤ a / pageSize := (Nat.le_div_iff_mul_le hps).mpr (by unfold memBytes at h; exact h)
  rw [Array.getElem?_eq_none this]

/-- SEGB's in-boundary production is the gas register (space 7). -/
theorem segb_send_space : ∀ i ∈ Segb.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true),
    i.msg.head? = some (Expr.c 7) := by decide +kernel

/-- **The memory frame of a segment** (trace level).  Under `seg_sound`'s premises (those the
execution needs) and the HOST rows' page-count rely: the out-state has the in-state's page count,
and every address with no space-3 message in the in-boundary block `initS` keeps its byte. -/
theorem seg_mem_frame (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
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
      (initS tr pub)) :
    ∀ sN, NearSpecV3.Wasm.seg X.toCtx.cfg X.toCtx.p (actListM2 tr pub).length s0 = .cont sN →
      sN.pages.size = s0.pages.size ∧
      ∀ a, (∀ x ∈ initS tr pub, x.space = 3 → x.slot ≠ a) → readByte sN a = readByte s0 a := by
  intro sN hseg
  have hP := P_val
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hlenEq := seg_len H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  let c := segCut X.toCtx H hrows hb hg hst0 hinit ht hfee
  have hpk : ∀ r ∈ c.act, PagesKeep X.toCtx (c.inS r) := by
    intro ρ hρ
    by_cases h22 : ρ.1 = 22
    · exact hpr ρ hρ h22
    · exact seg_instr_pagesKeep X H hcode ρ hρ h22
  have hsz := c.pages rfl hstepgas hg64 h0 hpk hseg
  refine ⟨hsz, fun a ha => ?_⟩
  by_cases hlt : a < memBytes s0
  · exact (c.frame rfl hstepgas hg64 h0 hlt (fun y hy h3 => ha y hy h3) hseg).1
  · have hm : memBytes sN = memBytes s0 := by unfold memBytes; rw [hsz]
    rw [readByte_oob (by omega), readByte_oob (by omega)]

#print axioms RelW.addByte
#print axioms CutSeg.frame
#print axioms StepPages.step_pages
#print axioms seg_instr_pagesKeep
#print axioms CutSeg.pages
#print axioms seg_mem_frame

end WasmBase
