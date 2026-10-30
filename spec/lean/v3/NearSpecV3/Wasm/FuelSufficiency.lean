import NearSpecV3.Wasm.FuelCert
/-!
# Fuel sufficiency (W02, obligations O-W1b … O-W4)

`Wasm/Fuel.lean` proves that raising the step budget changes only fuel-exhausted results. This
module proves that the successor budget `wasmFuel cfg gas` is **never** exhausted, for every
prepared module whose functions carry a valid *fuel certificate*.

## The potential

For a state `s` with call frames `f₀ :: f₁ :: …` let

  `Φ(s) = K · ⌊g / r⌋ + Σ_frames (K · rest(f.pc) + free(f.pc))`

where `r = regular_op_cost`, `K = freeStepFactor cfg = 2 · max_blocks_per_function + 2`, `g` is
the wasm-side gas global, `free(pc)` is the number of zero-fee control instructions at or after
`pc` (O-W1/O-W3's `P`), and `rest(pc)` is the number of costly instructions the current
finite-wasm group still has to run **without a further charge** (O-W4's prepaid credit). `step`
lowers `Φ` by at least one on every continuing step (`step_dec`), so a run started at `Φ < n`
cannot exhaust `n` steps of fuel (`run_ne_fuelOut`), and at entry `Φ ≤ K · ⌊prepaid / r⌋ + F`,
which is below `wasmFuel` (`callEntry_ne_fuelOut`).

## The certificate

`rest`, `free`, a liveness map and the static label stack of every `pc` are data (`FCert`). The
local checks in `certOK` are exactly what the step argument needs, instruction by instruction:

* **O-W1b** (`else` jumps forward): the label an `else` pops has a target past its `pc`.
* **O-W2** (a costly step raises `free` by at most `F`): every label/branch target and the
  successor of every falling-through instruction is live and carries the label stack the
  interpreter will have there; frames are only pushed by calls and popped by returns
  (proved below for every `exec` arm); host functions keep the frames and never refund gas
  (`HostsOK`, proved per host arm in `Wasm/FuelHost.lean`).
* **O-W3**: every `free(pc) ≤ 2 · max_blocks_per_function + 1`.
* **O-W4** (charges happen before execution): at every live charge point the constant fee pays
  `r` for each costly instruction of the group it opens (`fee.c ≥ r · grp`), at a non-charge point
  the credit `rest` covers the instruction and the rest of its group, and every jump target
  (branch target, `if`/`else` target, function entry) needs no credit (`rest = 0`), i.e. it
  starts a finite-wasm group.

The checks are decidable and run in linear time; `buildCert` computes the certificate from the
gas table, `matchBlocks` and finite-wasm's own unreachability flag. That every function that
`prepare` accepts passes `certOK` is the statement `PrepareCertified`; see the evidence README for
its status.
-/
namespace NearSpecV3.Wasm

/-! ## The potential and the invariant -/

def labTK (l : Label) : Nat × Bool := (l.target, l.isLoop)

/-- One frame's share of the potential. -/
def frameΦ (K : Nat) (cd : Nat → FCert) (f : Frame) : Nat := K * (cd f.fn).r f.pc + (cd f.fn).fr f.pc

def Φ (cfg : NearCfg) (cd : Nat → FCert) (s : St) : Nat :=
  freeStepFactor cfg * (s.gas.g / cfg.regularOpCost) + (s.frames.map (frameΦ (freeStepFactor cfg) cd)).sum

/-- Every frame sits at a live position with the label stack its certificate predicts. -/
def FrameInv (cd : Nat → FCert) (f : Frame) : Prop :=
  (cd f.fn).lv f.pc = true ∧ f.labels.map labTK = (cd f.fn).lb f.pc

def Inv (cd : Nat → FCert) (s : St) : Prop := ∀ f ∈ s.frames, FrameInv cd f

/-- Every defined function's certificate checks. -/
def Certified (cfg : NearCfg) (p : Prepared) (cd : Nat → FCert) : Prop :=
  ∀ k pf, p.funcs[k]? = some pf → certOK cfg pf (cd k) = true

/-- Host functions keep the call frames and never give gas back. -/
def HostMono (s s' : St) : Prop :=
  s'.frames = s.frames ∧ s'.gas.remaining ≤ s.gas.remaining ∧ s'.gas.prepaid = s.gas.prepaid

def HostsOK : Prop := ∀ (s : St) (name : String) (h : HM Unit) (u : Unit) (s' : St),
  dispatchArm s name = some h → h.run s = .ok u s' → HostMono s s'

/-! ## Facts about the certificate -/

section cert
variable {cfg : NearCfg} {pf : PFunc} {c : FCert}

theorem certOK_entry (h : certOK cfg pf c = true) :
    c.lv 0 = true ∧ c.r 0 = 0 ∧ c.lb 0 = [(pf.code.size, false)] := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2⟩

theorem certOK_pc (h : certOK cfg pf c = true) {i : Nat} {ins : Instr}
    (hi : pf.code[i]? = some ins) : pcOK cfg pf c i = true := by
  simp only [certOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  apply h.2
  rcases Nat.lt_or_ge i pf.code.size with hl | hl
  · exact hl
  · rw [Array.getElem?_eq_none hl] at hi; cases hi

theorem certOK_free_le (h : certOK cfg pf c = true) (t : Nat) :
    c.fr t ≤ 2 * cfg.maxBlocksPerFunction + 1 := by
  simp only [certOK, Bool.and_eq_true, Array.all_eq_true, decide_eq_true_eq] at h
  unfold FCert.fr
  rw [Array.getD_eq_getD_getElem?]
  cases hx : c.free[t]? with
  | none => simp
  | some v =>
    simp only [Option.getD_some]
    obtain ⟨hlt, hv⟩ := Array.getElem?_eq_some_iff.mp hx
    have := h.1.2 t hlt
    rw [hv] at this
    simpa using this

theorem certOK_free_step (h : certOK cfg pf c = true) {i : Nat} {ins : Instr}
    (hi : pf.code[i]? = some ins) : c.fr (i + 1) + freeBit ins ≤ c.fr i := by
  have := certOK_pc h hi
  simp only [pcOK, hi, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

/-- `free` never increases along the code. -/
theorem certOK_free_mono (h : certOK cfg pf c = true) : ∀ (k i : Nat), c.fr (i + k) ≤ c.fr i
  | 0, i => Nat.le_refl _
  | k + 1, i => by
    have ih := certOK_free_mono h k i
    rcases Nat.lt_or_ge (i + k) pf.code.size with hl | hl
    · have hs := certOK_free_step h (Array.getElem?_eq_getElem hl)
      have : i + (k + 1) = i + k + 1 := by omega
      rw [this]; omega
    · have hsz : c.free.size ≤ pf.code.size + 1 := by
        simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.1.2
      have : c.fr (i + (k + 1)) = 0 := by
        unfold FCert.fr
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
        rfl
      omega

theorem certOK_free_le_of_le (h : certOK cfg pf c = true) {i j : Nat} (hij : i ≤ j) :
    c.fr j ≤ c.fr i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact certOK_free_mono h k i

/-- At a live position: the move checks, and the credit/fee check. -/
theorem certOK_live (h : certOK cfg pf c = true) {i : Nat} {ins : Instr}
    (hi : pf.code[i]? = some ins) (hl : c.lv i = true) :
    moveOK c pf i ins = true ∧
      (pf.gas[i]? = some none → grp c i ins ≤ c.r i) ∧
      (∀ k fee, pf.gas[i]? = some (some (k, fee)) → cfg.regularOpCost * grp c i ins ≤ fee.c) := by
  have := certOK_pc h hi
  simp only [pcOK, hi, hl, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
  refine ⟨this.2.1, ?_, ?_⟩
  · intro hg; have := this.2.2; rw [hg] at this; simpa using this
  · intro k fee hg; have := this.2.2; rw [hg] at this; simpa using this

end cert

/-! ## Machine facts: what each primitive does to frames and gas -/

section machine

/-- `s'` has the frames and the gas of `s`. -/
def Keeps (s s' : St) : Prop := s'.frames = s.frames ∧ s'.gas = s.gas

theorem Keeps.refl (s : St) : Keeps s s := ⟨rfl, rfl⟩
theorem Keeps.trans {a b c : St} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem list_loop_keeps (f : Nat → St → St) (hf : ∀ i s, Keeps s (f i s)) :
    ∀ (l : List Nat) (s : St), Keeps s (Id.run (forIn l s (fun i s => pure (ForInStep.yield (f i s)))))
  | [], s => Keeps.refl s
  | x :: xs, s => by
    simp only [List.forIn_cons]
    exact (hf x s).trans (list_loop_keeps f hf xs _)

theorem keeps_pushV (s : St) (v : Val) : Keeps s (pushV s v) := ⟨rfl, rfl⟩
theorem keeps_popV (s : St) : Keeps s (popV s).2 := ⟨rfl, rfl⟩
theorem keeps_popN (s : St) : Keeps s (popN s).2 := by
  unfold popN; split <;> rename_i h <;> rw [← (Prod.ext_iff.mp h).2] <;> exact keeps_popV s
theorem keeps_popRef (s : St) : Keeps s (popRef s).2 := by
  unfold popRef; split <;> rename_i h <;> rw [← (Prod.ext_iff.mp h).2] <;> exact keeps_popV s
theorem keeps_pushI32 (s : St) (v : Nat) : Keeps s (pushI32 s v) := ⟨rfl, rfl⟩
theorem keeps_pushI64 (s : St) (v : Nat) : Keeps s (pushI64 s v) := ⟨rfl, rfl⟩
theorem keeps_pushT (s : St) (t : VT) (v : Nat) : Keeps s (pushT s t v) := by
  unfold pushT; split <;> exact ⟨rfl, rfl⟩
theorem keeps_writeByte (s : St) (a : Nat) (v : UInt8) : Keeps s (writeByte s a v) := ⟨rfl, rfl⟩

theorem keeps_writeLE (s : St) (a w v : Nat) : Keeps s (writeLE s a w v) := by
  unfold writeLE
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  exact list_loop_keeps (fun i t => writeByte t (a + i) (UInt8.ofNat (v / 256 ^ i % 256)))
    (fun _ _ => ⟨rfl, rfl⟩) _ s


@[simp] theorem popV_snd_frames (s : St) : (popV s).2.frames = s.frames := rfl
@[simp] theorem popV_snd_gas (s : St) : (popV s).2.gas = s.gas := rfl
@[simp] theorem popN_snd_frames (s : St) : (popN s).2.frames = s.frames := (keeps_popN s).1
@[simp] theorem popN_snd_gas (s : St) : (popN s).2.gas = s.gas := (keeps_popN s).2
@[simp] theorem popRef_snd_frames (s : St) : (popRef s).2.frames = s.frames := (keeps_popRef s).1
@[simp] theorem popRef_snd_gas (s : St) : (popRef s).2.gas = s.gas := (keeps_popRef s).2
@[simp] theorem pushV_frames (s : St) v : (pushV s v).frames = s.frames := rfl
@[simp] theorem pushV_gas (s : St) v : (pushV s v).gas = s.gas := rfl
@[simp] theorem pushI32_frames (s : St) v : (pushI32 s v).frames = s.frames := rfl
@[simp] theorem pushI32_gas (s : St) v : (pushI32 s v).gas = s.gas := rfl
@[simp] theorem pushI64_frames (s : St) v : (pushI64 s v).frames = s.frames := rfl
@[simp] theorem pushI64_gas (s : St) v : (pushI64 s v).gas = s.gas := rfl
@[simp] theorem pushT_frames (s : St) t v : (pushT s t v).frames = s.frames := (keeps_pushT s t v).1
@[simp] theorem pushT_gas (s : St) t v : (pushT s t v).gas = s.gas := (keeps_pushT s t v).2
@[simp] theorem writeLE_frames (s : St) a w v : (writeLE s a w v).frames = s.frames := (keeps_writeLE s a w v).1
@[simp] theorem writeLE_gas (s : St) a w v : (writeLE s a w v).gas = s.gas := (keeps_writeLE s a w v).2

def StepsOn (s : St) (f : Frame) (s' : St) : Prop :=
  ∃ s'' L, s''.frames = s.frames ∧ s''.gas = s.gas ∧ s' = setFrame s'' { f with pc := f.pc + 1, locals := L }


def isData : Instr → Bool
  | .unreachable | .block _ | .loop _ | .if_ _ | .else_ | .end_ | .br _ | .brIf _ | .brTable _ _
  | .ret | .call _ | .callIndirect _ _ => false
  | _ => true

theorem memFill_keeps (s : St) d v n s1 (h : memFill s d v n = .cont s1) : Keeps s s1 := by
  unfold memFill at h
  split at h
  · cases h
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
    cases h
    exact list_loop_keeps (fun i t => writeByte t (d + i) (UInt8.ofNat v)) (fun _ _ => ⟨rfl, rfl⟩) _ s


theorem list_loop'_keeps : ∀ (l : List Nat) (f : (i : Nat) → i ∈ l → St → St)
    (_ : ∀ i h s, Keeps s (f i h s)) (s : St),
    Keeps s (Id.run (forIn' l s (fun i h s => pure (ForInStep.yield (f i h s)))))
  | [], _, _, s => Keeps.refl s
  | x :: xs, f, hf, s => by
    simp only [List.forIn'_cons]
    exact (hf x _ s).trans (list_loop'_keeps xs _ (fun i h t => hf i _ t) _)

theorem list_loop'_keeps2 : ∀ (l : List Nat) (body : (i : Nat) → i ∈ l → St → Id (ForInStep St))
    (_ : ∀ i h s, ∃ t, body i h s = .yield t ∧ Keeps s t) (s : St), Keeps s (Id.run (forIn' l s body))
  | [], _, _, s => Keeps.refl s
  | x :: xs, body, hb, s => by
    simp only [List.forIn'_cons]
    obtain ⟨t, ht, hk⟩ := hb x (List.mem_cons_self) s
    rw [ht]
    exact hk.trans (list_loop'_keeps2 xs _ (fun i h t => hb i _ t) _)

theorem keeps_writeBytes (s : St) (a : Nat) (d : ByteArray) : Keeps s (writeBytes s a d) := by
  unfold writeBytes
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply list_loop'_keeps2
  intro i h t
  exact ⟨_, rfl, rfl, rfl⟩

theorem memCopy_keeps (s : St) d src n s1 (h : memCopy s d src n = .cont s1) : Keeps s s1 := by
  unfold memCopy at h; split at h
  · cases h
  · cases h; exact keeps_writeBytes _ _ _

theorem memInit_keeps (s : St) seg d src n s1 (h : memInit s seg d src n = .cont s1) : Keeps s s1 := by
  simp only [memInit] at h; split at h
  · cases h
  · cases h; exact keeps_writeBytes _ _ _

theorem tableInit_keeps (s : St) seg d src n s1 (h : tableInit s seg d src n = .cont s1) : Keeps s s1 := by
  simp only [tableInit] at h; split at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

theorem execNum_keeps (s : St) op s1 (h : execNum s op = .ok s1) : Keeps s s1 := by
  unfold execNum at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨by simp, by simp⟩)
    | skip

theorem execFloat_keeps (s : St) op s1 (h : execFloat s op = .ok s1) : Keeps s s1 := by
  simp only [execFloat] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨by simp, by simp⟩)
    | skip

set_option hygiene false in
macro "data_tac" : tactic => `(tactic| (
  simp only [exec] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; exact ⟨_, _, by simp, by simp, rfl⟩)
    | (rename_i hne; exact absurd h (hne _))
    | (cases h; rename_i heq; first
        | (have hk := memCopy_keeps _ _ _ _ _ heq; exact ⟨_, _, hk.1.trans (by simp), hk.2.trans (by simp), rfl⟩)
        | (have hk := memInit_keeps _ _ _ _ _ _ heq; exact ⟨_, _, hk.1.trans (by simp), hk.2.trans (by simp), rfl⟩)
        | (have hk := memFill_keeps _ _ _ _ _ heq; exact ⟨_, _, hk.1.trans (by simp), hk.2.trans (by simp), rfl⟩)
        | (have hk := tableInit_keeps _ _ _ _ _ _ heq; exact ⟨_, _, hk.1.trans (by simp), hk.2.trans (by simp), rfl⟩)
        | (have hk := execNum_keeps _ _ _ heq; exact ⟨_, _, hk.1.trans (by simp), hk.2.trans (by simp), rfl⟩)
        | (have hk := execFloat_keeps _ _ _ heq; exact ⟨_, _, hk.1.trans (by simp), hk.2.trans (by simp), rfl⟩))))

theorem ex_nop (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) 
    (h : exec cfg p s f pf (.nop ) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_refNull (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (t : VT)
    (h : exec cfg p s f pf (.refNull t) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_refIsNull (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) 
    (h : exec cfg p s f pf (.refIsNull ) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_refFunc (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.refFunc x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_drop (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) 
    (h : exec cfg p s f pf (.drop ) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_select (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (t : Option VT)
    (h : exec cfg p s f pf (.select t) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_localGet (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.localGet x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_localSet (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.localSet x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_localTee (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.localTee x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_globalGet (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.globalGet x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_globalSet (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.globalSet x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_tableGet (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.tableGet x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_tableSet (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.tableSet x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_tableSize (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.tableSize x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_tableGrow (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.tableGrow x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_tableFill (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.tableFill x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_tableCopy (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x y : Nat)
    (h : exec cfg p s f pf (.tableCopy x y) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_tableInit (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x y : Nat)
    (h : exec cfg p s f pf (.tableInit x y) = .cont s') : StepsOn s f s' := by
  simp only [exec] at h
  split at h
  · rename_i s1 heq
    cases h
    have hk := tableInit_keeps _ _ _ _ _ _ heq
    exact ⟨_, _, hk.1.trans (by simp), hk.2.trans (by simp), rfl⟩
  · rename_i hne; exact absurd h (hne _)

theorem ex_elemDrop (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.elemDrop x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_load (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x y z : Nat)
    (h : exec cfg p s f pf (.load x y z) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_store (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x y z : Nat)
    (h : exec cfg p s f pf (.store x y z) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_memSize (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) 
    (h : exec cfg p s f pf (.memSize ) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_memGrow (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) 
    (h : exec cfg p s f pf (.memGrow ) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_memCopy (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) 
    (h : exec cfg p s f pf (.memCopy ) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_memFill (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) 
    (h : exec cfg p s f pf (.memFill ) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_memInit (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.memInit x) = .cont s') : StepsOn s f s' := by
  simp only [exec] at h
  split at h
  · rename_i s1 heq
    cases h
    have hk := memInit_keeps _ _ _ _ _ _ heq
    exact ⟨_, _, hk.1.trans (by simp), hk.2.trans (by simp), rfl⟩
  · rename_i hne; exact absurd h (hne _)

theorem ex_dataDrop (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.dataDrop x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_i32Const (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : UInt32)
    (h : exec cfg p s f pf (.i32Const x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_i64Const (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : UInt64)
    (h : exec cfg p s f pf (.i64Const x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_num (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.num x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_float (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : Nat)
    (h : exec cfg p s f pf (.float x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_floatLoad (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x y z : Nat)
    (h : exec cfg p s f pf (.floatLoad x y z) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_floatStore (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x y z : Nat)
    (h : exec cfg p s f pf (.floatStore x y z) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_f32Const (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : UInt32)
    (h : exec cfg p s f pf (.f32Const x) = .cont s') : StepsOn s f s' := by data_tac

theorem ex_f64Const (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St) (x : UInt64)
    (h : exec cfg p s f pf (.f64Const x) = .cont s') : StepsOn s f s' := by data_tac


/-- Every data (non-control, non-call) instruction continues at `pc + 1` with the frames and the
gas it found (O-W2 for those arms). -/
theorem exec_data (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (s' : St)
    (ins : Instr) (hd : isData ins = true) (h : exec cfg p s f pf ins = .cont s') : StepsOn s f s' := by
  cases ins <;> simp only [isData, Bool.false_eq_true] at hd
  · exact ex_nop cfg p s f pf s' h
  · exact ex_refNull cfg p s f pf s' _ h
  · exact ex_refIsNull cfg p s f pf s' h
  · exact ex_refFunc cfg p s f pf s' _ h
  · exact ex_drop cfg p s f pf s' h
  · exact ex_select cfg p s f pf s' _ h
  · exact ex_localGet cfg p s f pf s' _ h
  · exact ex_localSet cfg p s f pf s' _ h
  · exact ex_localTee cfg p s f pf s' _ h
  · exact ex_globalGet cfg p s f pf s' _ h
  · exact ex_globalSet cfg p s f pf s' _ h
  · exact ex_tableGet cfg p s f pf s' _ h
  · exact ex_tableSet cfg p s f pf s' _ h
  · exact ex_tableSize cfg p s f pf s' _ h
  · exact ex_tableGrow cfg p s f pf s' _ h
  · exact ex_tableFill cfg p s f pf s' _ h
  · exact ex_tableCopy cfg p s f pf s' _ _ h
  · exact ex_tableInit cfg p s f pf s' _ _ h
  · exact ex_elemDrop cfg p s f pf s' _ h
  · exact ex_load cfg p s f pf s' _ _ _ h
  · exact ex_store cfg p s f pf s' _ _ _ h
  · exact ex_memSize cfg p s f pf s' h
  · exact ex_memGrow cfg p s f pf s' h
  · exact ex_memCopy cfg p s f pf s' h
  · exact ex_memFill cfg p s f pf s' h
  · exact ex_memInit cfg p s f pf s' _ h
  · exact ex_dataDrop cfg p s f pf s' _ h
  · exact ex_i32Const cfg p s f pf s' _ h
  · exact ex_i64Const cfg p s f pf s' _ h
  · exact ex_num cfg p s f pf s' _ h
  · exact ex_float cfg p s f pf s' _ h
  · exact ex_floatLoad cfg p s f pf s' _ _ _ h
  · exact ex_floatStore cfg p s f pf s' _ _ _ h
  · exact ex_f32Const cfg p s f pf s' _ h
  · exact ex_f64Const cfg p s f pf s' _ h

theorem setFrame_gas' (s : St) (F : Frame) : (setFrame s F).gas = s.gas := by
  unfold setFrame; split <;> rfl

/-- A continuing charge only lowers `g`, by the charged amount. -/
theorem charge_spec (s : St) (fee : Fee) (cnt : Nat) (s1 : St) (h : charge s fee cnt = .cont s1) :
    s1.frames = s.frames ∧ cnt * fee.l + fee.c ≤ s.gas.g ∧ s1.gas.g = s.gas.g - (cnt * fee.l + fee.c) ∧
      s1.gas.prepaid = s.gas.prepaid := by
  simp only [charge] at h
  by_cases h1 : cnt * fee.l + fee.c ≥ u64Bound
  · simp only [h1, ite_true] at h
    repeat' split at h
    all_goals cases h
  · simp only [h1, ite_false] at h
    by_cases h2 : cnt * fee.l + fee.c > s.gas.g
    · simp only [h2, ite_true] at h
      repeat' split at h
      all_goals cases h
    · simp only [h2, ite_false] at h
      cases h
      exact ⟨rfl, by omega, rfl, rfl⟩

/-- `CallingHost`/`ReturningFromWasm`: after a sync, `remaining = g` (or less). -/
theorem sync_spec (s s1 : St) (h : sync s = .ok s1) :
    s1.frames = s.frames ∧ s1.gas.remaining ≤ s.gas.g ∧ s1.gas.prepaid = s.gas.prepaid := by
  simp only [sync] at h
  split at h
  · rename_i h0
    cases h
    refine ⟨rfl, ?_, rfl⟩
    omega
  · rename_i h0
    split at h
    · rename_i gs hb
      cases h
      simp only [burn] at hb
      split at hb
      · cases hb
      · split at hb
        · cases hb
          refine ⟨rfl, ?_, rfl⟩
          simp only [Gas.remaining, Gas.used] at h0 ⊢
          omega
        · simp only [processGasLimit] at hb
          cases hb
    · cases h

/-- A host call keeps the frames and does not raise `g` (O-W2, host arms, given `HostsOK`). -/
theorem callHost_spec (hh : HostsOK) (s s' : St) (name : String) (h : callHost s name = .cont s') :
    s'.frames = s.frames ∧ s'.gas.g ≤ s.gas.g ∧ s'.gas.prepaid = s.gas.prepaid := by
  unfold callHost at h
  split at h
  · cases h
  · cases hs : sync s with
    | error e => rw [hs] at h; cases h
    | ok s1 =>
      rw [hs] at h
      simp only at h
      obtain ⟨hf1, hg1, hp1⟩ := sync_spec s s1 hs
      cases hd : dispatchArm s1 name with
      | none => rw [hd] at h; cases h
      | some hm =>
        rw [hd] at h
        simp only at h
        cases hr : hm.run s1 with
        | ok u s2 =>
          rw [hr] at h
          cases h
          obtain ⟨hf2, hg2, hp2⟩ := hh s1 name hm u s2 hd hr
          exact ⟨hf2.trans hf1, Nat.le_trans hg2 hg1, hp2.trans hp1⟩
        | error e s2 =>
          rw [hr] at h
          simp only at h
          split at h <;> cases h

/-- `enter` pushes one frame at `pc = 0` with the function label, and does not raise `g`. -/
theorem enter_spec (p : Prepared) (s s' : St) (fi : Nat) (h : enter p s fi = .cont s') :
    ∃ pf, p.funcs[fi - p.m.imports.size]? = some pf ∧ s'.gas.g ≤ s.gas.g ∧
      s'.gas.prepaid = s.gas.prepaid ∧
      ∃ fr : Frame, s'.frames = fr :: s.frames ∧ fr.fn = fi - p.m.imports.size ∧ fr.pc = 0 ∧
        fr.labels.map labTK = [(pf.code.size, false)] := by
  unfold enter at h
  simp only at h
  split at h
  · cases h
  · rename_i pf hpf
    split at h
    · split at h <;> cases h
    · split at h
      · rename_i s2 hc
        cases h
        obtain ⟨hf2, _, hg2, hp2⟩ := charge_spec _ _ _ _ hc
        refine ⟨pf, hpf, ?_, ?_, ?_⟩
        · simp only; rw [hg2]; simp only; omega
        · simp only; rw [hp2]
        · exact ⟨_, by simp only; rw [hf2], rfl, rfl, by simp [labTK]⟩
      · rename_i r hne; exact absurd h (hne _)

theorem doReturn_spec (p : Prepared) (s s' : St) (f : Frame) (fs : List Frame)
    (hf : s.frames = f :: fs) (h : doReturn p s = .cont s') : s'.frames = fs ∧ s'.gas = s.gas := by
  unfold doReturn at h
  rw [hf] at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩

/-- The frame after a taken branch to `lab` at depth `l`. -/
def brFrame (f : Frame) (lab : Label) (l : Nat) : Frame :=
  { f with pc := lab.target, labels := if lab.isLoop then f.labels.drop l else f.labels.drop (l + 1) }

theorem doBr_spec (p : Prepared) (s s' : St) (f : Frame) (fs : List Frame) (l : Nat)
    (hf : s.frames = f :: fs) (h : doBr p s f l = .cont s') :
    (s'.frames = fs ∧ s'.gas = s.gas) ∨
      (l + 1 < f.labels.length ∧ ∃ lab, f.labels[l]? = some lab ∧ s'.gas = s.gas ∧
        s'.frames = brFrame f lab l :: fs) := by
  unfold doBr at h
  split at h
  · exact .inl (doReturn_spec p s s' f fs hf h)
  · rename_i hl
    split at h
    · cases h
    · rename_i lab hlab
      cases h
      refine .inr ⟨by omega, lab, hlab, by simp [setFrame_gas'], ?_⟩
      exact setFrame_frames (by simpa using hf) _

end machine

/-! ## One step lowers the potential -/

/-- `s'` has at most the gas global of `s1` and the same prepaid gas. -/
def GasLe (s1 s' : St) : Prop := s'.gas.g ≤ s1.gas.g ∧ s'.gas.prepaid = s1.gas.prepaid

theorem GasLe.of_eq {s1 s' : St} (h : s'.gas = s1.gas) : GasLe s1 s' :=
  ⟨Nat.le_of_eq (by rw [h]), by rw [h]⟩

section potential
variable {cfg : NearCfg} {cd : Nat → FCert}

/-- The potential available to the instruction at the top frame `f` once its charge (if any)
is paid: the gas term, the group's credits, `free(pc)` and the frames below. -/
def budget (cfg : NearCfg) (cd : Nat → FCert) (g : Nat) (f : Frame) (fs : List Frame) (ins : Instr) :
    Nat :=
  freeStepFactor cfg * (g / cfg.regularOpCost) + freeStepFactor cfg * grp (cd f.fn) f.pc ins +
    (cd f.fn).fr f.pc + (fs.map (frameΦ (freeStepFactor cfg) cd)).sum

theorem Φ_of_frames (s : St) (top : List Frame) (fs : List Frame) (hf : s.frames = top ++ fs) :
    Φ cfg cd s = freeStepFactor cfg * (s.gas.g / cfg.regularOpCost) +
      (top.map (frameΦ (freeStepFactor cfg) cd)).sum + (fs.map (frameΦ (freeStepFactor cfg) cd)).sum := by
  unfold Φ; rw [hf, List.map_append, List.sum_append, Nat.add_assoc]

theorem inv_of_frames {s : St} {top fs : List Frame} (hf : s.frames = top ++ fs)
    (ht : ∀ g ∈ top, FrameInv cd g) (hfs : ∀ g ∈ fs, FrameInv cd g) : Inv cd s := by
  intro g hg; rw [hf, List.mem_append] at hg
  rcases hg with hg | hg
  · exact ht g hg
  · exact hfs g hg

theorem gas_term_le {s1 s' : St} (hg : s'.gas.g ≤ s1.gas.g) :
    freeStepFactor cfg * (s'.gas.g / cfg.regularOpCost) ≤ freeStepFactor cfg * (s1.gas.g / cfg.regularOpCost) :=
  Nat.mul_le_mul_left _ (Nat.div_le_div_right hg)

theorem grp_ge (c : FCert) (i : Nat) (ins : Instr) : costBit ins ≤ grp c i ins := by
  unfold grp; omega

theorem grp_falls (c : FCert) (i : Nat) (ins : Instr) (h : fallsThrough ins = true) :
    grp c i ins = costBit ins + c.r (i + 1) := by
  unfold grp; rw [h]; rfl

theorem pay_fall {K a b : Nat} (ins : Instr) (hK : 1 ≤ K) (h : a + freeBit ins ≤ b) :
    a + 1 ≤ K * costBit ins + b := by
  unfold costBit; unfold freeBit at h
  cases hfr : isFreeInstr ins
  · simp only [hfr] at h ⊢; simp at h ⊢; omega
  · simp only [hfr] at h ⊢; simp at h ⊢; omega

theorem dec_fall {s1 s' : St} {f f' : Frame} {fs : List Frame} {ins : Instr}
    (hfr : s'.frames = f' :: fs) (hg : GasLe s1 s') (hfn : f'.fn = f.fn)
    (hpc : f'.pc = f.pc + 1) (hlv : (cd f.fn).lv (f.pc + 1) = true)
    (hlab : f'.labels.map labTK = (cd f.fn).lb (f.pc + 1)) (hfalls : fallsThrough ins = true)
    (hfree : (cd f.fn).fr (f.pc + 1) + freeBit ins ≤ (cd f.fn).fr f.pc)
    (hK : 1 ≤ freeStepFactor cfg) (hfs : ∀ g ∈ fs, FrameInv cd g) :
    Inv cd s' ∧ s'.gas.prepaid = s1.gas.prepaid ∧ Φ cfg cd s' + 1 ≤ budget cfg cd s1.gas.g f fs ins := by
  refine ⟨inv_of_frames (top := [f']) hfr ?_ hfs, hg.2, ?_⟩
  · intro g hg; simp only [List.mem_singleton] at hg; subst hg
    exact ⟨by rw [hfn, hpc]; exact hlv, by rw [hfn, hpc]; exact hlab⟩
  · rw [Φ_of_frames (cd := cd) s' [f'] fs hfr]
    unfold budget
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, frameΦ, hfn, hpc,
      grp_falls _ _ _ hfalls, Nat.mul_add]
    have h1 := gas_term_le (cfg := cfg) hg.1
    have h2 := pay_fall ins hK hfree
    generalize freeStepFactor cfg * (s'.gas.g / cfg.regularOpCost) = a at *
    generalize freeStepFactor cfg * (s1.gas.g / cfg.regularOpCost) = b at *
    generalize freeStepFactor cfg * costBit ins = x at *
    omega

theorem dec_jump {s1 s' : St} {f f' : Frame} {fs : List Frame} {ins : Instr} {t : Nat}
    {L : List (Nat × Bool)}
    (hfr : s'.frames = f' :: fs) (hg : GasLe s1 s') (hfn : f'.fn = f.fn)
    (hpc : f'.pc = t) (hj : jumpOK (cd f.fn) t L = true) (hlab : f'.labels.map labTK = L)
    (hpay : (cd f.fn).fr t + 1 ≤ freeStepFactor cfg * costBit ins + (cd f.fn).fr f.pc)
    (hfs : ∀ g ∈ fs, FrameInv cd g) :
    Inv cd s' ∧ s'.gas.prepaid = s1.gas.prepaid ∧ Φ cfg cd s' + 1 ≤ budget cfg cd s1.gas.g f fs ins := by
  simp only [jumpOK, Bool.and_eq_true, decide_eq_true_eq] at hj
  obtain ⟨⟨hlv, hr0⟩, hlb⟩ := hj
  refine ⟨inv_of_frames (top := [f']) hfr ?_ hfs, hg.2, ?_⟩
  · intro g hg; simp only [List.mem_singleton] at hg; subst hg
    exact ⟨by rw [hfn, hpc]; exact hlv, by rw [hfn, hpc, hlb]; exact hlab⟩
  · rw [Φ_of_frames (cd := cd) s' [f'] fs hfr]
    unfold budget
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, frameΦ, hfn, hpc, hr0,
      Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    have h1 := gas_term_le (cfg := cfg) hg.1
    have h3 := Nat.mul_le_mul_left (freeStepFactor cfg) (grp_ge (cd f.fn) f.pc ins)
    generalize freeStepFactor cfg * (s'.gas.g / cfg.regularOpCost) = a at *
    generalize freeStepFactor cfg * (s1.gas.g / cfg.regularOpCost) = b at *
    generalize freeStepFactor cfg * costBit ins = x at *
    generalize freeStepFactor cfg * grp (cd f.fn) f.pc ins = y at *
    omega

theorem dec_pop {s1 s' : St} {f : Frame} {fs : List Frame} {ins : Instr}
    (hfr : s'.frames = fs) (hg : GasLe s1 s')
    (hpay : 1 ≤ freeStepFactor cfg * costBit ins + (cd f.fn).fr f.pc)
    (hfs : ∀ g ∈ fs, FrameInv cd g) :
    Inv cd s' ∧ s'.gas.prepaid = s1.gas.prepaid ∧ Φ cfg cd s' + 1 ≤ budget cfg cd s1.gas.g f fs ins := by
  refine ⟨inv_of_frames (top := []) (by simpa using hfr) (by simp) hfs, hg.2, ?_⟩
  rw [Φ_of_frames (cd := cd) s' [] fs (by simpa using hfr)]
  unfold budget
  simp only [List.map_nil, List.sum_nil, Nat.add_zero]
  have h1 := gas_term_le (cfg := cfg) hg.1
  have h3 := Nat.mul_le_mul_left (freeStepFactor cfg) (grp_ge (cd f.fn) f.pc ins)
  generalize freeStepFactor cfg * (s'.gas.g / cfg.regularOpCost) = a at *
  generalize freeStepFactor cfg * (s1.gas.g / cfg.regularOpCost) = b at *
  generalize freeStepFactor cfg * costBit ins = x at *
  generalize freeStepFactor cfg * grp (cd f.fn) f.pc ins = y at *
  omega

theorem dec_call {s1 s' : St} {f f' fr : Frame} {fs : List Frame} {ins : Instr}
    (hfr : s'.frames = fr :: f' :: fs) (hg : GasLe s1 s') (hfn : f'.fn = f.fn)
    (hpc : f'.pc = f.pc + 1) (hlv : (cd f.fn).lv (f.pc + 1) = true)
    (hlab : f'.labels.map labTK = (cd f.fn).lb (f.pc + 1)) (hfalls : fallsThrough ins = true)
    (hcost : costBit ins = 1)
    (hfree : (cd f.fn).fr (f.pc + 1) + freeBit ins ≤ (cd f.fn).fr f.pc)
    (hcal : FrameInv cd fr) (hcr : (cd fr.fn).r fr.pc = 0)
    (hcf : (cd fr.fn).fr fr.pc + 1 ≤ freeStepFactor cfg)
    (hfs : ∀ g ∈ fs, FrameInv cd g) :
    Inv cd s' ∧ s'.gas.prepaid = s1.gas.prepaid ∧ Φ cfg cd s' + 1 ≤ budget cfg cd s1.gas.g f fs ins := by
  refine ⟨inv_of_frames (top := [fr, f']) hfr ?_ hfs, hg.2, ?_⟩
  · intro g hg; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with hg | hg <;> subst hg
    · exact hcal
    · exact ⟨by rw [hfn, hpc]; exact hlv, by rw [hfn, hpc]; exact hlab⟩
  · rw [Φ_of_frames (cd := cd) s' [fr, f'] fs hfr]
    unfold budget
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, frameΦ, hfn, hpc, hcr,
      grp_falls _ _ _ hfalls, Nat.mul_add, hcost, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    have h1 := gas_term_le (cfg := cfg) hg.1
    have hcb : freeBit ins = 0 := by have := costBit_add_freeBit ins; omega
    rw [hcb] at hfree
    generalize freeStepFactor cfg * (s'.gas.g / cfg.regularOpCost) = a at *
    generalize freeStepFactor cfg * (s1.gas.g / cfg.regularOpCost) = b at *
    generalize freeStepFactor cfg * (cd f.fn).r (f.pc + 1) = y at *
    omega

end potential

/-! ## Every `exec` arm -/

section execdec
variable {cfg : NearCfg} {p : Prepared} {cd : Nat → FCert}

theorem freeStepFactor_pos (cfg : NearCfg) : 1 ≤ freeStepFactor cfg := by
  unfold freeStepFactor; omega

theorem pay_costly {c : FCert} {pf : PFunc} (hc : certOK cfg pf c = true) (t pc : Nat) :
    c.fr t + 1 ≤ freeStepFactor cfg * 1 + c.fr pc := by
  have := certOK_free_le hc t
  unfold freeStepFactor; omega

theorem isData_moveOK {c : FCert} {pf : PFunc} {i : Nat} {ins : Instr} (hd : isData ins = true)
    (h : moveOK c pf i ins = true) : ftOK c i (c.lb i) = true := by
  cases ins <;> simp only [isData, Bool.false_eq_true] at hd <;> exact h

theorem isData_falls {ins : Instr} (hd : isData ins = true) : fallsThrough ins = true := by
  cases ins <;> simp only [isData, Bool.false_eq_true] at hd <;> rfl

theorem isData_cost {ins : Instr} (hd : isData ins = true) : costBit ins = 1 := by
  cases ins <;> simp only [isData, Bool.false_eq_true] at hd <;> rfl

theorem labTK_map_drop (L : List Label) (k : Nat) : (L.drop k).map labTK = (L.map labTK).drop k := by
  rw [List.map_drop]

/-- A taken or returning branch (`br`, `br_if`, `br_table`), from a state with the frames and
the gas of `s1`. -/
theorem dec_br {pf : PFunc} {s1 s2 s' : St} {f : Frame}
    {fs : List Frame} {ins : Instr} {l : Nat} (hc : certOK cfg pf (cd f.fn) = true)
    (hs2 : s2.frames = f :: fs) (hg2 : s2.gas = s1.gas)
    (hlab : f.labels.map labTK = (cd f.fn).lb f.pc) (hb : brOK (cd f.fn) f.pc l = true)
    (hcost : costBit ins = 1) (hfs : ∀ g ∈ fs, FrameInv cd g)
    (h : doBr p s2 f l = .cont s') :
    Inv cd s' ∧ s'.gas.prepaid = s1.gas.prepaid ∧ Φ cfg cd s' + 1 ≤ budget cfg cd s1.gas.g f fs ins := by
  rcases doBr_spec p s2 s' f fs l hs2 h with ⟨hfr, hg⟩ | ⟨hl, lab, hlab', hg, hfr⟩
  · refine dec_pop hfr (GasLe.of_eq (by rw [hg, hg2])) ?_ hfs
    rw [hcost]; have := freeStepFactor_pos cfg; omega
  · have hlen : (f.labels.map labTK).length = f.labels.length := List.length_map _
    rw [hlab] at hlen
    unfold brOK at hb
    rw [if_neg (show ¬(l + 1 ≥ ((cd f.fn).lb f.pc).length) by omega)] at hb
    have hget : ((cd f.fn).lb f.pc)[l]? = some (labTK lab) := by
      rw [← hlab, List.getElem?_map, hlab']; rfl
    rw [hget] at hb
    simp only [labTK] at hb
    refine dec_jump hfr (GasLe.of_eq (by rw [hg, hg2])) rfl rfl hb ?_ ?_ hfs
    · simp only [brFrame]
      split <;> rename_i hh <;> simp [hh, labTK_map_drop, hlab]
    · rw [hcost]; exact pay_costly hc _ _

/-- A call to an import or a defined function. -/
theorem dec_callFunc (hcert : Certified cfg p cd) (hhost : HostsOK) {pf : PFunc}
    {s1 s2 s' : St} {f : Frame} {fs : List Frame} {ins : Instr} {fi : Nat}
    (_hc : certOK cfg pf (cd f.fn) = true)
    (hs2 : s2.frames = f :: fs) (hg2 : s2.gas = s1.gas)
    (hlab : f.labels.map labTK = (cd f.fn).lb f.pc) (hft : ftOK (cd f.fn) f.pc ((cd f.fn).lb f.pc) = true)
    (hfalls : fallsThrough ins = true) (hcost : costBit ins = 1)
    (hfree : (cd f.fn).fr (f.pc + 1) + freeBit ins ≤ (cd f.fn).fr f.pc)
    (hfs : ∀ g ∈ fs, FrameInv cd g)
    (h : callFunc cfg p (setFrame s2 { f with pc := f.pc + 1 }) fi = .cont s') :
    Inv cd s' ∧ s'.gas.prepaid = s1.gas.prepaid ∧ Φ cfg cd s' + 1 ≤ budget cfg cd s1.gas.g f fs ins := by
  simp only [ftOK, Bool.and_eq_true, decide_eq_true_eq] at hft
  have hsf := setFrame_frames hs2 { f with pc := f.pc + 1 }
  have hsg : (setFrame s2 { f with pc := f.pc + 1 }).gas = s1.gas := by rw [setFrame_gas', hg2]
  unfold callFunc at h
  split at h
  · obtain ⟨hfr, hg, hp⟩ := callHost_spec hhost _ _ _ h
    rw [hsf] at hfr; rw [hsg] at hg hp
    exact dec_fall hfr ⟨hg, hp⟩ rfl rfl hft.1 (by rw [hft.2]; exact hlab) hfalls hfree
      (freeStepFactor_pos cfg) hfs
  · obtain ⟨pf', hpf', hg, hp, fr, hfr, hfn, hpc, hlb⟩ := enter_spec p _ s' fi h
    rw [hsf] at hfr; rw [hsg] at hg hp
    have hc' := hcert _ _ hpf'
    obtain ⟨hlv0, hr0, hlb0⟩ := certOK_entry hc'
    have hf0 := certOK_free_le hc' 0
    refine dec_call hfr ⟨hg, hp⟩ rfl rfl hft.1 (by rw [hft.2]; exact hlab) hfalls hcost hfree
      ⟨by rw [hfn, hpc]; exact hlv0, by rw [hfn, hpc, hlb0]; exact hlb⟩ (by rw [hfn, hpc]; exact hr0)
      (by rw [hfn, hpc]; unfold freeStepFactor; omega) hfs

/-- O-W1b, O-W2, O-W4 at one instruction: a continuing `exec` lowers the potential below the
instruction's budget and keeps the invariant. -/
theorem exec_dec (hcert : Certified cfg p cd) (hhost : HostsOK)
    {s1 s' : St} {f : Frame} {fs : List Frame} {pf : PFunc} {ins : Instr}
    (hs1 : s1.frames = f :: fs) (hpf : p.funcs[f.fn]? = some pf) (hi : pf.code[f.pc]? = some ins)
    (hfi : FrameInv cd f) (hfs : ∀ g ∈ fs, FrameInv cd g)
    (h : exec cfg p s1 f pf ins = .cont s') :
    Inv cd s' ∧ s'.gas.prepaid = s1.gas.prepaid ∧ Φ cfg cd s' + 1 ≤ budget cfg cd s1.gas.g f fs ins := by
  have hc := hcert f.fn pf hpf
  obtain ⟨hlv, hlab⟩ := hfi
  obtain ⟨hmv, -, -⟩ := certOK_live hc hi hlv
  have hfree := certOK_free_step hc hi
  have hK := freeStepFactor_pos cfg
  by_cases hd : isData ins = true
  · obtain ⟨s'', L, hfr, hg, rfl⟩ := exec_data cfg p s1 f pf s' ins hd h
    have hft := isData_moveOK hd hmv
    simp only [ftOK, Bool.and_eq_true, decide_eq_true_eq] at hft
    exact dec_fall (setFrame_frames (hfr.trans hs1) _) (GasLe.of_eq (by rw [setFrame_gas', hg])) rfl rfl hft.1
      (by rw [hft.2]; exact hlab) (isData_falls hd) hfree hK hfs
  · cases ins <;> simp [isData] at hd
    case unreachable => simp [exec] at h
    case block bt =>
      simp only [exec] at h
      split at h
      · cases h
      · rename_i e he
        cases h
        simp only [moveOK, he, ftOK, Bool.and_eq_true, decide_eq_true_eq] at hmv
        exact dec_fall (setFrame_frames hs1 _) (GasLe.of_eq (by rw [setFrame_gas'])) rfl rfl hmv.1
          (by simp only [List.map_cons, labTK, hmv.2]; rw [← hlab]) rfl hfree hK hfs
    case loop bt =>
      simp only [exec] at h
      cases h
      simp only [moveOK, ftOK, Bool.and_eq_true, decide_eq_true_eq] at hmv
      exact dec_fall (setFrame_frames hs1 _) (GasLe.of_eq (by rw [setFrame_gas'])) rfl rfl hmv.1
        (by simp only [List.map_cons, labTK, hmv.2]; rw [← hlab]) rfl hfree hK hfs
    case if_ bt =>
      simp only [exec] at h
      split at h
      · rename_i e el he hel
        simp only [moveOK, he, hel, ftOK, Bool.and_eq_true, decide_eq_true_eq] at hmv
        have hs2 : (popN s1).2.frames = f :: fs := by simp [hs1]
        split at h
        · cases h
          exact dec_fall (setFrame_frames hs2 _) (GasLe.of_eq (by rw [setFrame_gas']; simp)) rfl rfl hmv.1.1
            (by simp only [List.map_cons, labTK, hmv.1.2]; rw [← hlab]) rfl hfree hK hfs
        · split at h
          · rename_i hne
            cases h
            rw [if_pos hne] at hmv
            exact dec_jump (setFrame_frames hs2 _) (GasLe.of_eq (by rw [setFrame_gas']; simp)) rfl rfl hmv.2
              (by simp only [List.map_cons, labTK]; rw [← hlab]) (pay_costly hc _ _) hfs
          · rename_i hne
            cases h
            rw [if_neg hne] at hmv
            exact dec_jump (setFrame_frames hs2 _) (GasLe.of_eq (by rw [setFrame_gas']; simp)) rfl rfl hmv.2
              hlab (pay_costly hc _ _) hfs
      · cases h
    case else_ =>
      simp only [exec] at h
      split at h
      · rename_i lab ls hls
        cases h
        simp only [moveOK] at hmv
        rw [← hlab, hls] at hmv
        simp only [List.map_cons, labTK, Bool.and_eq_true, decide_eq_true_eq] at hmv
        refine dec_jump (setFrame_frames hs1 _) (GasLe.of_eq (by rw [setFrame_gas'])) rfl rfl hmv.2 rfl ?_ hfs
        have h1 := certOK_free_le_of_le hc (show f.pc + 1 ≤ lab.target by omega)
        have h2 : freeBit Instr.else_ = 1 := rfl
        have h3 : costBit Instr.else_ = 0 := rfl
        rw [h2] at hfree
        show (cd f.fn).fr lab.target + 1 ≤ freeStepFactor cfg * costBit Instr.else_ + (cd f.fn).fr f.pc
        rw [h3, Nat.mul_zero, Nat.zero_add]
        omega
      · cases h
    case end_ =>
      simp only [exec] at h
      split at h
      · exact dec_pop (doReturn_spec p s1 s' f fs hs1 h).1
          (GasLe.of_eq (by rw [(doReturn_spec p s1 s' f fs hs1 h).2])) (by have : freeBit Instr.end_ = 1 := rfl; omega) hfs
      · exact dec_pop (doReturn_spec p s1 s' f fs hs1 h).1
          (GasLe.of_eq (by rw [(doReturn_spec p s1 s' f fs hs1 h).2])) (by have : freeBit Instr.end_ = 1 := rfl; omega) hfs
      · rename_i _ x ls hne1 hls
        cases h
        cases ls with
        | nil => exact absurd rfl hne1
        | cons y ys =>
          simp only [moveOK] at hmv
          rw [← hlab, hls] at hmv
          simp only [List.map_cons, ftOK, Bool.and_eq_true, decide_eq_true_eq] at hmv
          exact dec_fall (setFrame_frames hs1 _) (GasLe.of_eq (by rw [setFrame_gas'])) rfl rfl hmv.1
            (by simp only [List.map_cons]; rw [hmv.2]) rfl hfree hK hfs
    case br l =>
      simp only [exec] at h
      exact dec_br hc hs1 rfl hlab hmv rfl hfs h
    case brIf l =>
      simp only [moveOK, Bool.and_eq_true] at hmv
      simp only [exec] at h
      have hs2 : (popN s1).2.frames = f :: fs := by simp [hs1]
      split at h
      · exact dec_br hc hs2 (by simp) hlab hmv.1 rfl hfs h
      · cases h
        simp only [ftOK, Bool.and_eq_true, decide_eq_true_eq] at hmv
        exact dec_fall (setFrame_frames hs2 _) (GasLe.of_eq (by rw [setFrame_gas']; simp)) rfl rfl hmv.2.1
          (by rw [hmv.2.2]; exact hlab) rfl hfree hK hfs
    case brTable ls d =>
      simp only [moveOK, List.all_eq_true] at hmv
      simp only [exec] at h
      have hs2 : (popN s1).2.frames = f :: fs := by simp [hs1]
      refine dec_br hc hs2 (by simp) hlab (hmv _ ?_) rfl hfs h
      cases hx : ls[(popN s1).1]? with
      | none => simp
      | some x => simp only [Option.getD_some]; exact List.mem_append_left _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hx))
    case ret =>
      simp only [exec] at h
      obtain ⟨hfr, hg⟩ := doReturn_spec p s1 s' f fs hs1 h
      exact dec_pop hfr (GasLe.of_eq (by rw [hg])) (by have : costBit Instr.ret = 1 := rfl; rw [this]; omega) hfs
    case call fi =>
      simp only [exec] at h
      exact dec_callFunc hcert hhost hc hs1 rfl hlab hmv rfl rfl hfree hfs h
    case callIndirect ty tab =>
      simp only [exec] at h
      have hs2 : (popN s1).2.frames = f :: fs := by simp [hs1]
      split at h
      · cases h
      · cases h
      · split at h
        · split at h
          · cases h
          · exact dec_callFunc hcert hhost hc hs2 (by simp) hlab hmv rfl rfl hfree hfs h
        · cases h

end execdec

/-! ## The step and the run -/

section run
variable {cfg : NearCfg} {p : Prepared} {cd : Nat → FCert}

/-- A charge of at least `r · n` lowers `⌊g / r⌋` by at least `n`. -/
theorem div_pay {g a r n : Nat} (hr : 0 < r) (hn : r * n ≤ a) (ha : a ≤ g) :
    (g - a) / r + n ≤ g / r := by
  have h1 : (g - a) / r ≤ (g - r * n) / r := Nat.div_le_div_right (by omega)
  have h2 : (g - r * n) / r = g / r - n := Nat.sub_mul_div g r n
  have h3 : n ≤ g / r := (Nat.le_div_iff_mul_le hr).2 (by rw [Nat.mul_comm]; omega)
  omega

theorem Φ_cons {s : St} {f : Frame} {fs : List Frame} (hfr : s.frames = f :: fs) :
    Φ cfg cd s = freeStepFactor cfg * (s.gas.g / cfg.regularOpCost) +
      (freeStepFactor cfg * (cd f.fn).r f.pc + (cd f.fn).fr f.pc) +
      (fs.map (frameΦ (freeStepFactor cfg) cd)).sum := by
  unfold Φ; rw [hfr]; simp only [List.map_cons, List.sum_cons, frameΦ]; omega

/-- **The potential argument.** A continuing step keeps the invariant and the prepaid gas, and
lowers `Φ` by at least one. -/
theorem step_dec (hcert : Certified cfg p cd) (hhost : HostsOK) (hr : 0 < cfg.regularOpCost)
    {s s' : St} (hinv : Inv cd s) (h : step cfg p s = .cont s') :
    Inv cd s' ∧ s'.gas.prepaid = s.gas.prepaid ∧ Φ cfg cd s' + 1 ≤ Φ cfg cd s := by
  cases hfr : s.frames with
  | nil => simp only [step, hfr] at h; cases h
  | cons f fs =>
    have hfi : FrameInv cd f := hinv f (by rw [hfr]; exact List.mem_cons_self)
    have hfs : ∀ g ∈ fs, FrameInv cd g := fun g hg => hinv g (by rw [hfr]; exact List.mem_cons_of_mem _ hg)
    rw [Φ_cons hfr]
    simp only [step, hfr] at h
    cases hpf : p.funcs[f.fn]? with
    | none => simp only [hpf] at h; cases h
    | some pf =>
      simp only [hpf] at h
      cases hi : pf.code[f.pc]? with
      | none => simp only [hi] at h; cases h
      | some ins =>
        simp only [hi] at h
        have hc := hcert f.fn pf hpf
        obtain ⟨-, hnc, hch⟩ := certOK_live hc hi hfi.1
        cases hgt : pf.gas[f.pc]? with
        | none => simp only [hgt] at h; cases h
        | some o =>
          simp only [hgt] at h
          cases o with
          | none =>
            obtain ⟨hi', hp', hd'⟩ := exec_dec hcert hhost hfr hpf hi hfi hfs h
            refine ⟨hi', hp', ?_⟩
            have := Nat.mul_le_mul_left (freeStepFactor cfg) (hnc hgt)
            unfold budget at hd'
            omega
          | some kf =>
            obtain ⟨k, fee⟩ := kf
            simp only at h
            cases hcg : charge s fee (if k = .linear then topCount s else 0) with
            | cont s1 =>
              rw [hcg] at h
              simp only at h
              obtain ⟨hf1, hamt, hg1, hp1⟩ := charge_spec _ _ _ _ hcg
              obtain ⟨hi', hp', hd'⟩ := exec_dec hcert hhost (hf1.trans hfr) hpf hi hfi hfs h
              refine ⟨hi', hp'.trans hp1, ?_⟩
              have hfee := hch k fee hgt
              have hpay := div_pay hr (Nat.le_trans hfee (by omega)) hamt
              rw [← hg1] at hpay
              have := Nat.mul_le_mul_left (freeStepFactor cfg) hpay
              rw [Nat.mul_add] at this
              unfold budget at hd'
              omega
            | fin _ => rw [hcg] at h; cases h
            | abort _ _ => rw [hcg] at h; cases h
            | unmodeled _ => rw [hcg] at h; cases h

/-- **Fuel is not binding.** From a state satisfying the invariant, a run with more fuel than the
potential returns the same result as a run with any larger fuel. -/
theorem run_stable (hcert : Certified cfg p cd) (hhost : HostsOK) (hr : 0 < cfg.regularOpCost) :
    ∀ (n : Nat) (s : St), Inv cd s → Φ cfg cd s < n → ∀ m, n ≤ m → run cfg p m s = run cfg p n s
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, s, hi, hΦ, m, hm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [run]
    cases hs : step cfg p s with
    | cont s' =>
      obtain ⟨hi', -, hd⟩ := step_dec hcert hhost hr hi hs
      exact run_stable hcert hhost hr n s' hi' (by omega) m' (by omega)
    | fin _ => rfl
    | abort _ _ => rfl
    | unmodeled _ => rfl

/-- **No fuel exhaustion.** The result of such a run is the non-continuing result of an actual
`step` from a reachable state: it is never produced by the step budget running out. -/
theorem run_from_step (hcert : Certified cfg p cd) (hhost : HostsOK) (hr : 0 < cfg.regularOpCost) :
    ∀ (n : Nat) (s : St), Inv cd s → Φ cfg cd s < n →
      ∃ t, t.gas.prepaid = s.gas.prepaid ∧ run cfg p n s = step cfg p t ∧ ∀ u, step cfg p t ≠ .cont u
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, hi, hΦ => by
    simp only [run]
    cases hs : step cfg p s with
    | cont s' =>
      obtain ⟨hi', hp', hd⟩ := step_dec hcert hhost hr hi hs
      obtain ⟨t, hpt, ht, hnc⟩ := run_from_step hcert hhost hr n s' hi' (by omega)
      exact ⟨t, hpt.trans hp', ht, hnc⟩
    | fin t => exact ⟨s, rfl, hs.symm, by rw [hs]; intro u h; cases h⟩
    | abort t e => exact ⟨s, rfl, hs.symm, by rw [hs]; intro u h; cases h⟩
    | unmodeled w => exact ⟨s, rfl, hs.symm, by rw [hs]; intro u h; cases h⟩

end run

/-! ## Terminal results: `fin` keeps the gas, the instantiated state has the given gas -/

theorem doReturn_fin_gas (p : Prepared) (s t : St) (h : doReturn p s = .fin t) : t.gas = s.gas := by
  unfold doReturn at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · split at h
      · cases h; rfl
      · cases h

theorem charge_ne_fin (s : St) fee c t : charge s fee c ≠ .fin t := by
  intro h
  simp only [charge] at h
  repeat' split at h
  all_goals cases h

theorem callHost_ne_fin (s : St) name t : callHost s name ≠ .fin t := by
  intro h
  unfold callHost at h
  repeat' split at h
  all_goals cases h

theorem enter_ne_fin (p : Prepared) (s : St) fi t : enter p s fi ≠ .fin t := by
  intro h
  unfold enter at h
  simp only at h
  repeat' split at h
  all_goals first | cases h | exact charge_ne_fin _ _ _ _ h

theorem callFunc_ne_fin (cfg : NearCfg) (p : Prepared) (s : St) fi t : callFunc cfg p s fi ≠ .fin t := by
  unfold callFunc; split
  · exact callHost_ne_fin _ _ _
  · exact enter_ne_fin _ _ _ _

theorem doBr_fin_gas (p : Prepared) (s : St) f l t (h : doBr p s f l = .fin t) : t.gas = s.gas := by
  unfold doBr at h
  split at h
  · exact doReturn_fin_gas _ _ _ h
  · split at h <;> cases h

theorem memCopy_ne_fin (s : St) a b c t : memCopy s a b c ≠ .fin t := by
  intro h; unfold memCopy at h; split at h <;> cases h
theorem memInit_ne_fin (s : St) a b c d t : memInit s a b c d ≠ .fin t := by
  intro h; simp only [memInit] at h; split at h <;> cases h
theorem tableInit_ne_fin (s : St) a b c d t : tableInit s a b c d ≠ .fin t := by
  intro h; simp only [tableInit] at h; split at h <;> cases h
theorem memFill_ne_fin (s : St) a b c t : memFill s a b c ≠ .fin t := by
  intro h; unfold memFill at h; split at h
  · cases h
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h; cases h

set_option hygiene false in
macro "fin_tac" : tactic => `(tactic| (
  simp only [exec] at h <;> (repeat' split at h) <;>
    first
    | exact absurd h (memCopy_ne_fin _ _ _ _ _)
    | exact absurd h (memInit_ne_fin _ _ _ _ _ _)
    | exact absurd h (memFill_ne_fin _ _ _ _ _)
    | exact absurd h (tableInit_ne_fin _ _ _ _ _ _)
    | exact absurd h (callFunc_ne_fin _ _ _ _ _)
    | exact doReturn_fin_gas _ _ _ h
    | exact (doBr_fin_gas _ _ _ _ _ h).trans (by simp)
    | (cases h; done)
    | skip))

set_option maxHeartbeats 4000000 in
theorem exec_fin_gas (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (ins : Instr)
    (t : St) (h : exec cfg p s f pf ins = .fin t) : t.gas = s.gas := by
  cases ins
  all_goals fin_tac


/-- A predicate kept by every successful iteration of an `Except` loop holds at its end. -/
theorem except_list_loop {α β : Type} (P : β → Prop) (body : α → β → Except String (ForInStep β))
    (hb : ∀ x b r, P b → body x b = .ok r → P (match r with | .done b' => b' | .yield b' => b')) :
    ∀ (l : List α) (init out : β), P init → forIn l init body = .ok out → P out
  | [], init, out, hi, h => by
    simp only [List.forIn_nil] at h
    cases h; exact hi
  | x :: xs, init, out, hi, h => by
    simp only [List.forIn_cons] at h
    cases hx : body x init with
    | error e => rw [hx] at h; cases h
    | ok r =>
      rw [hx] at h
      have := hb x init r hi hx
      cases r with
      | done b' => cases h; exact this
      | yield b' => exact except_list_loop P body hb xs b' out this h

theorem except_array_loop {α β : Type} (P : β → Prop) (body : α → β → Except String (ForInStep β))
    (hb : ∀ x b r, P b → body x b = .ok r → P (match r with | .done b' => b' | .yield b' => b'))
    (xs : Array α) (init out : β) (hi : P init) (h : forIn xs init body = .ok out) : P out := by
  rw [← Array.forIn_toList] at h
  exact except_list_loop P body hb xs.toList init out hi h

set_option pp.proofs false in
theorem instantiate_gas (cfg : NearCfg) (p : Prepared) (gas : Gas) (s : St)
    (h : instantiate cfg p gas = .ok s) : s.gas = gas := by
  unfold instantiate at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v1 hv1
    have h1 := except_array_loop (fun b => b.1.gas = gas) _ ?_ _ _ _ rfl hv1
    · (try simp only at h1)
      split at h
      · cases h
      · rename_i v2 hv2
        have h2 := except_array_loop (fun b => b.1.gas = gas) _ ?_ _ _ _ h1 hv2
        · simp only [pure, Except.pure] at h
          cases h
          exact h2
        · intro x b r hb hr
          (try simp only at hr)
          repeat' split at hr
          all_goals first
            | (cases hr; done)
            | (cases hr; simpa using hb)
            | (cases hr; rename_i heq; exact (memInit_keeps _ _ _ _ _ _ heq).2.trans hb)
            | skip
    · intro x b r hb hr
      (try simp only at hr)
      repeat' split at hr
      all_goals first
        | (cases hr; done)
        | (cases hr; simpa using hb)
        | (cases hr; rename_i heq; exact (tableInit_keeps _ _ _ _ _ _ heq).2.trans hb)
        | skip


/-! ## Entries, calls, and the checker's call -/

section entry
variable {cfg : NearCfg} {p : Prepared} {cd : Nat → FCert}

theorem step_fin_prepaid {s t : St} (h : step cfg p s = .fin t) : t.gas.prepaid = s.gas.prepaid := by
  cases hfr : s.frames with
  | nil => simp only [step, hfr] at h; cases h; rfl
  | cons f fs =>
    simp only [step, hfr] at h
    cases hpf : p.funcs[f.fn]? with
    | none => simp only [hpf] at h; cases h
    | some pf =>
      simp only [hpf] at h
      cases hi : pf.code[f.pc]? with
      | none => simp only [hi] at h; cases h
      | some ins =>
        simp only [hi] at h
        cases hgt : pf.gas[f.pc]? with
        | none => simp only [hgt] at h; cases h
        | some o =>
          simp only [hgt] at h
          cases o with
          | none => rw [exec_fin_gas cfg p s f pf ins t h]
          | some kf =>
            obtain ⟨k, fee⟩ := kf
            simp only at h
            cases hcg : charge s fee (if k = .linear then topCount s else 0) with
            | cont s1 =>
              rw [hcg] at h; simp only at h
              rw [exec_fin_gas cfg p s1 f pf ins t h, (charge_spec _ _ _ _ hcg).2.2.2]
            | fin _ => exact absurd hcg (charge_ne_fin _ _ _ _)
            | abort _ _ => rw [hcg] at h; cases h
            | unmodeled _ => rw [hcg] at h; cases h

/-- O-W3 at entry: the entered frame needs no credit and carries at most `F` free instructions. -/
theorem entry_ok (hcert : Certified cfg p cd) {s s1 : St} {fi : Nat} (hf : s.frames = [])
    (h : enter p s fi = .cont s1) :
    Inv cd s1 ∧ s1.gas.prepaid = s.gas.prepaid ∧
      Φ cfg cd s1 ≤ freeStepFactor cfg * (s.gas.g / cfg.regularOpCost) + (2 * cfg.maxBlocksPerFunction + 1) := by
  obtain ⟨pf, hpf, hg, hp, fr, hfr, hfn, hpc, hlb⟩ := enter_spec p s s1 fi h
  rw [hf] at hfr
  have hc := hcert _ _ hpf
  obtain ⟨hlv0, hr0, hlb0⟩ := certOK_entry hc
  have hf0 := certOK_free_le hc 0
  refine ⟨inv_of_frames (top := [fr]) (fs := []) (by simpa using hfr) ?_ (by simp), hp, ?_⟩
  · intro g hg; simp only [List.mem_singleton] at hg; subst hg
    exact ⟨by rw [hfn, hpc]; exact hlv0, by rw [hfn, hpc, hlb0]; exact hlb⟩
  · rw [Φ_of_frames (cd := cd) s1 [fr] [] (by simpa using hfr)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, frameΦ, hfn, hpc, hr0,
      Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    have := gas_term_le (cfg := cfg) hg
    omega

/-- The entry potential is below the successor budget. -/
theorem entry_lt_wasmFuel (cfg : NearCfg) {g gas : Nat} (hg : g ≤ gas) :
    freeStepFactor cfg * (g / cfg.regularOpCost) + (2 * cfg.maxBlocksPerFunction + 1) < wasmFuel cfg gas := by
  unfold wasmFuel
  have h1 : g / cfg.regularOpCost ≤ gas / cfg.regularOpCost := Nat.div_le_div_right hg
  have h2 := Nat.mul_le_mul_left (freeStepFactor cfg) h1
  rw [Nat.add_mul, Nat.mul_comm (gas / cfg.regularOpCost)]
  have hK : freeStepFactor cfg = 2 * cfg.maxBlocksPerFunction + 2 := rfl
  generalize freeStepFactor cfg * (g / cfg.regularOpCost) = a at *
  generalize freeStepFactor cfg * (gas / cfg.regularOpCost) = b at *
  omega

theorem remaining_le_prepaid (g : Gas) : g.remaining ≤ g.prepaid := Nat.sub_le _ _

/-- **Entry level.** A wasm entry (`start` or the method) from a state whose prepaid gas is at
most `gas` has the same result for every fuel `≥ wasmFuel cfg gas`. -/
theorem callEntry_stable (hcert : Certified cfg p cd) (hhost : HostsOK) (hr : 0 < cfg.regularOpCost)
    (s : St) (fi gas : Nat) (hpre : s.gas.prepaid ≤ gas) (m : Nat) (hm : wasmFuel cfg gas ≤ m) :
    callEntry cfg p m s fi = callEntry cfg p (wasmFuel cfg gas) s fi := by
  simp only [callEntry]
  generalize he : enter p _ fi = e
  cases e with
  | cont s1 =>
    obtain ⟨hi, -, hΦ⟩ := entry_ok hcert rfl he
    have hlt := entry_lt_wasmFuel cfg (Nat.le_trans (remaining_le_prepaid s.gas) hpre)
    simp only at hΦ ⊢
    rw [run_stable hcert hhost hr _ s1 hi (by omega) m hm]
  | fin _ => rfl
  | abort _ _ => rfl
  | unmodeled _ => rfl

/-- **Entry level, no exhaustion.** Under the successor budget an entry's run ends in the
non-continuing result of a real `step`, never in the step budget. -/
theorem callEntry_run_from_step (hcert : Certified cfg p cd) (hhost : HostsOK)
    (hr : 0 < cfg.regularOpCost) (s : St) (fi gas : Nat) (hpre : s.gas.prepaid ≤ gas) (s1 : St)
    (he : enter p { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] } fi = .cont s1) :
    ∃ t, run cfg p (wasmFuel cfg gas) s1 = step cfg p t ∧ ∀ u, step cfg p t ≠ .cont u := by
  obtain ⟨hi, -, hΦ⟩ := entry_ok hcert rfl he
  have hlt := entry_lt_wasmFuel cfg (Nat.le_trans (remaining_le_prepaid s.gas) hpre)
  simp only at hΦ
  obtain ⟨t, -, ht, hnc⟩ := run_from_step hcert hhost hr (wasmFuel cfg gas) s1 hi (by omega)
  exact ⟨t, ht, hnc⟩

/-- An entry that finishes (`fin`) keeps the prepaid gas, so the method entry after `start` is
in the same budget. -/
theorem callEntry_prepaid (hcert : Certified cfg p cd) (hhost : HostsOK) (hr : 0 < cfg.regularOpCost)
    (s s' : St) (fi gas : Nat) (hpre : s.gas.prepaid ≤ gas)
    (h : callEntry cfg p (wasmFuel cfg gas) s fi = .ok (s', none)) : s'.gas.prepaid = s.gas.prepaid := by
  simp only [callEntry] at h
  generalize he : enter p _ fi = e at h
  cases e with
  | cont s1 =>
    obtain ⟨hi, hp1, hΦ⟩ := entry_ok hcert rfl he
    have hlt := entry_lt_wasmFuel cfg (Nat.le_trans (remaining_le_prepaid s.gas) hpre)
    simp only at hΦ
    obtain ⟨t, hpt, ht, hnc⟩ := run_from_step hcert hhost hr (wasmFuel cfg gas) s1 hi (by omega)
    simp only at h
    rw [ht] at h
    cases hst : step cfg p t with
    | cont u => exact absurd hst (hnc u)
    | fin s0 =>
      rw [hst] at h
      simp only at h
      cases hs : sync s0 with
      | error _ => rw [hs] at h; cases h
      | ok s2 =>
        rw [hs] at h
        simp only [Except.map] at h
        cases h
        rw [(sync_spec _ _ hs).2.2, step_fin_prepaid hst, hpt, hp1]
    | abort s0 e =>
      rw [hst] at h
      simp only at h
      cases hs : sync s0 with
      | error _ => rw [hs] at h; cases h
      | ok s2 => rw [hs] at h; simp only [Except.map] at h; cases h
    | unmodeled _ => rw [hst] at h; cases h
  | fin t => exact absurd he (enter_ne_fin _ _ _ _)
  | abort s0 e =>
    simp only at h
    cases hs : sync s0 with
    | error _ => rw [hs] at h; cases h
    | ok s2 => rw [hs] at h; simp only [Except.map] at h; cases h
  | unmodeled _ => cases h

/-- `start` then the method, both under the successor budget. -/
theorem runTail_stable (hcert : Certified cfg p cd) (hhost : HostsOK) (hr : 0 < cfg.regularOpCost)
    (S : St) (mi : Nat) (start : Option Nat) (gas : Nat) (hpre : S.gas.prepaid ≤ gas) (m : Nat)
    (hm : wasmFuel cfg gas ≤ m) :
    runTail cfg p m S mi start = runTail cfg p (wasmFuel cfg gas) S mi start := by
  cases start with
  | none =>
    simp only [runTail]
    rw [callEntry_stable hcert hhost hr S mi gas hpre m hm]
  | some st =>
    simp only [runTail]
    rw [callEntry_stable hcert hhost hr S st gas hpre m hm]
    cases hst : callEntry cfg p (wasmFuel cfg gas) S st with
    | error _ => rfl
    | ok r =>
      obtain ⟨s1, e⟩ := r
      cases e with
      | some _ => rfl
      | none =>
        simp only
        have hp := callEntry_prepaid hcert hhost hr S s1 st gas hpre hst
        rw [callEntry_stable hcert hhost hr s1 mi gas (by rw [hp]; exact hpre) m hm]

theorem burn_prepaid (gs : Gas) (x : Nat) : (burn gs x).1.prepaid = gs.prepaid := by
  simp only [burn]
  split
  · rfl
  · split
    · rfl
    · simp only [processGasLimit]

theorem payPer_prepaid (gs : Gas) (c : Cost) (n : Nat) : (payPer gs c n).1.prepaid = gs.prepaid := by
  unfold payPer
  split
  · rfl
  · simp only; exact burn_prepaid gs _

end entry

/-! ## The checker's call -/

section top
variable {cfg : NearCfg}

/-- Every module that `prepare` accepts for `code` has a certificate for each function. -/
def PrepCertified (cfg : NearCfg) (code : ByteArray) (blockLevel : Bool) : Prop :=
  ∀ p, prepare cfg code blockLevel = .ok p → ∃ cd, Certified cfg p cd

theorem runCall_stable (hhost : HostsOK) (hr : 0 < cfg.regularOpCost) (code : ByteArray)
    (method : String) (ctx : CallCtx) (blockLevel full : Bool) (real : Option TTN.RealStore)
    (hc : PrepCertified cfg code blockLevel) (m : Nat) (hm : wasmFuel cfg ctx.prepaidGas ≤ m) :
    runCall cfg code method ctx m blockLevel full real =
      runCall cfg code method ctx (wasmFuel cfg ctx.prepaidGas) blockLevel full real := by
  simp only [runCall]
  by_cases hme : method.isEmpty = true
  · simp only [hme, ite_true]
  simp only [hme, Bool.false_eq_true, ite_false]
  cases hp : prepare cfg code blockLevel with
  | ok p =>
    obtain ⟨cd, hcert⟩ := hc p hp
    simp only
    split
    · rfl
    split
    · rfl
    rename_i gs hl
    have hgs : gs.prepaid = ctx.prepaidGas := by
      revert hl
      cases hq : payPer (Gas.init ctx.prepaidGas) C.contractLoadingBytes code.size with
      | mk g1 e1 =>
        have h1 := payPer_prepaid (Gas.init ctx.prepaidGas) C.contractLoadingBytes code.size
        rw [hq] at h1
        cases e1 with
        | none =>
          intro hl
          simp only [payBase] at hl
          have h2 := payPer_prepaid g1 C.contractLoadingBase 1
          rw [hl] at h2
          simp only at h1 h2
          rw [h2, h1]; rfl
        | some _ => intro hl; simp at hl
    split
    · rfl
    · rfl
    split
    · rfl
    · rfl
    · rfl
    rename_i mi _
    split
    · rfl
    rename_i S hinst
    have hS := instantiate_gas cfg p gs S hinst
    exact runTail_stable hcert hhost hr _ mi p.m.start ctx.prepaidGas
      (by simp only; rw [hS, hgs]; exact Nat.le_refl _) m hm
  | outOfDomain _ => rfl
  | unmodeled _ => rfl
  | prepErr _ _ => rfl
  | compileErr _ _ => rfl

/-- **Fuel sufficiency at the checker's call.** For every contract whose prepared functions are
certified (`PrepCertified`), and given the host obligation `HostsOK`, the call the successor makes
(`StorageExecution.functionCall`: `runCallWithLimits … (wasmFuel cfg gas)` with
`ctx.prepaidGas = gas`) has the same result under every larger step budget: the budget never
decides an outcome, so no execution is turned into `unmodeled fuel exhausted`. -/
theorem runCallWithLimits_stable (hhost : HostsOK) (hr : 0 < cfg.regularOpCost) (code : ByteArray)
    (method : String) (ctx : CallCtx) (blockLevel full : Bool) (real : Option TTN.RealStore)
    (hc : PrepCertified cfg code blockLevel) (m : Nat) (hm : wasmFuel cfg ctx.prepaidGas ≤ m) :
    runCallWithLimits cfg code method ctx m blockLevel full real =
      runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas) blockLevel full real := by
  simp only [runCallWithLimits]
  cases hl : cfg.loadingLimits
  · simp only [Bool.not_false, ite_true]
    exact runCall_stable hhost hr code method ctx blockLevel full real hc m hm
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases hp : prepare cfg code blockLevel <;> simp only <;>
      try exact runCall_stable hhost hr code method ctx blockLevel full real hc m hm
    split
    · exact runCall_stable hhost hr code method ctx blockLevel full real hc m hm
    · rfl

end top

theorem prepCertOK_certified (cfg : NearCfg) (p : Prepared) (h : prepCertOK cfg p = true) :
    Certified cfg p (fun k => buildCert cfg (p.funcs[k]?.getD default)) := by
  intro k pf hk
  simp only [hk, Option.getD_some]
  unfold prepCertOK at h
  rw [Array.all_eq_true] at h
  obtain ⟨hlt, hv⟩ := Array.getElem?_eq_some_iff.mp hk
  have := h k hlt
  rw [hv] at this
  exact this

/-- The static obligation, as a decidable statement about one contract. -/
def CodeCertified (cfg : NearCfg) (code : ByteArray) (blockLevel : Bool) : Prop :=
  ∀ p, prepare cfg code blockLevel = .ok p → prepCertOK cfg p = true

theorem CodeCertified.prep {cfg : NearCfg} {code : ByteArray} {blockLevel : Bool}
    (h : CodeCertified cfg code blockLevel) : PrepCertified cfg code blockLevel :=
  fun p hp => ⟨_, prepCertOK_certified cfg p (h p hp)⟩

/-- **W02 fuel sufficiency (the successor's call).** If every function `prepare` produces for
`code` passes its certificate and the host table keeps frames and never refunds gas, then the
call `StorageExecution.functionCall` makes — `runCallWithLimits cfg code method ctx (wasmFuel cfg
ctx.prepaidGas) …` — returns the same result as with any larger step budget. -/
theorem wasmFuel_sufficient (cfg : NearCfg) (hhost : HostsOK) (hr : 0 < cfg.regularOpCost)
    (code : ByteArray) (method : String) (ctx : CallCtx) (blockLevel full : Bool)
    (real : Option TTN.RealStore) (hc : CodeCertified cfg code blockLevel) (m : Nat)
    (hm : wasmFuel cfg ctx.prepaidGas ≤ m) :
    runCallWithLimits cfg code method ctx m blockLevel full real =
      runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas) blockLevel full real :=
  runCallWithLimits_stable hhost hr code method ctx blockLevel full real hc.prep m hm

/-! Axiom audit (printed by every build of this module). -/
#print axioms step_dec
#print axioms run_stable
#print axioms run_from_step
#print axioms callEntry_stable
#print axioms callEntry_run_from_step
#print axioms runCallWithLimits_stable
#print axioms wasmFuel_sufficient

end NearSpecV3.Wasm
