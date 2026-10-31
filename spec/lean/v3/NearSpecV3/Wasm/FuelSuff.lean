import NearSpecV3.Wasm.FuelDefs
/-!
# Fuel sufficiency (W02, workplan item 3): the dynamic half

Given the static facts of `Wasm/FuelDefs.lean` (`FnOK` for every prepared function, `HostsOK` for
the host arms), every `.cont` step of `Wasm.step` strictly lowers the natural-number measure

  `μ s = (2·max_blocks_per_function + 2) · ⌊(g + regular_op_cost · req) / regular_op_cost⌋ + P`

where `g` is the wasm gas counter, `req` the costly instructions of the current charge group that
are already paid for, and `P` the free (`block`/`loop`/`else`/`end`) instructions at or after each
frame's `pc` (the potential of `Wasm/Fuel.lean`). A costly step lowers the first term by at least
one unit of `2·M + 2` and raises `P` by at most `2·M + 1`; a free step keeps the first term and
lowers `P`. So `run` with fuel above `μ` never runs out, and `μ` of a call's entry state is below
`wasmFuel cfg prepaid`.
-/
namespace NearSpecV3.Wasm.FuelGen

/-! ## Frames and gas are all the measure reads -/

/-- The parts of the machine state that the fuel argument tracks. -/
def fg (s : St) : List Frame × Gas := (s.frames, s.gas)

theorem foldl_fg {α : Type} (f : St → α → St) (hf : ∀ s a, fg (f s a) = fg s) :
    ∀ (l : List α) (init : St), fg (List.foldl f init l) = fg init
  | [], _ => rfl
  | a :: l, init => by
    simp only [List.foldl_cons]
    rw [foldl_fg f hf l]; exact hf init a

theorem forIn_range_fg (r : Std.Legacy.Range) (init : St) (f : Nat → St → St)
    (hf : ∀ i s, fg (f i s) = fg s) :
    fg (Id.run (forIn r init fun i s => pure (ForInStep.yield (f i s)))) = fg init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  exact foldl_fg (fun b a => f a b) (fun s a => hf a s) _ init

theorem forIn'_range_fg (r : Std.Legacy.Range) (init : St) (f : (i : Nat) → i ∈ r → St → St)
    (hf : ∀ i h s, fg (f i h s) = fg s) :
    fg (Id.run (forIn' r init fun i h s => pure (ForInStep.yield (f i h s)))) = fg init := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range', List.forIn'_pure_yield_eq_foldl]
  exact foldl_fg _ (fun s a => hf _ _ s) _ init

@[simp] theorem fg_writeByte (s : St) (a : Nat) (v : UInt8) : fg (writeByte s a v) = fg s := rfl
@[simp] theorem fg_pushV (s : St) (v : Val) : fg (pushV s v) = fg s := rfl
@[simp] theorem fg_popV (s : St) : fg (popV s).2 = fg s := rfl
theorem popN_snd (s : St) : (popN s).2 = (popV s).2 := by
  unfold popN; rcases h : popV s with ⟨v, s'⟩; cases v <;> rfl
theorem popRef_snd (s : St) : (popRef s).2 = (popV s).2 := by
  unfold popRef; rcases h : popV s with ⟨v, s'⟩; cases v <;> rfl
@[simp] theorem fg_popN (s : St) : fg (popN s).2 = fg s := by rw [popN_snd]; rfl
@[simp] theorem fg_popRef (s : St) : fg (popRef s).2 = fg s := by rw [popRef_snd]; rfl
@[simp] theorem fg_pushI32 (s : St) (v : Nat) : fg (pushI32 s v) = fg s := rfl
@[simp] theorem fg_pushI64 (s : St) (v : Nat) : fg (pushI64 s v) = fg s := rfl
@[simp] theorem fg_pushT (s : St) (t : VT) (v : Nat) : fg (pushT s t v) = fg s := by
  unfold pushT; split <;> rfl

@[simp] theorem fg_writeLE (s : St) (a w v : Nat) : fg (writeLE s a w v) = fg s :=
  forIn_range_fg _ s _ (fun _ _ => rfl)

@[simp] theorem fg_writeBytes (s : St) (a : Nat) (d : ByteArray) : fg (writeBytes s a d) = fg s :=
  forIn'_range_fg _ s _ (fun _ _ _ => rfl)

theorem fg_memFill {s s' : St} {d v n : Nat} (h : memFill s d v n = .cont s') : fg s' = fg s := by
  unfold memFill at h
  split at h
  · cases h
  · cases h
    exact forIn_range_fg _ s _ (fun _ _ => rfl)

theorem fg_memCopy {s s' : St} {d src n : Nat} (h : memCopy s d src n = .cont s') : fg s' = fg s := by
  unfold memCopy at h
  split at h
  · cases h
  · cases h; exact fg_writeBytes _ _ _

theorem fg_memInit {s s' : St} {seg d src n : Nat} (h : memInit s seg d src n = .cont s') :
    fg s' = fg s := by
  unfold memInit at h
  dsimp only at h
  split at h
  · cases h
  · cases h; exact fg_writeBytes _ _ _

theorem fg_tableInit {s s' : St} {seg d src n : Nat} (h : tableInit s seg d src n = .cont s') :
    fg s' = fg s := by
  unfold tableInit at h
  dsimp only at h
  split at h
  · cases h
  · cases h; rfl

/-! ## Plain instructions -/

/-- The instructions whose `exec` arm only moves to `pc + 1` (or stops). -/
def isControl : Instr → Bool
  | .unreachable | .block _ | .loop _ | .if_ _ | .else_ | .end_ | .br _ | .brIf _ | .brTable _ _
  | .ret | .call _ | .callIndirect _ _ => true
  | _ => false

theorem setFrame_fg {s s2 : St} {f : Frame} {fs : List Frame} (hf : s.frames = f :: fs)
    (h2 : fg s2 = fg s) (F : Frame) :
    (setFrame s2 F).frames = F :: fs ∧ (setFrame s2 F).gas = s.gas := by
  simp only [fg, Prod.mk.injEq] at h2
  unfold setFrame
  rw [h2.1, hf]
  exact ⟨rfl, h2.2⟩

@[simp] theorem popV_frames' (s : St) : (popV s).2.frames = s.frames := rfl
@[simp] theorem popV_gas' (s : St) : (popV s).2.gas = s.gas := rfl
@[simp] theorem pushV_frames' (s : St) (v : Val) : (pushV s v).frames = s.frames := rfl
@[simp] theorem pushV_gas' (s : St) (v : Val) : (pushV s v).gas = s.gas := rfl
@[simp] theorem pushI32_frames' (s : St) (v : Nat) : (pushI32 s v).frames = s.frames := rfl
@[simp] theorem pushI32_gas' (s : St) (v : Nat) : (pushI32 s v).gas = s.gas := rfl
@[simp] theorem pushI64_frames' (s : St) (v : Nat) : (pushI64 s v).frames = s.frames := rfl
@[simp] theorem pushI64_gas' (s : St) (v : Nat) : (pushI64 s v).gas = s.gas := rfl
@[simp] theorem pushT_frames' (s : St) (t : VT) (v : Nat) : (pushT s t v).frames = s.frames :=
  congrArg Prod.fst (fg_pushT s t v)
@[simp] theorem pushT_gas' (s : St) (t : VT) (v : Nat) : (pushT s t v).gas = s.gas :=
  congrArg Prod.snd (fg_pushT s t v)
@[simp] theorem writeLE_frames' (s : St) (a w v : Nat) : (writeLE s a w v).frames = s.frames :=
  congrArg Prod.fst (fg_writeLE s a w v)
@[simp] theorem writeLE_gas' (s : St) (a w v : Nat) : (writeLE s a w v).gas = s.gas :=
  congrArg Prod.snd (fg_writeLE s a w v)

theorem pair_eq_iff' {α β : Type} {p : α × β} {a : α} {b : β} : p = (a, b) ↔ a = p.1 ∧ b = p.2 := by
  cases p; simp [eq_comm]

set_option maxHeartbeats 1000000 in
theorem fg_execNum {s s2 : St} {op : Nat} (h : execNum s op = .ok s2) : fg s2 = fg s := by
  unfold execNum at h
  repeat' split at h
  all_goals (try dsimp only at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [pair_eq_iff'] at *)
  all_goals first
    | (cases h; done)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp_all [fg, popN_snd, popRef_snd])
    | (simp [throw, throwThe, MonadExceptOf.throw, Except.pure, pure] at h; done)

set_option maxHeartbeats 1000000 in
theorem fg_execFloat {s s2 : St} {op : Nat} (h : execFloat s op = .ok s2) : fg s2 = fg s := by
  unfold execFloat at h
  repeat' split at h
  all_goals (try dsimp only at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [pair_eq_iff'] at *)
  all_goals first
    | (cases h; done)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp_all [fg, popN_snd, popRef_snd])
    | (simp [throw, throwThe, MonadExceptOf.throw, Except.pure, pure] at h; done)

set_option maxHeartbeats 4000000 in
/-- A plain instruction that continues moves the top frame to `pc + 1` (labels kept) and leaves
the frames below and the gas alone. -/
theorem exec_plain (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (fs : List Frame)
    (hf : s.frames = f :: fs) (pf : PFunc) (i : Instr) (hc : isControl i = false) (s' : St)
    (h : exec cfg p s f pf i = .cont s') :
    ∃ f', s'.frames = f' :: fs ∧ f'.fn = f.fn ∧ f'.pc = f.pc + 1 ∧ f'.labels = f.labels ∧
      s'.gas = s.gas := by
  have fin : ∀ s2 F, fg s2 = fg s → F.fn = f.fn → F.pc = f.pc + 1 → F.labels = f.labels →
      setFrame s2 F = s' → ∃ f', s'.frames = f' :: fs ∧ f'.fn = f.fn ∧ f'.pc = f.pc + 1 ∧
        f'.labels = f.labels ∧ s'.gas = s.gas := by
    intro s2 F h2 h1 h3 h4 he
    subst he
    obtain ⟨a, b⟩ := setFrame_fg hf h2 F
    exact ⟨F, a, h1, h3, h4, b⟩
  cases i <;> simp only [isControl, Bool.true_eq_false] at hc <;> simp only [exec] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (exfalso; rename_i hne; exact hne _ h)
    | skip
  all_goals (try simp only [Id.run_bind, Id.run_pure] at h)
  all_goals (try injection h with h)
  all_goals (try (refine fin _ _ ?_ ?_ ?_ ?_ h <;> try rfl))
  all_goals first
    | exact (fg_memCopy (by assumption)).trans (by simp [fg, popN_snd, popRef_snd])
    | exact (fg_memFill (by assumption)).trans (by simp [fg, popN_snd, popRef_snd])
    | exact (fg_memInit (by assumption)).trans (by simp [fg, popN_snd, popRef_snd])
    | exact (fg_tableInit (by assumption)).trans (by simp [fg, popN_snd, popRef_snd])
    | exact (fg_execNum (by assumption)).trans (by simp [fg, popN_snd, popRef_snd])
    | exact (fg_execFloat (by assumption)).trans (by simp [fg, popN_snd, popRef_snd])
    | simp [fg, popN_snd, popRef_snd]

theorem plain_facts {i : Instr} (hc : isControl i = false) :
    fallsThrough i = true ∧ isOpener i = false ∧ isFreeInstr i = false ∧ isCallI i = false ∧
      i ≠ .else_ ∧ i ≠ .end_ := by
  cases i <;> simp_all [isControl, fallsThrough, isOpener, isFreeInstr, isCallI]

/-! ## Gas hooks, returns, branches and calls -/

theorem charge_cont' {s s1 : St} {fee : Fee} {c : Nat} (h : charge s fee c = .cont s1) :
    c * fee.l + fee.c ≤ s.gas.g ∧
      s1 = { s with gas := { s.gas with g := s.gas.g - (c * fee.l + fee.c) } } := by
  simp only [charge] at h
  by_cases h1 : c * fee.l + fee.c ≥ u64Bound
  · simp only [h1, ite_true] at h
    repeat' split at h
    all_goals cases h
  · simp only [h1, ite_false] at h
    by_cases h2 : c * fee.l + fee.c > s.gas.g
    · simp only [h2, ite_true] at h
      repeat' split at h
      all_goals cases h
    · simp only [h2, ite_false] at h
      cases h
      exact ⟨by omega, rfl⟩

theorem doReturn_cont {p : Prepared} {s s' : St} {f : Frame} {fs : List Frame}
    (hf : s.frames = f :: fs) (h : doReturn p s = .cont s') :
    s'.frames = fs ∧ s'.gas = s.gas ∧ fs ≠ [] := by
  unfold doReturn at h
  rw [hf] at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hne
      cases h
      refine ⟨rfl, rfl, ?_⟩
      intro h0; subst h0; exact hne rfl

theorem doBr_cont {p : Prepared} {s s' : St} {f : Frame} {fs : List Frame} {l : Nat}
    (hf : s.frames = f :: fs) (h : doBr p s f l = .cont s') :
    (f.labels.length ≤ l + 1 ∧ s'.frames = fs ∧ s'.gas = s.gas ∧ fs ≠ []) ∨
    (l + 1 < f.labels.length ∧ ∃ lab, f.labels[l]? = some lab ∧ s'.gas = s.gas ∧
      s'.frames = { f with pc := lab.target, labels := if lab.isLoop then f.labels.drop l else f.labels.drop (l + 1) } :: fs) := by
  unfold doBr at h
  split at h
  · rename_i hl
    exact .inl ⟨hl, doReturn_cont hf h⟩
  · rename_i hl
    split at h
    · cases h
    · rename_i lab hlab
      cases h
      refine .inr ⟨by omega, lab, hlab, ?_, ?_⟩
      · simp [setFrame, hf]
      · simp [setFrame, hf]

theorem sync_ok {s s3 : St} (h : sync s = .ok s3) (hg : s.gas.g ≤ s.gas.remaining) :
    s3.frames = s.frames ∧ s3.gas.prepaid = s.gas.prepaid ∧ s3.gas.remaining ≤ s.gas.g := by
  unfold sync at h
  dsimp only at h
  split at h
  · rename_i h0
    cases h
    exact ⟨rfl, rfl, by omega⟩
  · rename_i h0
    split at h
    · rename_i gs hb
      cases h
      unfold burn at hb
      dsimp only at hb
      split at hb
      · simp at hb
      · split at hb
        · simp only [Prod.mk.injEq] at hb
          obtain ⟨rfl, -⟩ := hb
          refine ⟨rfl, rfl, ?_⟩
          simp only [Gas.remaining, Gas.used] at hg h0 ⊢
          omega
        · unfold processGasLimit at hb
          simp at hb
    · cases h

theorem callHost_cont (hh : HostsOK) {s s' : St} {name : String} (hg : s.gas.g ≤ s.gas.remaining)
    (h : callHost s name = .cont s') :
    s'.frames = s.frames ∧ s'.gas.prepaid = s.gas.prepaid ∧ s'.gas.g ≤ s.gas.g ∧
      s'.gas.g ≤ s'.gas.remaining := by
  unfold callHost at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i s3 hs
      obtain ⟨h1, h2, h3⟩ := sync_ok hs hg
      split at h
      · cases h
      · rename_i hm harm
        split at h
        · rename_i u s4 hrun
          cases h
          obtain ⟨k1, k2, k3⟩ := hh s3 name hm u s4 harm hrun
          refine ⟨k1.trans h1, k3.trans h2, ?_, Nat.le_refl _⟩
          simp only [Gas.remaining, Gas.used] at h3 k2 ⊢
          omega
        · split at h <;> cases h

theorem enter_cont {p : Prepared} {s s' : St} {fi : Nat} (h : enter p s fi = .cont s') :
    ∃ pf2, p.funcs[fi - p.m.imports.size]? = some pf2 ∧ ∃ fr : Frame, s'.frames = fr :: s.frames ∧
      fr.fn = fi - p.m.imports.size ∧ fr.pc = 0 ∧
      fr.labels.map (fun l => (l.target, l.isLoop)) = [(pf2.code.size, false)] ∧
      s'.gas.g ≤ s.gas.g ∧ s'.gas.remaining = s.gas.remaining ∧
      s'.gas.prepaid = s.gas.prepaid := by
  unfold enter at h
  dsimp only at h
  split at h
  · cases h
  · rename_i pf2 hpf2
    split at h
    · split at h <;> cases h
    · cases hc : charge { s with stackRem := s.stackRem - pf2.stackCharge }
          (Fee.const pf2.prologueGas) 0 with
      | cont s1 =>
        simp only [hc] at h
        cases h
        obtain ⟨hle, rfl⟩ := charge_cont' hc
        exact ⟨pf2, hpf2, _, rfl, rfl, rfl, rfl, Nat.sub_le _ _, rfl, rfl⟩
      | fin _ => simp only [hc] at h; cases h
      | abort _ _ => simp only [hc] at h; cases h
      | unmodeled _ => simp only [hc] at h; cases h

theorem callFunc_cont (hh : HostsOK) {cfg : NearCfg} {p : Prepared} {s s' : St} {fi : Nat}
    (hg : s.gas.g ≤ s.gas.remaining) (h : callFunc cfg p s fi = .cont s') :
    (s'.frames = s.frames ∧ s'.gas.prepaid = s.gas.prepaid ∧ s'.gas.g ≤ s.gas.g ∧
      s'.gas.g ≤ s'.gas.remaining) ∨
    (∃ pf2, p.funcs[fi - p.m.imports.size]? = some pf2 ∧ ∃ fr : Frame,
      s'.frames = fr :: s.frames ∧ fr.fn = fi - p.m.imports.size ∧ fr.pc = 0 ∧
      fr.labels.map (fun l => (l.target, l.isLoop)) = [(pf2.code.size, false)] ∧
      s'.gas.prepaid = s.gas.prepaid ∧ s'.gas.g ≤ s.gas.g ∧ s'.gas.g ≤ s'.gas.remaining) := by
  unfold callFunc at h
  split at h
  · exact .inl (callHost_cont hh hg h)
  · obtain ⟨pf2, h1, fr, h2, h3, h4, h5, h6, h7, h8⟩ := enter_cont h
    exact .inr ⟨pf2, h1, fr, h2, h3, h4, h5, h8, h6, by rw [h7]; omega⟩

/-! ## Free instructions ahead of a `pc` (the potential) -/

/-- Free instructions at or after `pc`. -/
def freeFrom (code : Array Instr) (pc : Nat) : Nat := (code.toList.drop pc).countP isFreeInstr

theorem foldl_count (l : List Instr) (a : Nat) :
    l.foldl (fun a i => if isFreeInstr i then a + 1 else a) a = a + l.countP isFreeInstr := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.countP_cons, ih]
    cases isFreeInstr x <;> simp <;> omega

theorem freeCount_eq (code : Array Instr) : freeCount code = code.toList.countP isFreeInstr := by
  unfold freeCount
  rw [← Array.foldl_toList, foldl_count]
  simp

theorem freeFrom_le (code : Array Instr) (pc : Nat) : freeFrom code pc ≤ freeCount code := by
  rw [freeCount_eq]
  exact (List.drop_sublist pc code.toList).countP_le

theorem freeFrom_succ {code : Array Instr} {pc : Nat} {i : Instr} (hi : code[pc]? = some i) :
    freeFrom code pc = (if isFreeInstr i then 1 else 0) + freeFrom code (pc + 1) := by
  unfold freeFrom
  have h2 : code.toList[pc]? = some i := by simpa using hi
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h2
  rw [List.drop_eq_getElem_cons hlt, heq, List.countP_cons]
  cases isFreeInstr i <;> simp <;> omega

theorem freeFrom_succ_le (code : Array Instr) (pc : Nat) :
    freeFrom code (pc + 1) ≤ freeFrom code pc := by
  cases hi : code[pc]? with
  | some i => rw [freeFrom_succ hi]; omega
  | none =>
    have : code.size ≤ pc := by
      rcases Nat.lt_or_ge pc code.size with h | h
      · simp [h] at hi
      · exact h
    unfold freeFrom
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    simp

theorem freeFrom_anti (code : Array Instr) {a b : Nat} (hab : a ≤ b) :
    freeFrom code b ≤ freeFrom code a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.le_trans (freeFrom_succ_le code (a + n)) (ih (Nat.le_add_right _ _))

/-! ## Measure arithmetic -/

theorem mu_lt (K r A A' P P' c : Nat) (hK : 1 ≤ K) (hr : 0 < r) (hc : c ≤ 1)
    (hA : A' + r * c ≤ A) (hP : P' + (1 - c) ≤ P + (K - 1) * c) :
    K * (A' / r) + P' < K * (A / r) + P := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hA hP
    have h1 : A' / r ≤ A / r := Nat.div_le_div_right hA
    have := Nat.mul_le_mul_left K h1
    omega
  · simp only [Nat.mul_one, Nat.sub_self, Nat.add_zero] at hA hP
    have h1 : (A' + r) / r ≤ A / r := Nat.div_le_div_right hA
    rw [Nat.add_div_right _ hr] at h1
    have := Nat.mul_le_mul_left K h1
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

/-! ## Labels against the opener stack -/

def lproj (l : Label) : Nat × Bool := (l.target, l.isLoop)

theorem labelsOf_cons (pf : PFunc) (o : Nat) (os : List Nat) :
    labelsOf pf (o :: os) = labOf pf o :: labelsOf pf os := rfl

theorem labelsOf_length (pf : PFunc) (os : List Nat) : (labelsOf pf os).length = os.length + 1 := by
  simp [labelsOf]

theorem labels_cons {pf : PFunc} {L : List Label} {o : Nat} {os : List Nat}
    (h : L.map lproj = labelsOf pf (o :: os)) :
    ∃ lab L', L = lab :: L' ∧ lproj lab = labOf pf o ∧ L'.map lproj = labelsOf pf os := by
  cases L with
  | nil => simp [labelsOf] at h
  | cons lab L' =>
    rw [labelsOf_cons, List.map_cons, List.cons.injEq] at h
    exact ⟨lab, L', rfl, h.1, h.2⟩

theorem labels_nil {pf : PFunc} {L : List Label} (h : L.map lproj = labelsOf pf []) :
    ∃ lab, L = [lab] := by
  cases L with
  | nil => simp [labelsOf] at h
  | cons lab L' =>
    cases L' with
    | nil => exact ⟨lab, rfl⟩
    | cons _ _ => simp [labelsOf] at h

theorem labels_drop {pf : PFunc} {L : List Label} {os : List Nat}
    (h : L.map lproj = labelsOf pf os) (l : Nat) (hl : l ≤ os.length) :
    (L.drop l).map lproj = labelsOf pf (os.drop l) := by
  induction l generalizing L os with
  | zero => simpa using h
  | succ l ih =>
    cases os with
    | nil => simp at hl
    | cons o os =>
      obtain ⟨lab, L', rfl, -, h2⟩ := labels_cons h
      simp only [List.drop_succ_cons]
      exact ih h2 (by simp at hl; omega)

/-- `drop l` of an opener stack is again the opener stack of its head. -/
theorem nest_drop {pf : PFunc} {enc : Nat → List Nat} (hn : NestOK pf enc) :
    ∀ (l pc : Nat) (o : Nat) (rest : List Nat), pc < pf.code.size → (enc pc).drop l = o :: rest →
      o < pc ∧ enc o = rest ∧ (pf.code[o]?.map isOpener) = some true
  | 0, pc, o, rest, hpc, h => hn.chain pc o rest hpc (by simpa using h)
  | l + 1, pc, o, rest, hpc, h => by
    cases he : enc pc with
    | nil => rw [he] at h; simp at h
    | cons o0 r0 =>
      rw [he, List.drop_succ_cons] at h
      obtain ⟨h1, h2, -⟩ := hn.chain pc o0 r0 hpc he
      rw [← h2] at h
      obtain ⟨k1, k2, k3⟩ := nest_drop hn l o0 o rest (by omega) h
      exact ⟨by omega, k2, k3⟩

/-! ## The invariant -/

/-- A frame of `pf` whose position and labels agree with the nesting `enc`. -/
def FrameAt (cfg : NearCfg) (pf : PFunc) (enc : Nat → List Nat) (f : Frame) : Prop :=
  NestOK pf enc ∧ WC cfg pf enc ∧ Live pf enc f.pc ∧ f.labels.map lproj = labelsOf pf (enc f.pc)

def FrOK (cfg : NearCfg) (p : Prepared) (f : Frame) : Prop :=
  ∃ pf enc, p.funcs[f.fn]? = some pf ∧ freeCount pf.code ≤ 2 * cfg.maxBlocksPerFunction + 1 ∧
    FrameAt cfg pf enc f

def Pf (p : Prepared) (f : Frame) : Nat :=
  match p.funcs[f.fn]? with
  | some pf => freeFrom pf.code f.pc
  | none => 0

def Rq (p : Prepared) (f : Frame) : Nat :=
  match p.funcs[f.fn]? with
  | some pf => req pf f.pc
  | none => 0

def Psum (p : Prepared) (fs : List Frame) : Nat := (fs.map (Pf p)).sum

/-- The run invariant: `g ≤ remaining`, `prepaid` fixed, every frame consistent, and every caller
frame waiting at a group start. -/
def Inv (cfg : NearCfg) (p : Prepared) (G : Nat) (s : St) : Prop :=
  s.gas.g ≤ s.gas.remaining ∧ s.gas.prepaid = G ∧
    ∃ f fs, s.frames = f :: fs ∧ FrOK cfg p f ∧ ∀ f' ∈ fs, FrOK cfg p f' ∧ Rq p f' = 0

/-- The measure: costly-step capacity times `2M + 2`, plus the potential. -/
def mu (cfg : NearCfg) (p : Prepared) (s : St) : Nat :=
  match s.frames with
  | f :: fs => freeStepFactor cfg * ((s.gas.g + cfg.regularOpCost * Rq p f) / cfg.regularOpCost) +
      (Pf p f + Psum p fs)
  | [] => 0

theorem Pf_of {p : Prepared} {f : Frame} {pf : PFunc} (h : p.funcs[f.fn]? = some pf) :
    Pf p f = freeFrom pf.code f.pc := by simp [Pf, h]

theorem Rq_of {p : Prepared} {f : Frame} {pf : PFunc} (h : p.funcs[f.fn]? = some pf) :
    Rq p f = req pf f.pc := by simp [Rq, h]

/-- `req` one position at a time. -/
theorem req_unfold (pf : PFunc) (pc : Nat) (i : Instr) (hi : pf.code[pc]? = some i) :
    req pf pc = (match pf.gas[pc]? with
      | some (some _) => 0
      | _ => costOf i + (if fallsThrough i then req pf (pc + 1) else 0)) := by
  have hlt : pc < pf.code.size := by
    rcases Nat.lt_or_ge pc pf.code.size with h | h
    · exact h
    · simp [h] at hi
  unfold req
  have : pf.code.size - pc = (pf.code.size - (pc + 1)) + 1 := by omega
  rw [this, reqF]
  cases hg : pf.gas[pc]? with
  | none => simp [hi]
  | some e => cases e <;> simp [hi]

/-- What one `exec` step guarantees, relative to the state `s1` it starts from (after the charge
at `pc`, if any): the invariant again, the `g + r·req` part does not exceed `g1 + r·X` with `X`
the fall-through `req`, and the potential drops (free) or rises by at most `2M + 1` (costly). -/
def ExecPost (cfg : NearCfg) (p : Prepared) (G : Nat) (s1 s' : St) (pf : PFunc) (f : Frame)
    (fs : List Frame) (i : Instr) : Prop :=
  Inv cfg p G s' ∧ ∃ f' fs', s'.frames = f' :: fs' ∧
    s'.gas.g + cfg.regularOpCost * Rq p f' ≤
      s1.gas.g + cfg.regularOpCost * (if fallsThrough i then req pf (f.pc + 1) else 0) ∧
    Pf p f' + Psum p fs' + (1 - costOf i) ≤
      freeFrom pf.code f.pc + Psum p fs + (freeStepFactor cfg - 1) * costOf i

/-- Common hypotheses of an `exec` step. -/
structure ExecCtx (cfg : NearCfg) (p : Prepared) (G : Nat) (s1 : St) (pf : PFunc)
    (enc : Nat → List Nat) (f : Frame) (fs : List Frame) (i : Instr) : Prop where
  hfr : s1.frames = f :: fs
  hpf : p.funcs[f.fn]? = some pf
  hfc : freeCount pf.code ≤ 2 * cfg.maxBlocksPerFunction + 1
  hn : NestOK pf enc
  hw : WC cfg pf enc
  hlive : Live pf enc f.pc
  hlab : f.labels.map lproj = labelsOf pf (enc f.pc)
  hrest : ∀ f' ∈ fs, FrOK cfg p f' ∧ Rq p f' = 0
  hg : s1.gas.g ≤ s1.gas.remaining
  hG : s1.gas.prepaid = G
  hi : pf.code[f.pc]? = some i

theorem freeCount_le_K {cfg : NearCfg} {pf : PFunc}
    (h : freeCount pf.code ≤ 2 * cfg.maxBlocksPerFunction + 1) (q : Nat) :
    freeFrom pf.code q ≤ freeStepFactor cfg - 1 := by
  have := freeFrom_le pf.code q
  unfold freeStepFactor; omega

/-- Outcome: the top frame continues at `pc + 1` by fall-through. -/
theorem post_fall {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 s' : St} {pf : PFunc}
    {enc : Nat → List Nat} {f : Frame} {fs : List Frame} {i : Instr}
    (C : ExecCtx cfg p G s1 pf enc f fs i) (hft : fallsThrough i = true)
    (hne : i = .end_ → enc f.pc ≠ []) (f' : Frame) (hfr' : s'.frames = f' :: fs)
    (hfn' : f'.fn = f.fn) (hpc' : f'.pc = f.pc + 1)
    (hlab' : f'.labels.map lproj = labelsOf pf (enc (f.pc + 1)))
    (hgas : s'.gas.g ≤ s1.gas.g) (hrem : s'.gas.g ≤ s'.gas.remaining) (hG : s'.gas.prepaid = G)
    (hP : freeFrom pf.code (f.pc + 1) + (1 - costOf i) ≤
      freeFrom pf.code f.pc + (freeStepFactor cfg - 1) * costOf i) :
    ExecPost cfg p G s1 s' pf f fs i := by
  have hpf' : p.funcs[f'.fn]? = some pf := by rw [hfn']; exact C.hpf
  have hlive' : Live pf enc f'.pc := by
    rw [hpc']; exact .step _ _ _ C.hlive (.fall _ i C.hi hft hne)
  refine ⟨⟨hrem, hG, f', fs, hfr', ⟨pf, enc, hpf', C.hfc, C.hn, C.hw, hlive', by rw [hpc']; exact hlab'⟩,
    C.hrest⟩, f', fs, hfr', ?_, ?_⟩
  · rw [Rq_of hpf', hpc', hft, if_pos rfl]; omega
  · rw [Pf_of hpf', hpc']; omega

/-- Outcome: the top frame jumps to a static jump successor `q`. -/
theorem post_jump {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 s' : St} {pf : PFunc}
    {enc : Nat → List Nat} {f : Frame} {fs : List Frame} {i : Instr}
    (C : ExecCtx cfg p G s1 pf enc f fs i) (q : Nat) (hs : Succ pf enc f.pc q true)
    (f' : Frame) (hfr' : s'.frames = f' :: fs)
    (hfn' : f'.fn = f.fn) (hpc' : f'.pc = q)
    (hlab' : f'.labels.map lproj = labelsOf pf (enc q))
    (hgas : s'.gas.g ≤ s1.gas.g) (hrem : s'.gas.g ≤ s'.gas.remaining) (hG : s'.gas.prepaid = G)
    (hP : freeFrom pf.code q + (1 - costOf i) ≤
      freeFrom pf.code f.pc + (freeStepFactor cfg - 1) * costOf i) :
    ExecPost cfg p G s1 s' pf f fs i := by
  have hpf' : p.funcs[f'.fn]? = some pf := by rw [hfn']; exact C.hpf
  have hlive' : Live pf enc f'.pc := by rw [hpc']; exact .step _ _ _ C.hlive hs
  have hreq : req pf q = 0 := C.hw.jump _ _ C.hlive hs
  refine ⟨⟨hrem, hG, f', fs, hfr', ⟨pf, enc, hpf', C.hfc, C.hn, C.hw, hlive', by rw [hpc']; exact hlab'⟩,
    C.hrest⟩, f', fs, hfr', ?_, ?_⟩
  · rw [Rq_of hpf', hpc', hreq]; omega
  · rw [Pf_of hpf', hpc']; omega

/-- Outcome: the top frame returns to its caller. -/
theorem post_ret {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 s' : St} {pf : PFunc}
    {enc : Nat → List Nat} {f : Frame} {fs : List Frame} {i : Instr}
    (C : ExecCtx cfg p G s1 pf enc f fs i) (hfr' : s'.frames = fs) (hne : fs ≠ [])
    (hgas : s'.gas = s1.gas)
    (hP : 1 - costOf i ≤ freeFrom pf.code f.pc + (freeStepFactor cfg - 1) * costOf i) :
    ExecPost cfg p G s1 s' pf f fs i := by
  cases fs with
  | nil => exact absurd rfl hne
  | cons f2 fs2 =>
    have h2 := C.hrest f2 (by simp)
    refine ⟨⟨by rw [hgas]; exact C.hg, by rw [hgas]; exact C.hG, f2, fs2, hfr', h2.1,
      fun f' hf' => C.hrest f' (by simp [hf'])⟩, f2, fs2, hfr', ?_, ?_⟩
    · rw [h2.2, hgas]; omega
    · simp only [Psum, List.map_cons, List.sum_cons]; omega

theorem setFrame_gas (s : St) (F : Frame) : (setFrame s F).gas = s.gas := by
  unfold setFrame; split <;> rfl

theorem setFrame_prepaid (s : St) (F : Frame) : (setFrame s F).gas.prepaid = s.gas.prepaid := by
  rw [setFrame_gas]

theorem P_free {code : Array Instr} {pc : Nat} {i : Instr} (K : Nat) (hi : code[pc]? = some i)
    (hfree : isFreeInstr i = true) :
    freeFrom code (pc + 1) + (1 - costOf i) ≤ freeFrom code pc + K * costOf i := by
  rw [freeFrom_succ hi]; simp [costOf, hfree]; omega

theorem P_costly {code : Array Instr} {pc q K : Nat} {i : Instr} (hfree : isFreeInstr i = false)
    (hq : freeFrom code q ≤ freeFrom code pc + K) :
    freeFrom code q + (1 - costOf i) ≤ freeFrom code pc + K * costOf i := by
  simp [costOf, hfree]; omega

theorem ExecCtx.lt {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 : St} {pf : PFunc}
    {enc : Nat → List Nat} {f : Frame} {fs : List Frame} {i : Instr}
    (C : ExecCtx cfg p G s1 pf enc f fs i) : f.pc < pf.code.size := by
  rcases Nat.lt_or_ge f.pc pf.code.size with h | h
  · exact h
  · have := C.hi; simp [h] at this

/-- The same context after popping operands (`fg` unchanged). -/
theorem ExecCtx.pop {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 s2 : St} {pf : PFunc}
    {enc : Nat → List Nat} {f : Frame} {fs : List Frame} {i : Instr}
    (C : ExecCtx cfg p G s1 pf enc f fs i) (hs : fg s2 = fg s1) :
    ExecCtx cfg p G s2 pf enc f fs i := by
  simp only [fg, Prod.mk.injEq] at hs
  exact ⟨hs.1.trans C.hfr, C.hpf, C.hfc, C.hn, C.hw, C.hlive, C.hlab, C.hrest,
    by rw [hs.2]; exact C.hg, by rw [hs.2]; exact C.hG, C.hi⟩

theorem ExecPost.of_pop {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 s2 s' : St} {pf : PFunc}
    {f : Frame} {fs : List Frame} {i : Instr} (hs : fg s2 = fg s1)
    (h : ExecPost cfg p G s2 s' pf f fs i) : ExecPost cfg p G s1 s' pf f fs i := by
  simp only [fg, Prod.mk.injEq] at hs
  obtain ⟨a, f', fs', b, c, d⟩ := h
  exact ⟨a, f', fs', b, by rw [← hs.2]; exact c, d⟩

/-- Fall-through to `pc + 1` with the labels kept, for an instruction that is not a block
delimiter. -/
theorem post_next {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 s' : St} {pf : PFunc}
    {enc : Nat → List Nat} {f : Frame} {fs : List Frame} {i : Instr}
    (C : ExecCtx cfg p G s1 pf enc f fs i) (hft : fallsThrough i = true)
    (hop : isOpener i = false) (hne : i ≠ .else_) (hnend : i ≠ .end_)
    (hfree : isFreeInstr i = false) (f' : Frame) (hfr' : s'.frames = f' :: fs)
    (hfn' : f'.fn = f.fn) (hpc' : f'.pc = f.pc + 1) (hl' : f'.labels = f.labels)
    (hgas : s'.gas.g ≤ s1.gas.g) (hrem : s'.gas.g ≤ s'.gas.remaining) (hG : s'.gas.prepaid = G) :
    ExecPost cfg p G s1 s' pf f fs i :=
  post_fall C hft (fun h => absurd h hnend) f' hfr' hfn' hpc'
    (by rw [hl', C.hn.other _ _ C.hi hop hne hnend]; exact C.hlab) hgas hrem hG
    (P_costly hfree (by have := freeFrom_succ_le pf.code f.pc; omega))

/-- A branch through `doBr`. -/
theorem post_br {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 s' : St} {pf : PFunc}
    {enc : Nat → List Nat} {f : Frame} {fs : List Frame} {i : Instr}
    (C : ExecCtx cfg p G s1 pf enc f fs i) (hfree : isFreeInstr i = false) (l : Nat)
    (hS : ∀ q, brTarget pf enc f.pc l = some q → Succ pf enc f.pc q true)
    (h : doBr p s1 f l = .cont s') : ExecPost cfg p G s1 s' pf f fs i := by
  have hcost : costOf i = 1 := by simp [costOf, hfree]
  rcases doBr_cont C.hfr h with ⟨-, a, b, c⟩ | ⟨hl, lab, hlab, hgas, hfr'⟩
  · exact post_ret C a c b (by rw [hcost]; omega)
  · have hlen : f.labels.length = (enc f.pc).length + 1 := by
      rw [← labelsOf_length pf, ← C.hlab, List.length_map]
    have hlt : l < (enc f.pc).length := by omega
    have hd : (enc f.pc).drop l = (enc f.pc)[l] :: (enc f.pc).drop (l + 1) :=
      List.drop_eq_getElem_cons hlt
    obtain ⟨ho1, ho2, ho3⟩ := nest_drop C.hn l f.pc _ _ C.lt hd
    have hd' : f.labels.drop l = lab :: f.labels.drop (l + 1) := by
      obtain ⟨hlt', heq⟩ := List.getElem?_eq_some_iff.mp hlab
      rw [List.drop_eq_getElem_cons hlt', heq]
    have hD := labels_drop C.hlab l (Nat.le_of_lt hlt)
    rw [hd', hd, List.map_cons, labelsOf_cons, List.cons.injEq] at hD
    obtain ⟨hlp, hD2⟩ := hD
    rw [← ho2] at hD2
    generalize ho : (enc f.pc)[l] = o at hd ho1 ho2 ho3 hlp hD2
    have hT : lab.target = labTarget pf o := congrArg Prod.fst hlp
    have hL : lab.isLoop = (pf.code[o]?.map isLoopI).getD false := congrArg Prod.snd hlp
    have hbt : brTarget pf enc f.pc l = some lab.target := by
      simp [brTarget, List.getElem?_eq_getElem hlt, ho, hT]
    have hs := hS _ hbt
    have hP : freeFrom pf.code lab.target + (1 - costOf i) ≤
        freeFrom pf.code f.pc + (freeStepFactor cfg - 1) * costOf i :=
      P_costly hfree (by have := freeCount_le_K C.hfc lab.target; omega)
    cases hco : pf.code[o]? with
    | none => rw [hco] at ho3; simp at ho3
    | some io =>
      rw [hco] at ho3
      simp only [Option.map_some, Option.some.injEq] at ho3
      obtain ⟨_, -, hcodee, henc1, henc2⟩ := C.hn.opener o io hco ho3
      cases io with
      | loop bt =>
        have hlp' : lab.isLoop = true := by rw [hL, hco]; rfl
        have ht' : lab.target = o + 1 := by rw [hT]; simp [labTarget, hco]
        refine post_jump C lab.target hs _ hfr' rfl rfl ?_ (by rw [hgas]; exact Nat.le_refl _) (by rw [hgas]; exact C.hg)
          (by rw [hgas]; exact C.hG) hP
        simp only [hlp', if_true]
        rw [hd', List.map_cons, hlp, ht', henc1, labelsOf_cons, hD2]
      | block bt =>
        have hlp' : lab.isLoop = false := by rw [hL, hco]; rfl
        have ht' : lab.target = endAt pf o + 1 := by rw [hT]; simp [labTarget, hco]
        have he := ((C.hn.end_ _ hcodee).2 o (enc o) henc2).2
        refine post_jump C lab.target hs _ hfr' rfl rfl ?_ (by rw [hgas]; exact Nat.le_refl _) (by rw [hgas]; exact C.hg)
          (by rw [hgas]; exact C.hG) hP
        simp only [hlp', Bool.false_eq_true, if_false]
        rw [hD2, ht', he]
      | if_ bt =>
        have hlp' : lab.isLoop = false := by rw [hL, hco]; rfl
        have ht' : lab.target = endAt pf o + 1 := by rw [hT]; simp [labTarget, hco]
        have he := ((C.hn.end_ _ hcodee).2 o (enc o) henc2).2
        refine post_jump C lab.target hs _ hfr' rfl rfl ?_ (by rw [hgas]; exact Nat.le_refl _) (by rw [hgas]; exact C.hg)
          (by rw [hgas]; exact C.hG) hP
        simp only [hlp', Bool.false_eq_true, if_false]
        rw [hD2, ht', he]
      | _ => simp [isOpener] at ho3

/-- A call through `callFunc`, after advancing the caller to `pc + 1`. -/
theorem post_call {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 s' : St} {pf : PFunc}
    {enc : Nat → List Nat} {f : Frame} {fs : List Frame} {i : Instr}
    (hfn : ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf) (hh : HostsOK)
    (C : ExecCtx cfg p G s1 pf enc f fs i) (hcall : isCallI i = true)
    (hft : fallsThrough i = true) (hop : isOpener i = false) (hne : i ≠ .else_)
    (hnend : i ≠ .end_) (hfree : isFreeInstr i = false) (fi : Nat)
    (h : callFunc cfg p (setFrame s1 { f with pc := f.pc + 1 }) fi = .cont s') :
    ExecPost cfg p G s1 s' pf f fs i := by
  have hfr3 := setFrame_frames C.hfr { f with pc := f.pc + 1 }
  have hg3 := setFrame_gas s1 { f with pc := f.pc + 1 }
  rcases callFunc_cont hh (by rw [hg3]; exact C.hg) h with
    ⟨a, b, c, d⟩ | ⟨pf2, hpf2, fr, hfr', hfn2, hpc2, hlab2, hG2, hle2, hrem2⟩
  · rw [hfr3] at a
    rw [hg3] at b c
    exact post_next C hft hop hne hnend hfree _ a rfl rfl rfl c d (by rw [b]; exact C.hG)
  · rw [hfr3] at hfr'
    rw [hg3] at hle2 hG2
    obtain ⟨enc2, hn2, hw2, hfc2⟩ := hfn _ _ hpf2
    have hpf2' : p.funcs[fr.fn]? = some pf2 := by rw [hfn2]; exact hpf2
    have hlab1 : ({ f with pc := f.pc + 1 } : Frame).labels.map lproj = labelsOf pf (enc (f.pc + 1)) := by
      show f.labels.map lproj = _
      rw [C.hn.other _ _ C.hi hop hne hnend]; exact C.hlab
    have hlive1 : Live pf enc (f.pc + 1) := .step _ _ _ C.hlive (.fall _ i C.hi hft (fun h => absurd h hnend))
    have hreq1 : req pf (f.pc + 1) = 0 := C.hw.ret _ i C.hlive C.hi hcall
    have hF1 : FrOK cfg p { f with pc := f.pc + 1 } := ⟨pf, enc, C.hpf, C.hfc, C.hn, C.hw, hlive1, hlab1⟩
    have hR1 : Rq p { f with pc := f.pc + 1 } = 0 := by
      rw [Rq_of (f := { f with pc := f.pc + 1 }) C.hpf]; exact hreq1
    refine ⟨⟨hrem2, by rw [hG2]; exact C.hG, fr, _, hfr', ⟨pf2, enc2, hpf2', hfc2, hn2, hw2,
      by rw [hpc2]; exact .entry, by rw [hpc2, hn2.zero]; exact hlab2⟩, ?_⟩, fr, _, hfr', ?_, ?_⟩
    · intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | hf'
      · exact ⟨hF1, hR1⟩
      · exact C.hrest f' hf'
    · rw [Rq_of hpf2', hpc2, hw2.entry]; omega
    · rw [Pf_of hpf2', hpc2]
      simp only [Psum, List.map_cons, List.sum_cons]
      rw [Pf_of (f := { f with pc := f.pc + 1 }) C.hpf]
      have k1 := freeCount_le_K hfc2 0
      have k2 := freeFrom_succ_le pf.code f.pc
      simp only [costOf, hfree, Bool.false_eq_true, if_false]
      show freeFrom pf2.code 0 + (freeFrom pf.code (f.pc + 1) + (fs.map (Pf p)).sum) + (1 - 1) ≤
        freeFrom pf.code f.pc + (fs.map (Pf p)).sum + (freeStepFactor cfg - 1) * 1
      omega

theorem popN_fg {s s2 : St} {c : Nat} (hp : popN s = (c, s2)) : fg s2 = fg s := by
  have := fg_popN s; rw [hp] at this; exact this

/-- One `exec` step from a consistent frame. -/
theorem exec_post {cfg : NearCfg} {p : Prepared} {G : Nat} {s1 s' : St} {pf : PFunc}
    {enc : Nat → List Nat} {f : Frame} {fs : List Frame} {i : Instr}
    (hfn : ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf) (hh : HostsOK)
    (C : ExecCtx cfg p G s1 pf enc f fs i) (h : exec cfg p s1 f pf i = .cont s') :
    ExecPost cfg p G s1 s' pf f fs i := by
  cases hc : isControl i with
  | false =>
    obtain ⟨f', h1, h2, h3, h4, h5⟩ := exec_plain cfg p s1 f fs C.hfr pf i hc s' h
    obtain ⟨hft, hop, hfree, -, hne, hnend⟩ := plain_facts hc
    exact post_next C hft hop hne hnend hfree f' h1 h2 h3 h4 (by rw [h5]; exact Nat.le_refl _) (by rw [h5]; exact C.hg)
      (by rw [h5]; exact C.hG)
  | true =>
    cases i with
    | unreachable => simp [exec] at h
    | block bt =>
      obtain ⟨hend, hlt, hcode, henc1, henc2⟩ := C.hn.opener f.pc _ C.hi rfl
      simp only [exec, hend] at h
      cases h
      refine post_fall C rfl (fun h => by cases h) _ (setFrame_frames C.hfr _) rfl rfl ?_
        (by rw [setFrame_gas]; exact Nat.le_refl _) (by rw [setFrame_gas]; exact C.hg) (by rw [setFrame_gas]; exact C.hG)
        (P_free _ C.hi rfl)
      show (_ :: f.labels).map lproj = _
      rw [henc1, labelsOf_cons, List.map_cons, C.hlab]
      simp [lproj, labOf, labTarget, C.hi, isLoopI]
    | loop bt =>
      obtain ⟨hend, hlt, hcode, henc1, henc2⟩ := C.hn.opener f.pc _ C.hi rfl
      simp only [exec] at h
      cases h
      refine post_fall C rfl (fun h => by cases h) _ (setFrame_frames C.hfr _) rfl rfl ?_
        (by rw [setFrame_gas]; exact Nat.le_refl _) (by rw [setFrame_gas]; exact C.hg) (by rw [setFrame_gas]; exact C.hG)
        (P_free _ C.hi rfl)
      show (_ :: f.labels).map lproj = _
      rw [henc1, labelsOf_cons, List.map_cons, C.hlab]
      simp [lproj, labOf, labTarget, C.hi, isLoopI]
    | if_ bt =>
      obtain ⟨hend, hlt, hcode, henc1, henc2⟩ := C.hn.opener f.pc _ C.hi rfl
      obtain ⟨helse, hif⟩ := C.hn.if_ f.pc bt C.hi
      rcases hp : popN s1 with ⟨c, s2⟩
      have C2 := C.pop (popN_fg hp)
      apply ExecPost.of_pop (popN_fg hp)
      simp only [exec, hp, hend, helse] at h
      have hP : ∀ q, freeFrom pf.code q + (1 - costOf (Instr.if_ bt)) ≤
          freeFrom pf.code f.pc + (freeStepFactor cfg - 1) * costOf (Instr.if_ bt) := fun q =>
        P_costly rfl (by have := freeCount_le_K C.hfc q; omega)
      split at h
      · cases h
        refine post_fall C2 rfl (fun h => by cases h) _ (setFrame_frames C2.hfr _) rfl rfl ?_
          (by rw [setFrame_gas]; exact Nat.le_refl _) (by rw [setFrame_gas]; exact C2.hg)
          (by rw [setFrame_gas]; exact C2.hG) (hP _)
        show (_ :: f.labels).map lproj = _
        rw [henc1, labelsOf_cons, List.map_cons, C.hlab]
        simp [lproj, labOf, labTarget, C.hi, isLoopI]
      · split at h
        · rename_i hne
          cases h
          have henc3 : enc (elseAt pf f.pc + 1) = f.pc :: enc f.pc := by
            rcases hif with h0 | ⟨-, -, -, h3⟩
            · exact absurd h0 hne
            · exact h3
          refine post_jump C2 _ (.ifElse _ bt C.hi hne) _ (setFrame_frames C2.hfr _) rfl rfl ?_
            (by rw [setFrame_gas]; exact Nat.le_refl _) (by rw [setFrame_gas]; exact C2.hg)
            (by rw [setFrame_gas]; exact C2.hG) (hP _)
          show (_ :: f.labels).map lproj = _
          rw [henc3, labelsOf_cons, List.map_cons, C.hlab]
          simp [lproj, labOf, labTarget, C.hi, isLoopI]
        · rename_i heq
          have heq' : elseAt pf f.pc = endAt pf f.pc := by
            simpa using heq
          cases h
          have he := ((C.hn.end_ _ hcode).2 f.pc (enc f.pc) henc2).2
          refine post_jump C2 _ (.ifEnd _ bt C.hi heq') _ (setFrame_frames C2.hfr _) rfl rfl ?_
            (by rw [setFrame_gas]; exact Nat.le_refl _) (by rw [setFrame_gas]; exact C2.hg)
            (by rw [setFrame_gas]; exact C2.hG) (hP _)
          show f.labels.map lproj = _
          rw [he]; exact C.hlab
    | else_ =>
      obtain ⟨o, rest, bt, henc, hco, hel, hlt, henc'⟩ := C.hn.else_ f.pc C.hi
      have hl := C.hlab
      rw [henc] at hl
      obtain ⟨lab, L', hL, hlab1, hL'⟩ := labels_cons hl
      simp only [exec, hL] at h
      cases h
      have hT : lab.target = endAt pf o + 1 := by
        have := congrArg Prod.fst hlab1
        simpa [lproj, labOf, labTarget, hco] using this
      obtain ⟨-, -, hcodeo, -, henco⟩ := C.hn.opener o _ hco rfl
      have he := ((C.hn.end_ _ hcodeo).2 o (enc o) henco).2
      have hch := (C.hn.chain f.pc o rest C.lt henc).2.1
      refine post_jump C _ (.else_ _ o rest C.hi henc) _ (setFrame_frames C.hfr _) rfl hT ?_
        (by rw [setFrame_gas]; exact Nat.le_refl _) (by rw [setFrame_gas]; exact C.hg) (by rw [setFrame_gas]; exact C.hG) ?_
      · show L'.map lproj = _
        rw [he, hch]; exact hL'
      · have k1 := freeFrom_succ C.hi
        have k2 := freeFrom_anti pf.code (show f.pc + 1 ≤ endAt pf o + 1 by omega)
        simp only [costOf, isFreeInstr, if_true] at k1 ⊢
        omega
    | end_ =>
      cases henc : enc f.pc with
      | nil =>
        have hl := C.hlab
        rw [henc] at hl
        obtain ⟨lab, hL⟩ := labels_nil hl
        simp only [exec, hL] at h
        obtain ⟨a, b, c⟩ := doReturn_cont C.hfr h
        refine post_ret C a c b ?_
        have k1 := freeFrom_succ C.hi
        simp only [costOf, isFreeInstr, if_true] at k1 ⊢
        omega
      | cons o rest =>
        have hl := C.hlab
        rw [henc] at hl
        obtain ⟨lab, L', hL, -, hL'⟩ := labels_cons hl
        cases L' with
        | nil => simp [labelsOf] at hL'
        | cons lab2 L'' =>
          simp only [exec, hL] at h
          cases h
          have he := ((C.hn.end_ _ C.hi).2 o rest henc).2
          refine post_fall C rfl (fun _ => by rw [henc]; simp) _ (setFrame_frames C.hfr _) rfl rfl ?_
            (by rw [setFrame_gas]; exact Nat.le_refl _) (by rw [setFrame_gas]; exact C.hg)
            (by rw [setFrame_gas]; exact C.hG) (P_free _ C.hi rfl)
          show (lab2 :: L'').map lproj = _
          rw [he]; exact hL'
    | br l =>
      simp only [exec] at h
      exact post_br C rfl l (fun q hq => .br _ l q C.hi hq) h
    | brIf l =>
      rcases hp : popN s1 with ⟨c, s2⟩
      have C2 := C.pop (popN_fg hp)
      apply ExecPost.of_pop (popN_fg hp)
      simp only [exec, hp] at h
      split at h
      · exact post_br C2 rfl l (fun q hq => .brIf _ l q C.hi hq) h
      · cases h
        exact post_next C2 rfl rfl (by intro h; cases h) (by intro h; cases h) rfl _
          (setFrame_frames C2.hfr _) rfl rfl rfl (by rw [setFrame_gas]; exact Nat.le_refl _)
          (by rw [setFrame_gas]; exact C2.hg) (by rw [setFrame_gas]; exact C2.hG)
    | brTable ls d =>
      rcases hp : popN s1 with ⟨c, s2⟩
      have C2 := C.pop (popN_fg hp)
      apply ExecPost.of_pop (popN_fg hp)
      simp only [exec, hp] at h
      refine post_br C2 rfl _ (fun q hq => .brTable _ ls d _ q C.hi ?_ hq) h
      cases hx : ls[c]? with
      | none => right; simp
      | some x =>
        left
        simp only [Option.getD_some]
        exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hx)
    | ret =>
      simp only [exec] at h
      obtain ⟨a, b, c⟩ := doReturn_cont C.hfr h
      exact post_ret C a c b (by simp [costOf, isFreeInstr])
    | call fi =>
      simp only [exec] at h
      exact post_call hfn hh C rfl rfl rfl (by intro h; cases h) (by intro h; cases h) rfl fi h
    | callIndirect ty tab =>
      rcases hp : popN s1 with ⟨c, s2⟩
      have C2 := C.pop (popN_fg hp)
      apply ExecPost.of_pop (popN_fg hp)
      simp only [exec, hp] at h
      split at h
      · cases h
      · cases h
      · split at h
        · split at h
          · cases h
          · exact post_call hfn hh C2 rfl rfl rfl (by intro h; cases h) (by intro h; cases h) rfl _ h
        · cases h
    | _ => simp [isControl] at hc

/-! ## One step, the run, one entry -/

theorem step_post {cfg : NearCfg} {p : Prepared} {G : Nat} (hr : 0 < cfg.regularOpCost)
    (hfn : ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf) (hh : HostsOK) {s s' : St}
    (hI : Inv cfg p G s) (h : step cfg p s = .cont s') :
    Inv cfg p G s' ∧ mu cfg p s' < mu cfg p s := by
  obtain ⟨hg, hG, f, fs, hfr, ⟨pf, enc, hpf, hfc, hn, hw, hlive, hlab⟩, hrest⟩ := hI
  unfold step at h
  rw [hfr] at h
  simp only [hpf] at h
  cases hi : pf.code[f.pc]? with
  | none => simp [hi] at h
  | some i =>
    simp only [hi] at h
    have hK : 1 ≤ freeStepFactor cfg := by unfold freeStepFactor; omega
    have hc1 : costOf i ≤ 1 := by unfold costOf; split <;> omega
    cases hgt : pf.gas[f.pc]? with
    | none => simp [hgt] at h
    | some e =>
      simp only [hgt] at h
      cases e with
      | none =>
        have hreq : req pf f.pc = costOf i + (if fallsThrough i then req pf (f.pc + 1) else 0) := by
          rw [req_unfold pf f.pc i hi, hgt]
        have C : ExecCtx cfg p G s pf enc f fs i :=
          ⟨hfr, hpf, hfc, hn, hw, hlive, hlab, hrest, hg, hG, hi⟩
        obtain ⟨hI', f', fs', hfr', hA, hP⟩ := exec_post hfn hh C h
        refine ⟨hI', ?_⟩
        unfold mu
        rw [hfr', hfr]
        simp only
        rw [Rq_of hpf, Pf_of hpf, hreq]
        apply mu_lt _ _ _ _ _ _ (costOf i) hK hr hc1
        · rw [Nat.mul_add] at *; omega
        · omega
      | some ke =>
        obtain ⟨k, fee⟩ := ke
        have hreq : req pf f.pc = 0 := by rw [req_unfold pf f.pc i hi, hgt]
        simp only at h
        cases hch : charge s fee (if k = .linear then topCount s else 0) with
        | cont s1 =>
          simp only [hch] at h
          obtain ⟨hle, rfl⟩ := charge_cont' hch
          have C : ExecCtx cfg p G { s with gas := { s.gas with g := s.gas.g -
              ((if k = .linear then topCount s else 0) * fee.l + fee.c) } } pf enc f fs i :=
            ⟨hfr, hpf, hfc, hn, hw, hlive, hlab, hrest, by simp only [Gas.remaining, Gas.used] at hg ⊢; omega, hG, hi⟩
          obtain ⟨hI', f', fs', hfr', hA, hP⟩ := exec_post hfn hh C h
          have hwc := hw.charged f.pc i k fee hlive hi hgt
          refine ⟨hI', ?_⟩
          unfold mu
          rw [hfr', hfr]
          simp only
          rw [Rq_of hpf, Pf_of hpf, hreq]
          apply mu_lt _ _ _ _ _ _ (costOf i) hK hr hc1
          · have hA' : s'.gas.g + cfg.regularOpCost * Rq p f' ≤
                (s.gas.g - ((if k = .linear then topCount s else 0) * fee.l + fee.c)) +
                  cfg.regularOpCost * (if fallsThrough i then req pf (f.pc + 1) else 0) := hA
            rw [Nat.mul_add] at hwc
            have : fee.c ≤ (if k = .linear then topCount s else 0) * fee.l + fee.c := Nat.le_add_left _ _
            omega
          · omega
        | fin _ => simp [hch] at h
        | abort _ _ => simp [hch] at h
        | unmodeled _ => simp [hch] at h

/-- Above the measure, more fuel never changes the result of `run`. -/
theorem run_stable {cfg : NearCfg} {p : Prepared} {G : Nat} (hr : 0 < cfg.regularOpCost)
    (hfn : ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf) (hh : HostsOK) :
    ∀ (n : Nat) (s : St), Inv cfg p G s → mu cfg p s < n → ∀ k, run cfg p (n + k) s = run cfg p n s
  | 0, _, _, hmu, _ => absurd hmu (Nat.not_lt_zero _)
  | n + 1, s, hI, hmu, k => by
    rw [Nat.add_right_comm]
    simp only [run]
    cases hs : step cfg p s with
    | cont s' =>
      obtain ⟨hI', hlt⟩ := step_post hr hfn hh hI hs
      exact run_stable hr hfn hh n s' hI' (by omega) k
    | fin _ => rfl
    | abort _ _ => rfl
    | unmodeled _ => rfl

/-- **Fuel sufficiency for one entry.** With every prepared function satisfying `FnOK` and the
host arms `HostsOK`, a `callEntry` with fuel at least `wasmFuel cfg prepaid` has the result it has
with any larger fuel: the step budget is never what stops the run. -/
theorem callEntry_stable {cfg : NearCfg} {p : Prepared} (hr : 0 < cfg.regularOpCost)
    (hfn : ∀ (j : Nat) (pf : PFunc), p.funcs[j]? = some pf → FnOK cfg pf) (hh : HostsOK) (s : St) (fi n k : Nat)
    (hn : wasmFuel cfg s.gas.prepaid ≤ n) :
    callEntry cfg p (n + k) s fi = callEntry cfg p n s fi := by
  unfold callEntry
  simp only
  cases he : enter p { s with gas := { s.gas with g := s.gas.remaining }, stack := #[], frames := [] } fi with
  | cont s1 =>
    simp only
    obtain ⟨pf2, hpf2, fr, hfr, hfn2, hpc2, hlab2, hle, hrem, hG⟩ := enter_cont he
    obtain ⟨enc2, hn2, hw2, hfc2⟩ := hfn _ _ hpf2
    have hpf2' : p.funcs[fr.fn]? = some pf2 := by rw [hfn2]; exact hpf2
    have hI : Inv cfg p s.gas.prepaid s1 := by
      refine ⟨?_, hG, fr, [], hfr, ⟨pf2, enc2, hpf2', hfc2, hn2, hw2, by rw [hpc2]; exact .entry,
        by rw [hpc2, hn2.zero]; exact hlab2⟩, by simp⟩
      rw [hrem]; exact hle
    have hmu : mu cfg p s1 < n := by
      unfold mu
      rw [hfr]
      simp only
      rw [Rq_of hpf2', Pf_of hpf2', hpc2, hw2.entry]
      have k1 := freeCount_le_K hfc2 0
      have k2 : s1.gas.g ≤ s.gas.prepaid := by
        have : s1.gas.g ≤ s.gas.remaining := hle
        simp only [Gas.remaining] at this; omega
      have k3 : s1.gas.g / cfg.regularOpCost ≤ s.gas.prepaid / cfg.regularOpCost :=
        Nat.div_le_div_right k2
      have k4 := Nat.mul_le_mul_left (freeStepFactor cfg) k3
      have k5 : freeStepFactor cfg = 2 * cfg.maxBlocksPerFunction + 2 := rfl
      simp only [Nat.mul_zero, Nat.add_zero, Psum, List.map_nil, List.sum_nil]
      unfold wasmFuel at hn
      rw [Nat.add_mul] at hn
      have k6 : s.gas.prepaid / cfg.regularOpCost * freeStepFactor cfg =
          freeStepFactor cfg * (s.gas.prepaid / cfg.regularOpCost) := Nat.mul_comm _ _
      omega
    rw [run_stable hr hfn hh n s1 hI hmu k]
  | fin _ => rfl
  | abort _ _ => rfl
  | unmodeled _ => rfl

end NearSpecV3.Wasm.FuelGen

#print axioms NearSpecV3.Wasm.FuelGen.callEntry_stable
