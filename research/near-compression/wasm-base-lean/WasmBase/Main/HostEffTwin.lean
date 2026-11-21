import WasmBase.Main.HostCover

/-!
# WasmBase.Main.HostEffTwin — the σ-free post-state transfer of a HOST row (E2E M6, COVER item 2)

`HostEffRely` (`Main/HostSigmaBridge.lean`) asks that the post-state relation `Rel` transfer from the
honest post-state `xH = eff.apply uH` to the twin post-state `x = eff.apply u`.  As stated there the
pre-call states `uH`, `u` are **arbitrary** (any `HostEff` decomposition), so it cannot be proved: the
twin's frames, stack base and memory come from `u`, about which nothing is assumed.  This file proves
the transfer for the decomposition the two-run lemma actually produces (`step_host_two_run`):
`uH = setFrame {sH with gas := G} {fH with pc := fH.pc + 1}`, `u = setFrame {s with gas := G}
{f with pc := f.pc + 1}`, `sH`/`s` related to the row by `RelW`.

**`rel_twin_post`**: the twin's post `RelW` is built with

* environment live set `E'.live := stepLive live cons prod` restricted to spaces `≠ 0, ≠ lsp`
  (so the frame/stack/locals view is re-derived, the rest — globals, call chain, budget, memory,
  registers, gas register — is the twin's own traffic after the call);
* stack producer times: the twin's `tps` below the call's base `size − k`, the honest post `tps'H`
  above it (the top `k` slots carry the *same* live messages in both pre-states: they are consumed);
* memory: the twin's touched set `T` off the consumed addresses, the honest post's touched set on
  them; bytes on consumed addresses agree in the two pre-states (`RelW.byte_msg`), hence after the
  common writes (`agree_wbAll`); off them, the call writes nothing (`hwr`, the write-coverage premise)
  and consumes / produces nothing (the produced space-3 messages are paired with consumed ones at
  the same address, `hpair`).

The message-level premises are exactly what the AIR gives a HOST row (`Main/HostCoverAir.lean`):
spaces `0, 3, 6, 7` only, stack messages only in the top `k` slots, the top `k` slots consumed,
produced memory messages paired with consumed ones; and the out STATE message keeps `cid`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips
open NearSpecV3.Wasm hiding P
open HostFoot TwoRun
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Shape of `eff.apply (setFrame …)` -/

theorem setFrame_cons {s : St} {f : Frame} {rest : List Frame} (h : s.frames = f :: rest) (f1 : Frame) :
    (setFrame s f1).frames = f1 :: rest ∧ (setFrame s f1).stack = s.stack ∧ (setFrame s f1).pages = s.pages ∧
      (setFrame s f1).globals = s.globals ∧ (setFrame s f1).stackRem = s.stackRem := by
  unfold setFrame; rw [h]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem apply_size (e : HostEff) (u : St) (hk : e.k ≤ u.stack.size) :
    (e.apply u).stack.size = u.stack.size - e.k + e.top.size := by
  simp only [HostEff.apply, base, Array.size_append, Array.size_extract]; omega

theorem apply_lo (e : HostEff) (u : St) {i : Nat} (hi : i < u.stack.size - e.k) :
    (e.apply u).stack[i]? = u.stack[i]? := by
  simp only [HostEff.apply, base]
  rw [Array.getElem?_append_left (by simp only [Array.size_extract]; omega)]
  simp only [Array.getElem?_extract]
  rw [if_pos (show i < min (u.stack.size - e.k) u.stack.size - 0 by omega)]; simp

theorem apply_hi (e : HostEff) {u u' : St} (hsz : u.stack.size = u'.stack.size) (hk : e.k ≤ u.stack.size)
    {i : Nat} (hi : u.stack.size - e.k ≤ i) : (e.apply u).stack[i]? = (e.apply u').stack[i]? := by
  simp only [HostEff.apply, base]
  rw [Array.getElem?_append_right (by simp only [Array.size_extract]; omega),
    Array.getElem?_append_right (by simp only [Array.size_extract]; omega)]
  simp only [Array.size_extract, hsz]

/-- `fnOf` is injective on the checked functions when the function list has no duplicates. -/
theorem fnOf_inj {X : Ctx} (hnd : X.M.fns.Nodup) {k k' : Nat} (hk : k < X.nf) (hk' : k' < X.nf)
    (h : X.fnOf k = X.fnOf k') : k = k' := by
  unfold Ctx.fnOf at h; unfold Ctx.nf at hk hk'
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hk'] at h
  simp only [Option.getD_some] at h
  exact (List.Nodup.getElem_inj hnd).mp h

/-! ## 2. The twin post-state relation -/

/-- A consumed memory message at address `a`. -/
def Cov3 (cons : List Msg) (a : Nat) : Prop := ∃ z ∈ cons, z.space = 3 ∧ z.slot = a

theorem memView_slot {T : List Nat} {s : St} {tpm : Nat → Nat} {m : Msg} (hm : m.space = 3) :
    m ∈ memView T s tpm ↔ m.slot ∈ T ∧ m = encB m.slot (readByte s m.slot).toNat (tpm m.slot) := by
  rw [mem_memView]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨ha, rfl⟩
  · rintro ⟨ha, he⟩; exact ⟨_, ha, he⟩

theorem stackView_slot {stk : Array Val} {tps : Nat → Nat} {m : Msg} (hm : m.space = 0) :
    m ∈ stackView stk tps ↔ m.slot < stk.size ∧ m = enc 0 m.slot (stk[m.slot]?.getD default) (tps m.slot) := by
  rw [mem_stackView]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨hi, rfl⟩
  · rintro ⟨hi, he⟩; exact ⟨_, hi, he⟩

/-- A live message in a space other than `0` and `lsp` is an environment message. -/
theorem RelW.live_env {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) {m : Msg}
    (h0 : m.space ≠ 0) (hl : m.space ≠ E.lsp) : live m ↔ E.live m := by
  rw [R.live m]
  constructor
  · rintro (h | h | h)
    · obtain ⟨i, -, rfl⟩ := mem_stackView.mp h; exact absurd rfl h0
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; exact absurd rfl hl
    · exact h
  · intro h; exact Or.inr (Or.inr h)

/-- A live space-0 message is the stack view's. -/
theorem RelW.live_stk {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) {m : Msg}
    (h0 : m.space = 0) : live m ↔ m ∈ stackView s.stack tps := by
  rw [R.live m]
  constructor
  · rintro (h | h | h)
    · exact h
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [Env.lsp] at h0
    · exact absurd h0 (R.envSep m h).1
  · intro h; exact Or.inl h

/-- A live `lsp` message is the locals view's. -/
theorem RelW.live_loc {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) {m : Msg}
    (hl : m.space = E.lsp) : live m ↔ m ∈ localView E.lsp f.locals tpl := by
  rw [R.live m]
  constructor
  · rintro (h | h | h)
    · obtain ⟨i, -, rfl⟩ := mem_stackView.mp h; simp [Env.lsp] at hl; omega
    · exact h
    · exact absurd hl (R.envSep m h).2
  · intro h; exact Or.inr (Or.inl h)

/-- A live memory message is the only live message at its address. -/
theorem RelW.mem_unique {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) {y : Msg} (hy : live y)
    (hy3 : y.space = 3) {m : Msg} (hm3 : m.space = 3) (hs : m.slot = y.slot) : live m ↔ m = y := by
  have hne0 : ∀ z : Msg, z.space = 3 → z.space ≠ 0 := by intro z h; omega
  have hnel : ∀ z : Msg, z.space = 3 → z.space ≠ E.lsp := by intro z h; simp only [Env.lsp]; omega
  obtain ⟨T, tpm, -, -, -, hv⟩ := R.heap.mem
  have ey := (memView_slot hy3).mp ((hv y hy3).mp ((R.live_env (hne0 y hy3) (hnel y hy3)).mp hy))
  rw [R.live_env (hne0 m hm3) (hnel m hm3), hv m hm3, memView_slot hm3, hs]
  constructor
  · rintro ⟨-, he⟩; rw [he, ← ey.2]
  · rintro rfl; exact ey

theorem pagesOK_congr {s s' : St} (h : s'.pages = s.pages) (hs : PagesOK s) : PagesOK s' := by
  unfold PagesOK at hs ⊢; rw [h]; exact hs

/-- **`rel_twin_post` (COVER item 2).**  The honest post-state relation transfers to the twin
post-state, for the decomposition `x = eff.apply (setFrame {s with gas := G} {f with pc := f.pc + 1})`
the two-run lemma produces.  Premises: both pre-states related at the row (same code position, frame
base, stack size, page count), the row's consumed messages live in both, the message shape of a
HOST row (`hsp`, `hslot`, `hstk`, `hpair`), the out-STATE `cid` pin (`hcid`) and **write coverage**
`hwr` (the call changes no byte off the consumed addresses). -/
theorem rel_twin_post {X : Ctx} (hnd : X.M.fns.Nodup)
    {EH E : Env} {sH s : St} {fH f : Frame} {tpsH tps tplH tpl : Nat → Nat} {t pcH pc SH S : Nat}
    {liveH live : Msg → Prop} {aH bH a b : Nat}
    (RH : RelW X EH sH fH tpsH tplH t pcH SH liveH aH bH) (R : RelW X E s f tps tpl t pc S live a b)
    (ek : EH.k = E.k) (epc : pcH = pc) (esb : EH.sb = E.sb)
    (hsz : sH.stack.size = s.stack.size) (hpg : sH.pages.size = s.pages.size)
    {cons prod : List Msg} (hlH : ∀ y ∈ cons, liveH y) (hl : ∀ y ∈ cons, live y)
    (hsp : ∀ y ∈ cons ++ prod, y.space = 0 ∨ y.space = 3 ∨ y.space = 6 ∨ y.space = 7)
    {k : Nat} (hk : k ≤ s.stack.size)
    (hslot : ∀ y ∈ cons ++ prod, y.space = 0 → s.stack.size - k ≤ y.slot)
    (hstk : MsgCoverStk cons s.stack.size k)
    (hpair : ∀ y ∈ prod, y.space = 3 → Cov3 cons y.slot)
    (eff : HostEff) (hek : eff.k = k) (G : Gas)
    (hwr : ∀ a, ¬ Cov3 cons a →
      readByte (eff.apply (setFrame { s with gas := G } { f with pc := f.pc + 1 })) a = readByte s a)
    {k' pc' S' sb' cid' c d : Nat} (hcid : cid' = E.cid)
    (HR : Rel X (eff.apply (setFrame { sH with gas := G } { fH with pc := fH.pc + 1 })) (t + 1) k' pc' S' sb'
      cid' (stepLive liveH cons prod) c d) :
    Rel X (eff.apply (setFrame { s with gas := G } { f with pc := f.pc + 1 })) (t + 1) k' pc' S' sb' cid'
      (stepLive live cons prod) c d := by
  classical
  obtain ⟨E2, f2, tps2, tpl2, h2sb, h2cid, h2k, R2⟩ := HR
  -- the pre-call states
  obtain ⟨u1, u2, u3, u4, u5⟩ := setFrame_cons (s := { s with gas := G }) R.frames { f with pc := f.pc + 1 }
  obtain ⟨v1, v2, v3, v4, v5⟩ := setFrame_cons (s := { sH with gas := G }) RH.frames { fH with pc := fH.pc + 1 }
  generalize setFrame { s with gas := G } { f with pc := f.pc + 1 } = u at u1 u2 u3 u4 u5 hwr ⊢
  generalize setFrame { sH with gas := G } { fH with pc := fH.pc + 1 } = uH at v1 v2 v3 v4 v5 R2
  simp only at u2 u3 u4 u5 v2 v3 v4 v5
  -- the honest post frame
  have ex2 : (eff.apply uH).frames = f2 :: E2.rest := R2.frames
  have exH : (eff.apply uH).frames = { fH with pc := fH.pc + 1 } :: EH.rest := v1
  rw [exH] at ex2
  obtain ⟨ef2, er2⟩ := List.cons.inj ex2
  have hsb' : sb' = E.sb := by
    rw [← h2sb, ← R2.base, ← ef2]; show fH.base = E.sb; rw [RH.base, esb]
  have hk' : k' = E.k := by
    rw [← h2k]
    refine fnOf_inj hnd R2.kLt R.kLt ?_
    rw [← R2.fn, ← ef2, ← R.fn]; show fH.fn = f.fn
    rw [RH.fn, R.fn, ek]
  have hpc' : pc' = pc + 1 := by
    rw [← R2.pcEq, ← ef2]; show fH.pc + 1 = pc + 1; rw [RH.pcEq, epc]
  subst hsb' hk' hcid hpc'
  -- sizes and the stack
  have hkH : eff.k ≤ uH.stack.size := by rw [v2, hsz, hek]; exact hk
  have hku : eff.k ≤ u.stack.size := by rw [u2, hek]; exact hk
  have hxs : (eff.apply u).stack.size = s.stack.size - k + eff.top.size := by
    rw [apply_size eff u hku, u2, hek]
  have hxsH : (eff.apply uH).stack.size = s.stack.size - k + eff.top.size := by
    rw [apply_size eff uH hkH, v2, hsz, hek]
  have hlo : ∀ i, i < s.stack.size - k → (eff.apply u).stack[i]? = s.stack[i]? := by
    intro i hi; rw [apply_lo eff u (by rw [u2, hek]; exact hi), u2]
  have hhi : ∀ i, s.stack.size - k ≤ i → (eff.apply u).stack[i]? = (eff.apply uH).stack[i]? := by
    intro i hi; exact apply_hi eff (by rw [u2, v2, hsz]) hku (by rw [u2, hek]; exact hi)
  -- pages
  have hxp : (eff.apply u).pages = wbAll eff.writes s.pages := by
    show wbAll eff.writes u.pages = _; rw [u3]
  have hxpH : (eff.apply uH).pages = wbAll eff.writes sH.pages := by
    show wbAll eff.writes uH.pages = _; rw [v3]
  have hmb : memBytes (eff.apply u) = memBytes s := by
    simp only [memBytes, hxp, wbAll_size]
  have hmbH : memBytes (eff.apply uH) = memBytes s := by
    simp only [memBytes, hxpH, wbAll_size, hpg]
  -- the consumed messages pin the top `k` stack slots in both pre-states
  have stkEq : ∀ m : Msg, m.space = 0 → s.stack.size - k ≤ m.slot → (live m ↔ liveH m) := by
    intro m hm0 hms
    rw [R.live_stk hm0, RH.live_stk hm0, stackView_slot hm0, stackView_slot hm0, hsz]
    by_cases hlt : m.slot < s.stack.size
    · obtain ⟨y, hy, hy0, hys⟩ := hstk (m.slot - (s.stack.size - k)) (by omega)
      have hys' : y.slot = m.slot := by omega
      have e1 := (stackView_slot hy0).mp ((R.live_stk hy0).mp (hl y hy))
      have e2 := (stackView_slot hy0).mp ((RH.live_stk hy0).mp (hlH y hy))
      rw [hys'] at e1 e2
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans (e1.2.symm.trans e2.2)⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans (e2.2.symm.trans e1.2)⟩
    · constructor <;> (rintro ⟨h1, -⟩; omega)
  -- the consumed memory messages pin their bytes and messages in both pre-states
  have memEq : ∀ a, Cov3 cons a → readByte s a = readByte sH a ∧
      ∀ m : Msg, m.space = 3 → m.slot = a → (live m ↔ liveH m) := by
    rintro a ⟨y, hy, hy3, rfl⟩
    have m1 := R.byte_msg (hl y hy) hy3
    have m2 := RH.byte_msg (hlH y hy) hy3
    refine ⟨UInt8.toNat_inj.mp (m1.trans m2.symm), fun m hm3 hms => ?_⟩
    rw [R.mem_unique (hl y hy) hy3 hm3 hms, RH.mem_unique (hlH y hy) hy3 hm3 hms]
  have byteEq : ∀ a, Cov3 cons a → readByte (eff.apply u) a = readByte (eff.apply uH) a := by
    intro a ha
    have hA : Agree (fun b => b = a) s sH :=
      ⟨R.heap.pages, RH.heap.pages, hpg.symm, fun b hb => by rw [hb]; exact (memEq a ha).1⟩
    have h := (agree_wbAll eff.writes s sH hA).b a rfl
    rw [readByte_congr (s := { s with pages := wbAll eff.writes s.pages }) hxp,
      readByte_congr (s := { sH with pages := wbAll eff.writes sH.pages }) hxpH]; exact h
  -- messages outside the call's traffic
  have notIn : ∀ m : Msg, m.space ≠ 0 → m.space ≠ 3 → m.space ≠ 6 → m.space ≠ 7 →
      (stepLive live cons prod m ↔ live m) := by
    intro m h0 h3 h6 h7
    have hc : m ∉ cons := fun h => by
      rcases hsp m (List.mem_append_left _ h) with e | e | e | e <;> simp_all
    have hp : m ∉ prod := fun h => by
      rcases hsp m (List.mem_append_right _ h) with e | e | e | e <;> simp_all
    simp only [stepLive, hc, hp, not_false_eq_true, and_true, or_false]
  -- the new environment
  let E' : Env := { sb := E.sb, cid := E.cid, rest := E.rest, k := E.k,
                    live := fun m => stepLive live cons prod m ∧ m.space ≠ 0 ∧ m.space ≠ 16 + E.cid }
  let tps' : Nat → Nat := fun i => if i < s.stack.size - k then tps i else tps2 i
  -- space 0 of the twin post
  have stk0 : ∀ m : Msg, m.space = 0 →
      (stepLive live cons prod m ↔ m ∈ stackView (eff.apply u).stack tps') := by
    intro m hm0
    rw [stackView_slot hm0, hxs]
    by_cases hlt : m.slot < s.stack.size - k
    · have hc : m ∉ cons := fun h => by have := hslot m (List.mem_append_left _ h) hm0; omega
      have hp : m ∉ prod := fun h => by have := hslot m (List.mem_append_right _ h) hm0; omega
      simp only [stepLive, hc, hp, not_false_eq_true, and_true, or_false]
      rw [R.live_stk hm0, stackView_slot hm0, hlo m.slot hlt]
      simp only [tps', if_pos hlt]
      constructor
      · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
      · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
    · have e : stepLive live cons prod m ↔ stepLive liveH cons prod m := by
        simp only [stepLive, stkEq m hm0 (by omega)]
      rw [e, R2.live_stk hm0, stackView_slot hm0, hxsH, hhi m.slot (by omega)]
      simp only [tps', if_neg hlt]
  -- the heap of the twin post
  obtain ⟨T, tpm, hTnd, hTlt, hTtp, hTv⟩ := R.heap.mem
  obtain ⟨T2, tpm2, hT2nd, hT2lt, hT2tp, hT2v⟩ := R2.heap.mem
  let T' : List Nat := T.filter (fun a => decide (¬ Cov3 cons a)) ++ T2.filter (fun a => decide (Cov3 cons a))
  let tpm' : Nat → Nat := fun a => if Cov3 cons a then tpm2 a else tpm a
  have memT' : ∀ a, a ∈ T' ↔ (¬ Cov3 cons a ∧ a ∈ T) ∨ (Cov3 cons a ∧ a ∈ T2) := by
    intro a
    simp only [T', List.mem_append, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨h2, h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨h2, h1⟩
  have heap3 : ∀ m : Msg, m.space = 3 → (stepLive live cons prod m ↔ m ∈ memView T' (eff.apply u) tpm') := by
    intro m hm3
    have h0 : m.space ≠ 0 := by omega
    have hl3 : m.space ≠ E.lsp := by simp only [Env.lsp]; omega
    rw [memView_slot hm3, memT']
    by_cases hc : Cov3 cons m.slot
    · have e : stepLive live cons prod m ↔ stepLive liveH cons prod m := by
        simp only [stepLive, (memEq m.slot hc).2 m hm3 rfl]
      have hl2 : m.space ≠ E2.lsp := by simp only [Env.lsp]; omega
      rw [e, R2.live_env h0 hl2, hT2v m hm3, memView_slot hm3, byteEq m.slot hc]
      simp only [tpm', if_pos hc, hc, not_true_eq_false, false_and, true_and, false_or]
    · have hcm : m ∉ cons := fun h => hc ⟨m, h, hm3, rfl⟩
      have hpm : m ∉ prod := fun h => hc (hpair m h hm3)
      simp only [stepLive, hcm, hpm, not_false_eq_true, and_true, or_false]
      rw [R.live_env h0 hl3, hTv m hm3, memView_slot hm3, hwr m.slot hc]
      simp only [tpm', if_neg hc, hc, not_false_eq_true, true_and, false_and, or_false]
  -- the twin post relation
  refine ⟨E', { f with pc := f.pc + 1 }, tps', tpl, rfl, rfl, rfl, ?_⟩
  have hfr : (eff.apply u).frames = { f with pc := f.pc + 1 } :: E.rest := u1
  refine
    { frames := hfr
      kLt := R.kLt
      fn := R.fn
      pcEq := by show f.pc + 1 = pc + 1; rw [R.pcEq]
      pcLt := by have := R2.pcLt; rw [h2k] at this; exact this
      labels := ?_
      base := R.base
      sbLe := by have := R2.sbLe; rw [hxsH, h2sb] at this; rw [hxs]; exact this
      height := by have := R2.height; rw [hxsH, h2sb, h2k] at this; rw [hxs]; exact this
      nloc := R.nloc
      gas := R2.gas
      segLt := R2.segLt
      segbLt := R2.segbLt
      numS := ?_
      numL := R.numL
      tpsLt := ?_
      tplLt := fun j hj => by have := R.tplLt j hj; omega
      envSep := fun m hm => ⟨hm.2.1, hm.2.2⟩
      entry := R.entry
      sbLt := R.sbLt
      cidLt := R.cidLt
      heap := ?_
      calls := ?_
      live := ?_ }
  · obtain ⟨ls2, hls2, hf2⟩ := R2.labels
    obtain ⟨ls0, hls0, hf0⟩ := R.labels
    obtain ⟨ls1, hls1, hf1⟩ := RH.labels
    refine ⟨ls2, by rw [h2k] at hls2; exact hls2, ?_⟩
    have e1 : ls1 = ls0 := by rw [ek, epc] at hls1; rw [hls1] at hls0; exact Option.some.inj hls0
    show f.labels = shiftLabels E.sb ls2
    rw [hf0, ← e1, ← esb, ← hf1]
    have := congrArg Frame.labels ef2
    simp only at this
    rw [this, hf2, h2sb, esb]
  · intro i hi
    by_cases hlt : i < s.stack.size - k
    · rw [hlo i hlt]; exact R.numS i (by omega)
    · rw [hhi i (by omega)]; exact R2.numS i (by rw [hxsH]; rw [hxs] at hi; exact hi)
  · intro i hi
    by_cases hlt : i < s.stack.size - k
    · simp only [tps', if_pos hlt]; have := R.tpsLt i (by omega); omega
    · simp only [tps', if_neg hlt]; exact R2.tpsLt i (by rw [hxsH]; rw [hxs] at hi; exact hi)
  · refine ⟨pagesOK_congr (s := { s with pages := wbAll eff.writes s.pages }) hxp ?_, ⟨T', tpm', ?_, ?_, ?_, fun m hm3 => ?_⟩, ?_⟩
    · have hA : Agree (fun _ => False) s sH := ⟨R.heap.pages, RH.heap.pages, hpg.symm, fun _ h => h.elim⟩
      exact pagesOK_congr rfl (agree_wbAll eff.writes s sH hA).pok
    · simp only [T']
      refine List.nodup_append.mpr ⟨hTnd.filter _, hT2nd.filter _, ?_⟩
      intro a ha b hb hab
      subst hab
      simp only [List.mem_filter, decide_eq_true_eq] at ha hb
      exact ha.2 hb.2
    · intro a ha
      rcases (memT' a).mp ha with ⟨-, h⟩ | ⟨-, h⟩
      · rw [hmb]; exact hTlt a h
      · have := hT2lt a h; rw [hmbH] at this; rw [hmb]; exact this
    · intro a ha
      simp only [tpm']
      rcases (memT' a).mp ha with ⟨hc, h⟩ | ⟨hc, h⟩
      · rw [if_neg hc]; have := hTtp a h; omega
      · rw [if_pos hc]; exact hT2tp a h
    · show (stepLive live cons prod m ∧ m.space ≠ 0 ∧ m.space ≠ 16 + E.cid) ↔ _
      rw [← heap3 m hm3]
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, by omega, by omega⟩
    · obtain ⟨tpg, hg, hgv⟩ := R.heap.glob
      have hgl : (eff.apply u).globals = s.globals := u4
      refine ⟨tpg, fun g hg' => ?_, fun m hm2 => ?_⟩
      · rw [hgl] at hg' ⊢
        have := hg g hg'; exact ⟨by omega, this.2⟩
      · show (stepLive live cons prod m ∧ m.space ≠ 0 ∧ m.space ≠ 16 + E.cid) ↔ _
        rw [notIn m (by omega) (by omega) (by omega) (by omega),
          R.live_env (by omega) (by simp only [Env.lsp]; omega), hgv m hm2, hgl]
        constructor
        · exact fun h => h.1
        · intro h; exact ⟨h, by omega, by omega⟩
  · refine R.calls.mono (by omega) rfl rfl rfl rfl (fun m hm => ?_) u5
    show (stepLive live cons prod m ∧ m.space ≠ 0 ∧ m.space ≠ 16 + E.cid) ↔ E.live m
    by_cases hlsp : m.space = 16 + E.cid
    · constructor
      · exact fun h => absurd hlsp h.2.2
      · intro h; exact absurd hlsp (R.envSep m h).2
    · have h0 : m.space ≠ 0 := by omega
      rw [notIn m h0 (by omega) (by omega) (by omega), R.live_env h0 hlsp]
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, h0, hlsp⟩
  · intro m
    show stepLive live cons prod m ↔ m ∈ stackView (eff.apply u).stack tps' ∨
      m ∈ localView (16 + E.cid) f.locals tpl ∨ (stepLive live cons prod m ∧ m.space ≠ 0 ∧ m.space ≠ 16 + E.cid)
    by_cases h0 : m.space = 0
    · rw [stk0 m h0]
      constructor
      · exact fun h => Or.inl h
      · rintro (h | h | h)
        · exact h
        · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp at h0
        · exact absurd h0 h.2.1
    · by_cases hlsp : m.space = 16 + E.cid
      · rw [notIn m h0 (by omega) (by omega) (by omega), R.live_loc hlsp]
        constructor
        · exact fun h => Or.inr (Or.inl h)
        · rintro (h | h | h)
          · obtain ⟨i, -, rfl⟩ := mem_stackView.mp h; simp at h0
          · exact h
          · exact absurd hlsp h.2.2
      · constructor
        · intro h; exact Or.inr (Or.inr ⟨h, h0, hlsp⟩)
        · rintro (h | h | h)
          · obtain ⟨i, -, rfl⟩ := mem_stackView.mp h; simp at h0
          · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp at hlsp
          · exact h.1

#print axioms rel_twin_post

end WasmBase
