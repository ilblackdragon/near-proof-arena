import NpaiIR.Lib.Word

/-!
# NpaiIR.WP — verification-condition generation

* `wp st m Q`: every normal exit of `st` from `m` satisfies `Q` (partial
  correctness, used for **soundness**);
* `twp st m Q`: `st` exits normally from `m` in a state `m'` with cost `c` and
  `Q m' c` (total correctness, used for **completeness** and fuel bounds).

The simp lemmas below unfold both through `seq`, `ite` and single
instructions, so `simp` turns a program fragment into its verification
conditions. Loops are handled by the invariant rules `wp_loop`, `twp_loop`,
`wp_forUp`, `twp_forUp`, and macros by their own lemmas.
-/

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

def wp (p : Program) (inp : Inputs) (st : Stmt) (m : M) (Q : M → Prop) : Prop :=
  ∀ m' c, Ev p inp st m (.ok m') c → Q m'

def twp (p : Program) (inp : Inputs) (st : Stmt) (m : M) (Q : M → Nat → Prop) : Prop :=
  ∃ m' c, Ev p inp st m (.ok m') c ∧ Q m' c

theorem wp_apply {st : Stmt} {m m' : M} {c : Nat} {Q : M → Prop} (h : wp p inp st m Q)
    (e : Ev p inp st m (.ok m') c) : Q m' := h m' c e

theorem wp_mono {st : Stmt} {m : M} {Q Q' : M → Prop} (h : wp p inp st m Q) (hq : ∀ m, Q m → Q' m) :
    wp p inp st m Q' := fun m' c e => hq _ (h m' c e)

theorem twp_mono {st : Stmt} {m : M} {Q Q' : M → Nat → Prop} (h : twp p inp st m Q)
    (hq : ∀ m c, Q m c → Q' m c) : twp p inp st m Q' := by
  obtain ⟨m', c, e, hq'⟩ := h; exact ⟨m', c, e, hq _ _ hq'⟩

/-! ## Structural rules -/

@[simp] theorem wp_seq {a b : Stmt} {m : M} {Q : M → Prop} :
    wp p inp (.seq a b) m Q ↔ wp p inp a m (fun m1 => wp p inp b m1 Q) := by
  constructor
  · intro h m1 c1 e1 m2 c2 e2; exact h m2 _ (.seqOk e1 e2)
  · intro h m2 c e
    rw [ev_seq_ok] at e
    obtain ⟨m1, c1, c2, e1, e2, rfl⟩ := e
    exact h m1 c1 e1 m2 c2 e2

@[simp] theorem wp_op {i : Instr} {m : M} {Q : M → Prop} :
    wp p inp (.op i) m Q ↔ (okInstr i = true → ∀ m', ins p inp m i = some m' → Q m') := by
  constructor
  · intro h hi m' e; exact h m' _ (.op hi e)
  · intro h m' c e
    rw [ev_op_ok] at e
    exact h e.1 m' e.2.1

@[simp] theorem wp_ite {x : Nat} {t e : Stmt} {m : M} {Q : M → Prop} :
    wp p inp (.ite x t e) m Q ↔ (m.regs x = 0 → wp p inp e m Q) ∧ (m.regs x ≠ 0 → wp p inp t m Q) := by
  constructor
  · intro h
    exact ⟨fun hx m' c ev => h m' _ (.iteF hx ev), fun hx m' c ev => h m' _ (.iteTOk hx ev)⟩
  · rintro ⟨h1, h2⟩ m' c ev
    rcases ev_ite_ok.mp ev with ⟨hx, c', ev', -⟩ | ⟨hx, c', ev', -⟩
    · exact h2 hx m' c' ev'
    · exact h1 hx m' c' ev'

@[simp] theorem twp_seq {a b : Stmt} {m : M} {Q : M → Nat → Prop} :
    twp p inp (.seq a b) m Q ↔ twp p inp a m (fun m1 c1 => twp p inp b m1 (fun m2 c2 => Q m2 (c1 + c2))) := by
  constructor
  · rintro ⟨m2, c, e, hq⟩
    rw [ev_seq_ok] at e
    obtain ⟨m1, c1, c2, e1, e2, rfl⟩ := e
    exact ⟨m1, c1, e1, m2, c2, e2, hq⟩
  · rintro ⟨m1, c1, e1, m2, c2, e2, hq⟩
    exact ⟨m2, _, .seqOk e1 e2, hq⟩

@[simp] theorem twp_op {i : Instr} {m : M} {Q : M → Nat → Prop} :
    twp p inp (.op i) m Q ↔ (okInstr i = true ∧ ∃ m', ins p inp m i = some m' ∧ Q m' (cost m.regs i)) := by
  constructor
  · rintro ⟨m', c, e, hq⟩
    rw [ev_op_ok] at e
    obtain ⟨hi, e, rfl⟩ := e
    exact ⟨hi, m', e, hq⟩
  · rintro ⟨hi, m', e, hq⟩
    exact ⟨m', _, .op hi e, hq⟩

@[simp] theorem twp_ite {x : Nat} {t e : Stmt} {m : M} {Q : M → Nat → Prop} :
    twp p inp (.ite x t e) m Q ↔
      (m.regs x = 0 ∧ twp p inp e m (fun m' c => Q m' (c + 1))) ∨
      (m.regs x ≠ 0 ∧ twp p inp t m (fun m' c => Q m' (c + 2))) := by
  constructor
  · rintro ⟨m', c, ev, hq⟩
    rcases ev_ite_ok.mp ev with ⟨hx, c', ev', rfl⟩ | ⟨hx, c', ev', rfl⟩
    · exact .inr ⟨hx, m', c', ev', hq⟩
    · exact .inl ⟨hx, m', c', ev', hq⟩
  · rintro (⟨hx, m', c', ev', hq⟩ | ⟨hx, m', c', ev', hq⟩)
    · exact ⟨m', _, .iteF hx ev', hq⟩
    · exact ⟨m', _, .iteTOk hx ev', hq⟩

/-- If-then-else with a known condition (completeness, the `else` branch). -/
theorem twp_ite_zero {x : Nat} {t e : Stmt} {m : M} {Q : M → Nat → Prop} (hx : m.regs x = 0)
    (h : twp p inp e m (fun m' c => Q m' (c + 1))) : twp p inp (.ite x t e) m Q :=
  twp_ite.mpr (.inl ⟨hx, h⟩)

theorem twp_ite_ne {x : Nat} {t e : Stmt} {m : M} {Q : M → Nat → Prop} (hx : m.regs x ≠ 0)
    (h : twp p inp t m (fun m' c => Q m' (c + 2))) : twp p inp (.ite x t e) m Q :=
  twp_ite.mpr (.inr ⟨hx, h⟩)

/-! ## Loops -/

theorem wp_loop {x : Nat} {b : Stmt} {m : M} {Q : M → Prop} (I : M → Prop) (h0 : I m)
    (hb : ∀ m, I m → m.regs x ≠ 0 → wp p inp b m I) (hq : ∀ m, I m → m.regs x = 0 → Q m) :
    wp p inp (.loop x b) m Q := by
  intro m' c e
  obtain ⟨hi, hz⟩ := loop_sound I (fun m m' c hi hx e => hb m hi hx m' c e) e h0
  exact hq m' hi hz

theorem twp_loop {x : Nat} {b : Stmt} {m : M} {Q : M → Nat → Prop} (I : M → Prop) (Pot : M → Nat)
    (h0 : I m)
    (hb : ∀ m, I m → m.regs x ≠ 0 → twp p inp b m (fun m' c => I m' ∧ c + 2 + Pot m' ≤ Pot m))
    (hq : ∀ m' c, I m' → m'.regs x = 0 → c + Pot m' ≤ Pot m + 1 → Q m' c) :
    twp p inp (.loop x b) m Q := by
  obtain ⟨m', c, e, hi, hz, hc⟩ := loop_complete I Pot (fun m hi hx => by
    obtain ⟨m', c, e, hi', hc⟩ := hb m hi hx; exact ⟨m', c, e, hi', hc⟩) m h0
  exact ⟨m', c, e, hq m' c hi hz hc⟩

/-! ## Blocks and loop-free code -/

theorem wp_of_exe {st : Stmt} {m m1 : M} {c1 : Nat} {Q : M → Prop} (h : exe p inp st m = some (m1, c1))
    (hq : Q m1) : wp p inp st m Q := by
  intro m' c e
  obtain ⟨e1, -⟩ := Ev.det e (exe_sound h)
  cases e1; exact hq

theorem twp_of_exe {st : Stmt} {m m1 : M} {c1 : Nat} {Q : M → Nat → Prop}
    (h : exe p inp st m = some (m1, c1)) (hq : Q m1 c1) : twp p inp st m Q :=
  ⟨m1, c1, exe_sound h, hq⟩

/-- Macro rule (soundness) from an `exe` equation. -/
theorem wp_exe_iff {st : Stmt} {m m1 : M} {c1 : Nat} {Q : M → Prop} (h : exe p inp st m = some (m1, c1)) :
    wp p inp st m Q ↔ Q m1 :=
  ⟨fun hw => hw m1 c1 (exe_sound h), wp_of_exe h⟩

theorem twp_exe_iff {st : Stmt} {m m1 : M} {c1 : Nat} {Q : M → Nat → Prop}
    (h : exe p inp st m = some (m1, c1)) : twp p inp st m Q ↔ Q m1 c1 := by
  constructor
  · rintro ⟨m', c, e, hq⟩
    obtain ⟨e1, rfl⟩ := Ev.det e (exe_sound h)
    cases e1; exact hq
  · exact twp_of_exe h

end NpaiIR

namespace NpaiIR

open ArenaCore Interp

variable {p : Program} {inp : Inputs}

/-! ## Base macros -/

theorem exe_nop (m : M) : exe p inp nop m = some (m, 1) := by
  have := mov00 (p := p) (inp := inp) m
  simp only [nop, exe, okInstr, ↓reduceIte, this, Option.map_some]
  rfl

@[simp] theorem wp_nop {m : M} {Q : M → Prop} : wp p inp nop m Q ↔ Q m := wp_exe_iff (exe_nop m)

@[simp] theorem twp_nop {m : M} {Q : M → Nat → Prop} : twp p inp nop m Q ↔ Q m 1 := twp_exe_iff (exe_nop m)

theorem wp_fail (hp : p.memSize ≤ 4294967295) {m : M} {Q : M → Prop} : wp p inp fail m Q :=
  fun _ _ e => absurd e (fail_no_ok hp)

theorem twp_fail (hp : p.memSize ≤ 4294967295) {m : M} {Q : M → Nat → Prop} : ¬ twp p inp fail m Q :=
  fun ⟨_, _, e, _⟩ => fail_no_ok hp e

theorem wp_ld32 {d a : Nat} (hda : d ≠ a) (hd : d ≠ 12) (ha : a ≠ 12) (hd14 : d ≠ 14) {m : M}
    (hk : m.regs 14 = 8) (hb : m.regs a + 4 ≤ p.memSize) (hw : p.memSize < 4294967296) {Q : M → Prop} :
    wp p inp (ld32 d a) m Q ↔ Q ⟨setReg (setReg m.regs 12 (m.mem (m.regs a)).toNat) d
      (Bytes.leToNat (readMem m.mem (m.regs a) 4)), m.mem⟩ :=
  wp_exe_iff (ld32_exe hda hd ha hd14 hk hb hw)

theorem twp_ld32 {d a : Nat} (hda : d ≠ a) (hd : d ≠ 12) (ha : a ≠ 12) (hd14 : d ≠ 14) {m : M}
    (hk : m.regs 14 = 8) (hb : m.regs a + 4 ≤ p.memSize) (hw : p.memSize < 4294967296)
    {Q : M → Nat → Prop} :
    twp p inp (ld32 d a) m Q ↔ Q ⟨setReg (setReg m.regs 12 (m.mem (m.regs a)).toNat) d
      (Bytes.leToNat (readMem m.mem (m.regs a) 4)), m.mem⟩ 14 :=
  twp_exe_iff (ld32_exe hda hd ha hd14 hk hb hw)

theorem wp_ld16 {d a : Nat} (hda : d ≠ a) (hd : d ≠ 12) (ha : a ≠ 12) (hd14 : d ≠ 14) {m : M}
    (hk : m.regs 14 = 8) (hb : m.regs a + 2 ≤ p.memSize) (hw : p.memSize < 4294967296) {Q : M → Prop} :
    wp p inp (ld16 d a) m Q ↔ Q ⟨setReg (setReg m.regs 12 (m.mem (m.regs a)).toNat) d
      (Bytes.leToNat (readMem m.mem (m.regs a) 2)), m.mem⟩ :=
  wp_exe_iff (ld16_exe hda hd ha hd14 hk hb hw)

theorem twp_ld16 {d a : Nat} (hda : d ≠ a) (hd : d ≠ 12) (ha : a ≠ 12) (hd14 : d ≠ 14) {m : M}
    (hk : m.regs 14 = 8) (hb : m.regs a + 2 ≤ p.memSize) (hw : p.memSize < 4294967296)
    {Q : M → Nat → Prop} :
    twp p inp (ld16 d a) m Q ↔ Q ⟨setReg (setReg m.regs 12 (m.mem (m.regs a)).toNat) d
      (Bytes.leToNat (readMem m.mem (m.regs a) 2)), m.mem⟩ 6 :=
  twp_exe_iff (ld16_exe hda hd ha hd14 hk hb hw)

theorem wp_ld64 {d a : Nat} (hda : d ≠ a) (hd : d ≠ 12) (ha : a ≠ 12) (hd14 : d ≠ 14) {m : M}
    (hk : m.regs 14 = 8) (hb : m.regs a + 8 ≤ p.memSize) (hw : p.memSize < 4294967296) {Q : M → Prop} :
    wp p inp (ld64 d a) m Q ↔ Q ⟨setReg (setReg m.regs 12 (m.mem (m.regs a)).toNat) d
      (Bytes.leToNat (readMem m.mem (m.regs a) 8)), m.mem⟩ :=
  wp_exe_iff (ld64_exe hda hd ha hd14 hk hb hw)

theorem twp_ld64 {d a : Nat} (hda : d ≠ a) (hd : d ≠ 12) (ha : a ≠ 12) (hd14 : d ≠ 14) {m : M}
    (hk : m.regs 14 = 8) (hb : m.regs a + 8 ≤ p.memSize) (hw : p.memSize < 4294967296)
    {Q : M → Nat → Prop} :
    twp p inp (ld64 d a) m Q ↔ Q ⟨setReg (setReg m.regs 12 (m.mem (m.regs a)).toNat) d
      (Bytes.leToNat (readMem m.mem (m.regs a) 8)), m.mem⟩ 30 :=
  twp_exe_iff (ld64_exe hda hd ha hd14 hk hb hw)

theorem wp_st32 {a v : Nat} (ha : a ≠ 12) (ha13 : a ≠ 13) {m : M} (hk : m.regs 14 = 8)
    (hb : m.regs a + 4 ≤ p.memSize) (hw : p.memSize < 4294967296) (hv : m.regs v < 18446744073709551616)
    {Q : M → Prop} :
    wp p inp (st32 a v) m Q ↔ Q ⟨setReg (setReg m.regs 12 (m.regs v / 256 / 256 / 256)) 13
      (m.regs a + 3), writeMem m.mem (m.regs a) 4 (Bytes.leN 4 (m.regs v))⟩ :=
  wp_exe_iff (st32_exe ha ha13 hk hb hw hv)

theorem twp_st32 {a v : Nat} (ha : a ≠ 12) (ha13 : a ≠ 13) {m : M} (hk : m.regs 14 = 8)
    (hb : m.regs a + 4 ≤ p.memSize) (hw : p.memSize < 4294967296) (hv : m.regs v < 18446744073709551616)
    {Q : M → Nat → Prop} :
    twp p inp (st32 a v) m Q ↔ Q ⟨setReg (setReg m.regs 12 (m.regs v / 256 / 256 / 256)) 13
      (m.regs a + 3), writeMem m.mem (m.regs a) 4 (Bytes.leN 4 (m.regs v))⟩ 11 :=
  twp_exe_iff (st32_exe ha ha13 hk hb hw hv)

end NpaiIR

namespace NpaiIR
open ArenaCore Interp
variable {p : Program} {inp : Inputs}

theorem twp_fail_iff (hp : p.memSize ≤ 4294967295) {m : M} {Q : M → Nat → Prop} :
    twp p inp fail m Q ↔ False := ⟨twp_fail hp, False.elim⟩

theorem wp_fail_iff (hp : p.memSize ≤ 4294967295) {m : M} {Q : M → Prop} :
    wp p inp fail m Q ↔ True := ⟨fun _ => trivial, fun _ => wp_fail hp⟩

end NpaiIR

namespace NpaiIR
open ArenaCore Interp
variable {p : Program} {inp : Inputs}

/-! ## Counted loops -/

theorem wp_forUp {i n t : Nat} {body : Stmt} (hit : i ≠ t) (hnt : n ≠ t) (hin : i ≠ n) {m : M}
    {Q : M → Prop} (J : Nat → M → Prop) (N : Nat) (hN : N < 18446744073709551616)
    (hJ : ∀ j m v w, J j m → J j { m with regs := setReg (setReg m.regs i v) t w })
    (h0 : J 0 m) (hi0 : m.regs i = 0) (hn0 : m.regs n = N)
    (hbody : ∀ j m, j < N → J j m → m.regs i = j → m.regs n = N →
      wp p inp body m (fun m' => J (j + 1) m' ∧ m'.regs i = j ∧ m'.regs n = N))
    (hq : ∀ m, J N m → m.regs n = N → Q m) : wp p inp (forUp i n t body) m Q := by
  intro m' c e
  obtain ⟨h1, h2⟩ := forUp_sound hit hnt hin J N hN hJ
    (fun j m m' c hj hJ hi hn e => hbody j m hj hJ hi hn m' c e) e h0 hi0 hn0
  exact hq m' h1 h2

theorem twp_forUp {i n t : Nat} {body : Stmt} (hit : i ≠ t) (hnt : n ≠ t) (hin : i ≠ n) {m : M}
    {Q : M → Nat → Prop} (J : Nat → M → Prop) (N B : Nat) (hN : N < 18446744073709551616)
    (hJ : ∀ j m v w, J j m → J j { m with regs := setReg (setReg m.regs i v) t w })
    (h0 : J 0 m) (hi0 : m.regs i = 0) (hn0 : m.regs n = N)
    (hbody : ∀ j m, j < N → J j m → m.regs i = j → m.regs n = N →
      twp p inp body m (fun m' c => J (j + 1) m' ∧ m'.regs i = j ∧ m'.regs n = N ∧ c ≤ B))
    (hq : ∀ m c, J N m → m.regs n = N → c ≤ N * (B + 4) + 2 → Q m c) :
    twp p inp (forUp i n t body) m Q := by
  obtain ⟨m', c, e, h1, h2, h3⟩ := forUp_complete hit hnt hin J N B hN hJ
    (fun j m hj hJ hi hn => by
      obtain ⟨m', c, e, hq⟩ := hbody j m hj hJ hi hn
      exact ⟨m', c, e, hq⟩) m h0 hi0 hn0
  exact ⟨m', c, e, hq m' c h1 h2 h3⟩

/-- Down-counting loop `while k ≠ 0 do body` (body decrements `k`). -/
theorem wp_loopDown {k : Nat} {body : Stmt} {m : M} {Q : M → Prop} (J : Nat → M → Prop) (n : Nat)
    (h0 : J n m) (hk : m.regs k = n)
    (hbody : ∀ j m, 0 < j → J j m → m.regs k = j → wp p inp body m (fun m' => J (j - 1) m' ∧ m'.regs k = j - 1))
    (hq : ∀ m, J 0 m → Q m) : wp p inp (.loop k body) m Q := by
  intro m' c e
  exact hq m' (loopDown_sound J (fun j m m' c hj hJ hk e => hbody j m hj hJ hk m' c e) e h0 hk)

theorem twp_loopDown {k : Nat} {body : Stmt} {m : M} {Q : M → Nat → Prop} (J : Nat → M → Prop) (n B : Nat)
    (h0 : J n m) (hk : m.regs k = n)
    (hbody : ∀ j m, 0 < j → J j m → m.regs k = j →
      twp p inp body m (fun m' c => J (j - 1) m' ∧ m'.regs k = j - 1 ∧ c ≤ B))
    (hq : ∀ m c, J 0 m → m.regs k = 0 → c ≤ n * (B + 2) + 1 → Q m c) : twp p inp (.loop k body) m Q := by
  obtain ⟨m', c, e, h1, h2, h3⟩ := loopDown_complete J B (fun j m hj hJ hk => by
    obtain ⟨m', c, e, hq⟩ := hbody j m hj hJ hk
    exact ⟨m', c, e, hq⟩) n m h0 hk
  exact ⟨m', c, e, hq m' c h1 h2 h3⟩

/-- Rule for a total macro given by a spec `∃ m' c, Ev … ∧ R m' c`: soundness by determinism. -/
theorem wp_of_spec {st : Stmt} {m : M} {R : M → Nat → Prop} {Q : M → Prop}
    (h : ∃ m' c, Ev p inp st m (.ok m') c ∧ R m' c) (hq : ∀ m' c, R m' c → Q m') : wp p inp st m Q := by
  intro m2 c2 e
  obtain ⟨m', c, e', hr⟩ := h
  obtain ⟨e1, rfl⟩ := Ev.det e' e
  cases e1; exact hq _ _ hr

theorem twp_of_spec {st : Stmt} {m : M} {R : M → Nat → Prop} {Q : M → Nat → Prop}
    (h : ∃ m' c, Ev p inp st m (.ok m') c ∧ R m' c) (hq : ∀ m' c, R m' c → Q m' c) : twp p inp st m Q := by
  obtain ⟨m', c, e, hr⟩ := h
  exact ⟨m', c, e, hq _ _ hr⟩

end NpaiIR
