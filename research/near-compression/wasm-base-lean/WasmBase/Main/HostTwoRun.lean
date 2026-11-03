import WasmBase.Main.HostArms
import WasmBase.Main.SegSigma
import WasmBase.Mem

/-!
# WasmBase.Main.HostTwoRun — the two-run (relational) footprint framework for host programs (E2E M6.1)

`Main/HostFoot.lean` proves *unary* facts about host programs (`Inv I V m`: an invariant of one run).
Here is the *binary* analogue: **two runs of the same host program from two states that agree on
what the program reads end in corresponding results.**

## The relation `Tw s0 s0' k`

Fix two start states `s0`, `s0'` and a stack depth `k` (the shared top of the operand stack).  A pair
of states `(x, x')` is **twinned** (`Tw s0 s0' k x x'`) when

* their host parts agree: `hostR x = hostR x'` (`hostR`: every field except stack, frames, pages,
  globals, table, tableMax, elems, datas, stackRem; **registers and the whole gas record included**);
* their Wasm-visible parts are the start states' changed by **one common effect** (`VisAt`): the top
  `k` entries of the operand stack replaced by a common `top`, a common list of byte writes `W`
  applied to the pages (`wbAll W`), everything else (frames, globals, table, segments, stack budget)
  untouched.

The start pair satisfies `Low A k s0 s0'` (equal host parts, equal top-`k` stack entries, equal page
count, well-sized pages, equal bytes on the address set `A`): everything else (the stack below the
top `k`, the caller frames, globals, static fields, the bytes outside `A`) is free.

## Relational specs `Rel2 T V m m'`

`Rel2 T V m m'`: from any `T`-related pair, `m` and `m'` both succeed with **equal** values (satisfying
`V`) and `T`-related states, or both fail with **equal** messages and `T`-related states.  Two programs
because after `get` the continuations capture *different* states (`rel_get_bind`).  Rules: `pure`,
`bind`, `get`-`bind`, `set`, `modify`, `throw`, `if`, `dite`, `for` over lists/ranges, `<$>`; the
primitives (`withGas` and the gas ops, `readMemH` **with its read-set side condition**, `writeMemH`,
`regGetH`, `regSetH`, `pushRet`) are proved in §6–7 below; `rel_auto` (§5) walks two copies of a program in
lock step, aligning host reads of the captured states (`tw_host`, `relAlign`) and leaving the read-set
side goals of `readMemH`.
-/

namespace WasmBase
namespace TwoRun
open NearSpecV3.Wasm
open HostFoot
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. The host part and the visible effect -/

/-- **The host part of a state**: `hostSide` (`Main/HostFoot.lean`) with the register file kept. -/
def hostR (s : St) : St := { hostSide s with registers := s.registers }

/-- The pages after a list of writes (in order); `wbPages` is `writeBytes` on the pages. -/
def wbAll (W : List (Nat × ByteArray)) (p : Array ByteArray) : Array ByteArray :=
  W.foldl (fun p w => wbPages p w.1 w.2) p

/-- The operand stack below the top `k` entries. -/
def base (k : Nat) (s : St) : Array Val := s.stack.extract 0 (s.stack.size - k)
/-- The top `k` entries of the operand stack. -/
def topK (k : Nat) (s : St) : Array Val := s.stack.extract (s.stack.size - k) s.stack.size

/-- `x`'s Wasm-visible part (registers excepted) is `s0`'s after the effect `(top, W)`: the top `k`
stack entries replaced by `top`, the writes `W` applied, frames/globals/table/segments/budget kept. -/
structure VisAt (s0 : St) (k : Nat) (top : Array Val) (W : List (Nat × ByteArray)) (x : St) : Prop where
  stack : x.stack = base k s0 ++ top
  pages : x.pages = wbAll W s0.pages
  frames : x.frames = s0.frames
  globals : x.globals = s0.globals
  table : x.table = s0.table
  tableMax : x.tableMax = s0.tableMax
  elems : x.elems = s0.elems
  datas : x.datas = s0.datas
  stackRem : x.stackRem = s0.stackRem

/-- Two states' memories agree on the address set `A` (well-sized pages, same page count). -/
structure Agree (A : Nat → Prop) (u u' : St) : Prop where
  pok : PagesOK u
  pok' : PagesOK u'
  n : u.pages.size = u'.pages.size
  b : ∀ b, A b → readByte u b = readByte u' b

/-- **Twinned states** relative to the start pair `(s0, s0')`, the shared stack depth `k` and the
read set `A`: equal host parts, memories agreeing on `A`, and visible parts given by one common
effect from the start states. -/
def Tw (s0 s0' : St) (k : Nat) (A : Nat → Prop) (x x' : St) : Prop :=
  hostR x = hostR x' ∧ Agree A x x' ∧ ∃ top W, VisAt s0 k top W x ∧ VisAt s0' k top W x'

/-- **Low equivalence of the start states** on the address set `A` with shared stack top `k`: equal host
parts, the top `k` stack entries equal (both stacks at least `k` deep), and memories agreeing on `A`
(well-sized pages, same page count, equal bytes on `A`).  Everything else is free. -/
structure Low (A : Nat → Prop) (k : Nat) (s0 s0' : St) : Prop where
  host : hostR s0 = hostR s0'
  kle : k ≤ s0.stack.size
  kle' : k ≤ s0'.stack.size
  top : topK k s0 = topK k s0'
  mem : Agree A s0 s0'

/-! ## 2. Relational specs -/

/-- Corresponding results: equal values satisfying `V` and `T`-related states, or equal errors and
`T`-related states. -/
def RC (T : St → St → Prop) {α : Type} (V : α → Prop) :
    EStateM.Result String St α → EStateM.Result String St α → Prop
  | .ok a x, .ok b y => a = b ∧ V a ∧ T x y
  | .error e x, .error e' y => e = e' ∧ T x y
  | _, _ => False

/-- **Relational spec**: from `T`-related states, `m` and `m'` give corresponding results. -/
def Rel2 (T : St → St → Prop) {α : Type} (V : α → Prop) (m m' : HM α) : Prop :=
  ∀ s s', T s s' → RC T V (m s) (m' s')

section
variable {T : St → St → Prop}

theorem rel_pure {α : Type} {V : α → Prop} {a a' : α} (he : a = a') (h : V a) :
    Rel2 T V (pure a : HM α) (pure a' : HM α) := fun _ _ hs => ⟨he, h, hs⟩

theorem rel_bind {α β : Type} {V : α → Prop} {W : β → Prop} {m m' : HM α} {k k' : α → HM β}
    (hm : Rel2 T V m m') (hk : ∀ a, V a → Rel2 T W (k a) (k' a)) : Rel2 T W (m >>= k) (m' >>= k') := by
  intro s s' hs
  have h := hm s s' hs
  simp only [bind, EStateM.bind]
  revert h
  cases m s with
  | ok a x =>
    cases m' s' with
    | ok b y => rintro ⟨rfl, hv, ht⟩; exact hk a hv x y ht
    | error e y => intro h; exact h.elim
  | error e x =>
    cases m' s' with
    | ok b y => intro h; exact h.elim
    | error e' y => intro h; exact h

/-- **`get` then continue**: the continuations capture *different* (but `T`-related) states. -/
theorem rel_get_bind {β : Type} {W : β → Prop} {g g' : HM St} {k k' : St → HM β}
    (hg : ∀ s, g s = .ok s s) (hg' : ∀ s, g' s = .ok s s)
    (hk : ∀ x x', T x x' → Rel2 T W (k x) (k' x')) : Rel2 T W (g >>= k) (g' >>= k') := by
  intro s s' hs
  simp only [bind, EStateM.bind, hg, hg']
  exact hk s s' hs s s' hs

theorem rel_set {y y' : St} (h : T y y') : Rel2 T (fun _ => True) (set y : HM PUnit) (set y' : HM PUnit) :=
  fun _ _ _ => ⟨rfl, trivial, h⟩

theorem rel_modify {f f' : St → St} (h : ∀ x x', T x x' → T (f x) (f' x')) :
    Rel2 T (fun _ => True) (modify f : HM PUnit) (modify f' : HM PUnit) :=
  fun x x' hs => ⟨rfl, trivial, h x x' hs⟩

theorem rel_throw {α : Type} {V : α → Prop} {e e' : String} (he : e = e') :
    Rel2 T V (throw e : HM α) (throw e' : HM α) := fun _ _ hs => ⟨he, hs⟩

theorem rel_hErr {α : Type} {V : α → Prop} {e e' : String} (he : e = e') :
    Rel2 T V (hErr e : HM α) (hErr e' : HM α) := fun _ _ hs => ⟨by rw [he], hs⟩

/-- A failing first half: the continuations are never run. -/
theorem rel_throw_bind {α β : Type} {W : β → Prop} {e e' : String} {k k' : α → HM β} (he : e = e') :
    Rel2 T W ((throw e : HM α) >>= k) ((throw e' : HM α) >>= k') := fun _ _ hs => ⟨he, hs⟩

theorem rel_hErr_bind {α β : Type} {W : β → Prop} {e e' : String} {k k' : α → HM β} (he : e = e') :
    Rel2 T W ((hErr e : HM α) >>= k) ((hErr e' : HM α) >>= k') := fun _ _ hs => ⟨by rw [he], hs⟩

theorem rel_mono {α : Type} {V W : α → Prop} {m m' : HM α} (h : Rel2 T V m m') (hw : ∀ a, V a → W a) :
    Rel2 T W m m' := by
  intro s s' hs
  have := h s s' hs
  revert this
  cases m s <;> cases m' s' <;> simp only [RC] <;> first | exact fun h => ⟨h.1, hw _ h.2.1, h.2.2⟩ | exact id

theorem rel_map {α β : Type} {V : α → Prop} {f : α → β} {m m' : HM α} (h : Rel2 T V m m') :
    Rel2 T (fun _ => True) (f <$> m) (f <$> m') := by
  intro s s' hs
  have := h s s' hs
  simp only [Functor.map, EStateM.map]
  revert this
  cases m s <;> cases m' s' <;> simp only [RC] <;>
    first | exact fun h => ⟨by rw [h.1], trivial, h.2.2⟩ | exact id | exact fun h => h.elim

theorem rel_ite {α : Type} {V : α → Prop} {c c' : Prop} [Decidable c] [Decidable c'] {a b a' b' : HM α}
    (hc : c ↔ c') (ha : c → Rel2 T V a a') (hb : ¬ c → Rel2 T V b b') :
    Rel2 T V (if c then a else b) (if c' then a' else b') := by
  by_cases h : c
  · rw [if_pos h, if_pos (hc.mp h)]; exact ha h
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]; exact hb h

theorem rel_dite {α : Type} {V : α → Prop} {c c' : Prop} [Decidable c] [Decidable c'] {a : c → HM α}
    {b : ¬ c → HM α} {a' : c' → HM α} {b' : ¬ c' → HM α}
    (hc : c ↔ c') (ha : ∀ h h', Rel2 T V (a h) (a' h')) (hb : ∀ h h', Rel2 T V (b h) (b' h')) :
    Rel2 T V (if h : c then a h else b h) (if h : c' then a' h else b' h) := by
  by_cases h : c
  · rw [dif_pos h, dif_pos (hc.mp h)]; exact ha _ _
  · rw [dif_neg h, dif_neg (fun h' => h (hc.mpr h'))]; exact hb _ _

theorem rel_forIn_list {α β : Type} {V : β → Prop} (l : List α) (b : β) (f f' : α → β → HM (ForInStep β))
    (hb : V b) (hf : ∀ x, x ∈ l → ∀ c, V c → Rel2 T (fun r => V r.value) (f x c) (f' x c)) :
    Rel2 T V (forIn l b f) (forIn l b f') := by
  induction l generalizing b with
  | nil => exact rel_pure rfl hb
  | cons x l ih =>
    rw [List.forIn_cons, List.forIn_cons]
    refine rel_bind (hf x List.mem_cons_self b hb) fun r hr => ?_
    cases r with
    | done c => exact rel_pure rfl hr
    | yield c => exact ih c hr (fun y hy => hf y (List.mem_cons_of_mem _ hy))

theorem rel_forIn_range {β : Type} {V : β → Prop} (r : Std.Legacy.Range) (b : β)
    (f f' : Nat → β → HM (ForInStep β))
    (hb : V b) (hf : ∀ x, x ∈ List.range' r.start r.size r.step → ∀ c, V c →
      Rel2 T (fun r => V r.value) (f x c) (f' x c)) :
    Rel2 T V (forIn r b f) (forIn r b f') := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact rel_forIn_list _ b f f' hb hf

end

/-! ## 3. Memory agreement under writes -/

theorem array_modify_oob {α : Type} (a : Array α) (i : Nat) (f : α → α) (h : a.size ≤ i) : a.modify i f = a := by
  apply Array.ext
  · simp
  · intro j h1 h2; rw [Array.getElem_modify]; rw [if_neg (by simp at h1; omega)]

/-- `readByte` after `writeByte`, in or out of bounds (well-sized pages). -/
theorem readByte_writeByte' {s : St} (hP : PagesOK s) (a : Nat) (x : UInt8) (b : Nat) :
    readByte (writeByte s a x) b = if a = b ∧ a < memBytes s then x else readByte s b := by
  by_cases ha : a < memBytes s
  · rw [readByte_writeByte hP ha]
    by_cases hab : a = b
    · subst hab; simp [ha]
    · simp [hab]
  · have hle : s.pages.size ≤ a / pageSize := by
      unfold memBytes at ha
      exact (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    have e : writeByte s a x = s := by
      rw [writeByte_pages, array_modify_oob _ _ _ hle]
    rw [e]; simp [ha]

theorem agree_writeByte {A : Nat → Prop} {u u' : St} (h : Agree A u u') (a : Nat) (x : UInt8) :
    Agree A (writeByte u a x) (writeByte u' a x) := by
  refine ⟨writeByte_ok h.pok _ _, writeByte_ok h.pok' _ _, by simp [writeByte_size, h.n], fun b hb => ?_⟩
  rw [readByte_writeByte' h.pok, readByte_writeByte' h.pok', h.b b hb,
    show memBytes u = memBytes u' by simp [memBytes, h.n]]

theorem agree_foldl {A : Nat → Prop} (a : Nat) (d : ByteArray) :
    ∀ (l : List Nat) (u u' : St), Agree A u u' →
      Agree A (l.foldl (fun s i => writeByte s (a + i) d[i]!) u) (l.foldl (fun s i => writeByte s (a + i) d[i]!) u')
  | [], _, _, h => h
  | i :: l, u, u', h => by
    simp only [List.foldl_cons]
    exact agree_foldl a d l _ _ (agree_writeByte h _ _)

theorem agree_writeBytes {A : Nat → Prop} {u u' : St} (h : Agree A u u') (a : Nat) (d : ByteArray) :
    Agree A (writeBytes u a d) (writeBytes u' a d) := by
  rw [writeBytes_eq, writeBytes_eq]; exact agree_foldl a d _ u u' h

theorem agree_congr {A : Nat → Prop} {u u' v v' : St} (h : Agree A u u') (hv : v.pages = u.pages)
    (hv' : v'.pages = u'.pages) : Agree A v v' :=
  ⟨fun i hi => by have := h.pok i (by rw [← hv]; exact hi); simpa only [hv] using this,
   fun i hi => by have := h.pok' i (by rw [← hv']; exact hi); simpa only [hv'] using this,
   by rw [hv, hv', h.n], fun b hb => by rw [readByte_congr hv, readByte_congr hv', h.b b hb]⟩

theorem wbAll_cons (w : Nat × ByteArray) (W : List (Nat × ByteArray)) (p : Array ByteArray) :
    wbAll (w :: W) p = wbAll W (wbPages p w.1 w.2) := rfl

theorem wbAll_append (W V : List (Nat × ByteArray)) (p : Array ByteArray) :
    wbAll (W ++ V) p = wbAll V (wbAll W p) := by
  simp [wbAll, List.foldl_append]

theorem wbAll_size (W : List (Nat × ByteArray)) : ∀ p : Array ByteArray, (wbAll W p).size = p.size := by
  induction W with
  | nil => intro p; rfl
  | cons w W ih => intro p; rw [wbAll_cons, ih, wbPages_size]

/-- **Writes applied to both sides keep the agreement.** -/
theorem agree_wbAll {A : Nat → Prop} (W : List (Nat × ByteArray)) :
    ∀ (u u' : St), Agree A u u' → Agree A { u with pages := wbAll W u.pages } { u' with pages := wbAll W u'.pages } := by
  induction W with
  | nil => intro u u' h; exact h
  | cons w W ih =>
    intro u u' h
    have h1 := agree_writeBytes h w.1 w.2
    rw [writeBytes_split, writeBytes_split] at h1
    exact ih _ _ h1

/-- `readBytes` as a fold. -/
theorem readBytes_eq (s : St) (a n : Nat) :
    readBytes s a n = (List.range' 0 n).foldl (fun d i => d.push (readByte s (a + i))) ByteArray.empty := by
  unfold readBytes
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Id.run]

/-- `readBytes` only reads the bytes in its range. -/
theorem readBytes_congr {s s' : St} {a n : Nat} (h : ∀ i, i < n → readByte s (a + i) = readByte s' (a + i)) :
    readBytes s a n = readBytes s' a n := by
  rw [readBytes_eq, readBytes_eq]
  apply foldl_congr_mem
  intro i hi d
  simp only [List.mem_range'] at hi
  rw [h i (by omega)]

/-! ## 4. Twinned states -/

/-- The Wasm-visible fields except the registers (what `VisAt` speaks about). -/
def visW (s : St) : Array Val × Array ByteArray × List Frame × Array Val × Array (Option Nat) × Nat ×
    Array (Array (Option Nat)) × Array ByteArray × Nat :=
  (s.stack, s.pages, s.frames, s.globals, s.table, s.tableMax, s.elems, s.datas, s.stackRem)

theorem visAt_congr {s0 : St} {k : Nat} {top : Array Val} {W : List (Nat × ByteArray)} {x y : St}
    (h : VisAt s0 k top W x) (hv : visW y = visW x) : VisAt s0 k top W y := by
  simp only [visW, Prod.mk.injEq] at hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hv
  exact ⟨h1 ▸ h.stack, h2 ▸ h.pages, h3 ▸ h.frames, h4 ▸ h.globals, h5 ▸ h.table, h6 ▸ h.tableMax,
    h7 ▸ h.elems, h8 ▸ h.datas, h9 ▸ h.stackRem⟩

section
variable {s0 s0' : St} {k : Nat} {A : Nat → Prop}

/-- **A host-part-only change of twinned states** (both visible parts unchanged, equal new host
parts) keeps them twinned.  The workhorse of `set`/`modify` leaves. -/
theorem tw_of {x x' y y' : St} (h : Tw s0 s0' k A x x') (hv : visW y = visW x) (hv' : visW y' = visW x')
    (hh : hostR y = hostR y') : Tw s0 s0' k A y y' := by
  obtain ⟨-, hA, top, W, h1, h2⟩ := h
  simp only [visW, Prod.mk.injEq] at hv hv'
  refine ⟨hh, agree_congr hA hv.2.1 hv'.2.1, top, W, visAt_congr h1 ?_, visAt_congr h2 ?_⟩
  · simp only [visW, hv]
  · simp only [visW, hv']

/-- The field equalities of twinned states (right in terms of left), and equal memory size. -/
theorem Tw.eqs {x x' : St} (h : Tw s0 s0' k A x x') :
    x'.gas = x.gas ∧ x'.ctx = x.ctx ∧ x'.ret = x.ret ∧ x'.balance = x.balance ∧
    x'.storageUsage = x.storageUsage ∧ x'.registers = x.registers ∧ x'.regUsage = x.regUsage ∧
    x'.logs = x.logs ∧ x'.totalLogLen = x.totalLogLen ∧ x'.promises = x.promises ∧ x'.trie = x.trie ∧
    x'.actions = x.actions ∧ x'.dataCount = x.dataCount ∧ x'.real = x.real ∧
    x'.subsidized = x.subsidized ∧ x'.globalActions = x.globalActions ∧ x'.curveHosts = x.curveHosts ∧
    memBytes x' = memBytes x := by
  have e := h.1
  refine ⟨(congrArg St.gas e).symm, (congrArg St.ctx e).symm, (congrArg St.ret e).symm,
    (congrArg St.balance e).symm, (congrArg St.storageUsage e).symm, (congrArg St.registers e).symm,
    (congrArg St.regUsage e).symm, (congrArg St.logs e).symm, (congrArg St.totalLogLen e).symm,
    (congrArg St.promises e).symm, (congrArg St.trie e).symm, (congrArg St.actions e).symm,
    (congrArg St.dataCount e).symm, (congrArg St.real e).symm, (congrArg St.subsidized e).symm,
    (congrArg St.globalActions e).symm, (congrArg St.curveHosts e).symm, ?_⟩
  simp only [memBytes, h.2.1.n]

/-- Twinned states read the same bytes on `A`. -/
theorem Tw.read {x x' : St} (h : Tw s0 s0' k A x x') {b : Nat} (hb : A b) : readByte x' b = readByte x b :=
  (h.2.1.b b hb).symm

theorem Tw.readBytes {x x' : St} (h : Tw s0 s0' k A x x') {a n : Nat} (hA : ∀ i, i < n → A (a + i)) :
    readBytes x' a n = readBytes x a n :=
  readBytes_congr fun i hi => h.read (hA i hi)

end

/-- **Normalise after a `get`**: rewrite every host field of the right state (and its memory size) to
the left state's, so both continuations mention the same host data. -/
syntax "tw_norm " term : tactic
macro_rules
  | `(tactic| tw_norm $h) => `(tactic|
      (obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ :=
          Tw.eqs $h
       try simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]))

/-- **Close `t[x] = t[x']` (or `↔`) when `t` reads only host fields**: for a `Tw` hypothesis
`h : Tw … x x'`, `t[x] ≡ t[hostR x] = t[hostR x'] ≡ t[x']`. -/
syntax "tw_host" : tactic

/-- Close `Tw … y y'` for host-part updates of twinned `x`, `x'` (after `tw_norm`): tries every
`Tw` hypothesis of the context with `tw_of h rfl rfl rfl`. -/
syntax "tw_close" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| tw_close) => withMainContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      unless (← whnfR (← instantiateMVars d.type)).isAppOf ``Tw do continue
      let stx ← Term.exprToSyntax d.toExpr
      for t in [← `(tactic| exact $stx), ← `(tactic| exact tw_of $stx rfl rfl rfl),
                ← `(tactic| (refine tw_of $stx rfl rfl ?_; simp only [hostR, hostSide]; done)),
                ← `(tactic| (refine tw_of $stx rfl rfl ?_; simp only [hostR, hostSide, St.mk.injEq, true_and, and_true]; and_intros <;> first | trivial | rfl | tw_host))] do
        let saved ← saveState
        try
          Term.withoutErrToSorry (evalTactic t)
          if (← getGoals).isEmpty then return
          saved.restore
        catch _ => saved.restore
    throwError "tw_close: no `Tw` hypothesis closes the goal"


open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| tw_host) => withMainContext do
    let tgt ← instantiateMVars (← getMainTarget)
    let (isIff, lhs, rhs) ← match tgt.getAppFn.constName?, tgt.getAppArgs with
      | some ``Eq, #[_, l, r] => pure (false, l, r)
      | some ``Iff, #[l, r] => pure (true, l, r)
      | _, _ => throwError "tw_host: not an equation"
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      unless ty.isAppOfArity ``Tw 6 do continue
      let x := ty.getArg! 4
      let x' := ty.getArg! 5
      -- the motive: abstract `x` in the left side, or `x'` in the right side
      let mut Ms : List Lean.Expr := []
      let b1 ← kabstract lhs x
      if b1.hasLooseBVars then
        let M := Lean.mkLambda `z .default (mkConst ``St) b1
        if ← isDefEq (M.beta #[x']) rhs then Ms := Ms ++ [M]
      let b2 ← kabstract rhs x'
      if b2.hasLooseBVars then
        let M := Lean.mkLambda `z .default (mkConst ``St) b2
        if ← isDefEq (M.beta #[x]) lhs then Ms := Ms ++ [M]
      for M in Ms do
        let saved ← saveState
        try
          let Mstx ← Term.exprToSyntax M
          let xs ← Term.exprToSyntax x
          let xs' ← Term.exprToSyntax x'
          let hs ← Term.exprToSyntax d.toExpr
          let pf ← `(((rfl : $Mstx $xs = $Mstx (hostR $xs)).trans ((congrArg $Mstx ($hs).1).trans (rfl : $Mstx (hostR $xs') = $Mstx $xs'))))
          if isIff then evalTactic (← `(tactic| exact Iff.of_eq $pf))
          else evalTactic (← `(tactic| exact $pf))
          return
        catch _ => saved.restore
    throwError "tw_host: no `Tw` hypothesis closes the goal"

/-! ## 5. The lock-step tactic `rel_auto`

`rel_auto` proves `Rel2 T V m m'` for two copies of the same host program (`m'` differs from `m` only
in the states captured by `get`): it walks both programs in lock step over `bind`, `get`-`bind`
(followed by `tw_norm`), `if`/`dite` (side condition `c ↔ c'`, closed by `Iff.rfl` after
normalisation), `match` (`split`), `for`, `pure`, `set`/`modify` (closed by `tw_close`), `throw`,
and the primitive lemmas of `rel_prim`; unknown helpers are unfolded on both sides.  Side conditions
it cannot close (e.g. the read-set obligations of `readMemH`) are **left as goals**. -/

/-- Known relational primitive lemmas (extended by `macro_rules`). -/
syntax "rel_prim" : tactic
macro_rules | `(tactic| rel_prim) => `(tactic| fail "rel_prim")

syntax "rel_auto" : tactic

/-- The maximal differing subterm pairs of two terms of the same shape. -/
partial def relDiffs (e e' : Lean.Expr) : List (Lean.Expr × Lean.Expr) :=
  if e == e' then []
  else if e.isApp && e'.isApp && e.getAppNumArgs == e'.getAppNumArgs && e.getAppFn == e'.getAppFn then
    let sub := (e.getAppArgs.zip e'.getAppArgs).toList.flatMap fun (a, b) => relDiffs a b
    -- a differing state variable: the smallest unit to align is the application reading it
    if sub.any (fun (a, b) => a.isFVar || b.isFVar || a.hasLooseBVars || b.hasLooseBVars) then [(e, e')] else sub
  else match e, e' with
    | .lam _ t b _, .lam _ t' b' _ =>
      if t == t' then
        let sub := relDiffs b b'
        if sub.any (fun (a, b) => a.hasLooseBVars || b.hasLooseBVars) then [(e, e')] else sub
      else [(e, e')]
    | .mdata _ a, .mdata _ b => relDiffs a b
    | _, _ => [(e, e')]

open Lean Meta Elab Tactic in
/-- **Align the right program with the left one**: for each maximal differing subterm pair `(d, d')`
(host reads of the captured states), prove `d = d'` by `tw_host` and rewrite `d'` to `d`. -/
def relAlign (g : MVarId) (e e' : Lean.Expr) : TacticM (Option MVarId) := g.withContext do
  if e == e' then return none
  let mut g := g
  let mut changed := false
  for (d, d') in relDiffs e e' do
    if d.hasLooseBVars || d'.hasLooseBVars then continue
    let saved ← saveState
    try
      let g' ← g.withContext do
        let mv ← mkFreshExprSyntheticOpaqueMVar (← mkEq d d')
        setGoals [mv.mvarId!]
        Term.withoutErrToSorry (evalTactic (← `(tactic| tw_host)))
        unless (← getGoals).isEmpty do throwError "relAlign"
        let r ← g.rewrite (← g.getType) (← mkEqSymm mv)
        g.replaceTargetEq r.eNew r.eqProof
      g := g'
      changed := true
    catch _ => saved.restore
  return if changed then some g else none

open Lean Meta Elab Tactic in
/-- One `rel_auto` step; returns the goals it leaves. -/
partial def relAutoGo (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let t := (← whnfR t).cleanupAnnotations
  let rec norm : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n + 1, e => match e.headBeta with
      | .letE _ _ v b _ => norm n (b.instantiate1 v)
      | .mdata _ e => norm n e
      | e => e
  unless t.isAppOfArity ``Rel2 5 do throwError "rel_auto: not a `Rel2` goal{indentExpr t}"
  let args := t.getAppArgs
  let T := args[0]!
  let α := args[1]!
  let W := args[2]!
  let m := norm 1000 args[3]!
  let m' := norm 1000 args[4]!
  let g ← g.replaceTargetDefEq (mkAppN t.getAppFn #[T, α, W, m, m'])
  let nm := m.getAppFn.constName?.getD .anonymous
  let nm' := m'.getAppFn.constName?.getD .anonymous
  let isGet (e : Lean.Expr) : Bool :=
    let n := e.getAppFn.constName?.getD .anonymous
    n == ``MonadState.get || n == ``MonadStateOf.get || n == ``get || n == ``getThe
  -- run a tactic on `g`, returning the goals it leaves
  let runT (g : MVarId) (tac : TSyntax `tactic) : TacticM (List MVarId) := do
    setGoals [g]
    Term.withoutErrToSorry (evalTactic tac)
    getGoals
  -- try to close `g` by `tac`; if it fails or leaves goals, keep `g` as a residual goal
  let close (g : MVarId) (tac : TSyntax `tactic) : TacticM (List MVarId) := do
    let saved ← saveState
    try
      let gs ← runT g tac
      if gs.isEmpty then return [] else saved.restore; return [g]
    catch _ => saved.restore; return [g]
  if nm == ``Bind.bind && nm' == ``Bind.bind && m.getAppNumArgs == 6 && m'.getAppNumArgs == 6 then
    let β := m.getArg! 3
    let x := m.getArg! 4
    let f := m.getArg! 5
    let x' := m'.getArg! 4
    let f' := m'.getArg! 5
    let xn := x.getAppFn.constName?.getD .anonymous
    if xn == ``hErr || xn == ``throw || xn == ``MonadExcept.throw || xn == ``MonadExceptOf.throw then
      return (← close g (← `(tactic| first | (refine rel_hErr_bind ?_; rfl) | (refine rel_throw_bind ?_; rfl))))
    if isGet x && isGet x' then
      let st := mkConst ``St
      let hgT ← withLocalDeclD `s st fun s => do
        mkForallFVars #[s] (← mkEq (mkApp x s) (mkAppN (mkConst ``EStateM.Result.ok [levelZero]) #[mkConst ``String, st, st, s, s]))
      let hgT' ← withLocalDeclD `s st fun s => do
        mkForallFVars #[s] (← mkEq (mkApp x' s) (mkAppN (mkConst ``EStateM.Result.ok [levelZero]) #[mkConst ``String, st, st, s, s]))
      let hg ← mkFreshExprSyntheticOpaqueMVar hgT
      let hg' ← mkFreshExprSyntheticOpaqueMVar hgT'
      let hkT ← withLocalDeclD `x st fun a => withLocalDeclD `x' st fun a' => do
        withLocalDeclD `hx (mkApp2 T a a') fun ha => do
          mkForallFVars #[a, a', ha] (mkAppN (mkConst ``Rel2) #[T, β, W, (mkApp f a).headBeta, (mkApp f' a').headBeta])
      let hk ← mkFreshExprSyntheticOpaqueMVar hkT
      g.assign (mkAppN (mkConst ``rel_get_bind) #[T, β, W, x, x', f, f', hg, hg', hk])
      let r1 ← runT hg.mvarId! (← `(tactic| exact fun _ => rfl))
      let r2 ← runT hg'.mvarId! (← `(tactic| exact fun _ => rfl))
      let (fv, gk) ← hk.mvarId!.introN 3
      let hx ← gk.withContext do Term.exprToSyntax (mkFVar fv[2]!)
      setGoals [gk]
      Term.withoutErrToSorry (evalTactic (← `(tactic| tw_norm $hx)))
      let gk ← getMainGoal
      return r1 ++ r2 ++ (← relAutoGo gk)
    else
      let αx := m.getArg! 2
      let V ← withLocalDeclD `a αx fun a => mkLambdaFVars #[a] (mkConst ``True)
      let hmT := mkAppN (mkConst ``Rel2) #[T, αx, V, x, x']
      let hm ← mkFreshExprSyntheticOpaqueMVar hmT
      let hkT ← withLocalDeclD `a αx fun a => do
        let va := (mkApp V a).headBeta
        withLocalDeclD `ha va fun ha => do
          mkForallFVars #[a, ha] (mkAppN (mkConst ``Rel2) #[T, β, W, (mkApp f a).headBeta, (mkApp f' a).headBeta])
      let hk ← mkFreshExprSyntheticOpaqueMVar hkT
      g.assign (mkAppN (mkConst ``rel_bind) #[T, αx, β, V, W, x, x', f, f', hm, hk])
      let r1 ← relAutoGo hm.mvarId!
      let (_, hk') ← hk.mvarId!.introN 2
      return r1 ++ (← relAutoGo hk')
  else if nm == ``ite && nm' == ``ite && m.getAppNumArgs == 5 && m'.getAppNumArgs == 5 then
    let c := m.getArg! 1
    let inst := m.getArg! 2
    let a := m.getArg! 3
    let b := m.getArg! 4
    let c' := m'.getArg! 1
    let inst' := m'.getArg! 2
    let a' := m'.getArg! 3
    let b' := m'.getArg! 4
    let hc ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Iff) c c')
    let haT ← withLocalDeclD `h c fun h => mkForallFVars #[h] (mkAppN (mkConst ``Rel2) #[T, α, W, a, a'])
    let hbT ← withLocalDeclD `h (mkNot c) fun h => mkForallFVars #[h] (mkAppN (mkConst ``Rel2) #[T, α, W, b, b'])
    let ha ← mkFreshExprSyntheticOpaqueMVar haT
    let hb ← mkFreshExprSyntheticOpaqueMVar hbT
    g.assign (mkAppN (mkConst ``rel_ite) #[T, α, W, c, c', inst, inst', a, b, a', b', hc, ha, hb])
    let r0 ← close hc.mvarId! (← `(tactic| first | exact Iff.rfl | tw_host))
    let (_, ga) ← ha.mvarId!.intro1
    let r1 ← relAutoGo ga
    let (_, gb) ← hb.mvarId!.intro1
    return r0 ++ r1 ++ (← relAutoGo gb)
  else if nm == ``dite && nm' == ``dite && m.getAppNumArgs == 5 && m'.getAppNumArgs == 5 then
    let c := m.getArg! 1
    let inst := m.getArg! 2
    let a := m.getArg! 3
    let b := m.getArg! 4
    let c' := m'.getArg! 1
    let inst' := m'.getArg! 2
    let a' := m'.getArg! 3
    let b' := m'.getArg! 4
    let hc ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Iff) c c')
    let haT ← withLocalDeclD `h c fun h => withLocalDeclD `h' c' fun h' =>
      mkForallFVars #[h, h'] (mkAppN (mkConst ``Rel2) #[T, α, W, (mkApp a h).headBeta, (mkApp a' h').headBeta])
    let hbT ← withLocalDeclD `h (mkNot c) fun h => withLocalDeclD `h' (mkNot c') fun h' =>
      mkForallFVars #[h, h'] (mkAppN (mkConst ``Rel2) #[T, α, W, (mkApp b h).headBeta, (mkApp b' h').headBeta])
    let ha ← mkFreshExprSyntheticOpaqueMVar haT
    let hb ← mkFreshExprSyntheticOpaqueMVar hbT
    g.assign (mkAppN (mkConst ``rel_dite) #[T, α, W, c, c', inst, inst', a, b, a', b', hc, ha, hb])
    let r0 ← close hc.mvarId! (← `(tactic| first | exact Iff.rfl | tw_host))
    let (_, ga) ← ha.mvarId!.introN 2
    let r1 ← relAutoGo ga
    let (_, gb) ← hb.mvarId!.introN 2
    return r0 ++ r1 ++ (← relAutoGo gb)
  else if nm == ``Pure.pure && nm' == ``Pure.pure && m.getAppNumArgs == 4 && m'.getAppNumArgs == 4 then
    let v := m.getArg! 3
    let v' := m'.getArg! 3
    let he ← mkFreshExprSyntheticOpaqueMVar (← mkEq v v')
    let hw ← mkFreshExprSyntheticOpaqueMVar (mkApp W v).headBeta
    g.assign (mkAppN (mkConst ``rel_pure) #[T, α, W, v, v', he, hw])
    let r0 ← close he.mvarId! (← `(tactic| first | rfl | tw_host))
    let r1 ← close hw.mvarId! (← `(tactic| first | trivial | assumption))
    return r0 ++ r1
  else if (nm == ``MonadStateOf.set || nm == ``MonadState.set || nm == ``set) then
    let gs ← runT g (← `(tactic| refine rel_set ?_))
    let mut res := []
    for g' in gs do res := res ++ (← close g' (← `(tactic| tw_close)))
    return res
  else if nm == ``modify || nm == ``MonadState.modifyGet || nm == ``modifyGet then
    let g ← match ← (if m != m' then relAlign g m m' else pure none) with
      | some g' => pure g'
      | none => pure g
    close g (← `(tactic| (refine rel_modify (fun y y' hy => ?_); tw_norm hy; first | tw_close | (split <;> tw_close))))
  else if (nm == ``throw || nm == ``MonadExcept.throw || nm == ``MonadExceptOf.throw || nm == ``throwThe ||
      nm == ``hErr) then
    let gs ← runT g (← `(tactic| first | refine rel_hErr ?_ | refine rel_throw ?_))
    let mut res := []
    for g' in gs do res := res ++ (← close g' (← `(tactic| first | rfl | tw_host)))
    return res
  else if nm == ``ForIn.forIn && nm' == ``ForIn.forIn && m.getAppNumArgs ≥ 3 then
    let saved ← saveState
    try
      let gs ← runT g (← `(tactic| rel_prim))
      return gs
    catch _ => saved.restore
    let gs ← runT g (← `(tactic| first
      | refine rel_forIn_range (V := fun _ => True) _ _ _ _ trivial (fun x hx c hc => ?_)
      | refine rel_forIn_list (V := fun _ => True) _ _ _ _ trivial (fun x hx c hc => ?_)))
    let mut res := []
    for g' in gs do res := res ++ (← relAutoGo g')
    return res
  else if nm == ``Functor.map && nm' == ``Functor.map then
    let gs ← runT g (← `(tactic| refine rel_map ?_))
    let mut res := []
    for g' in gs do res := res ++ (← relAutoGo g')
    return res
  else if (← isMatcher nm) || (← isMatcher nm') then
    -- align differing discriminants first (host reads of the captured states)
    if nm == nm' && m.getAppNumArgs == m'.getAppNumArgs then
      if let some info ← getMatcherInfo? nm then
        for i in [0:info.numDiscrs] do
          let d := m.getArg! (info.getFirstDiscrPos + i)
          let d' := m'.getArg! (info.getFirstDiscrPos + i)
          if d != d' then
            if let some g' ← relAlign g d d' then return ← relAutoGo g'
    setGoals [g]
    evalTactic (← `(tactic| split))
    let mut res := []
    for g' in ← getGoals do
      let saved ← saveState
      -- a branch made impossible by the lock step (the two matches disagree) closes by contradiction
      let closed ← try
          let gs ← runT g' (← `(tactic| contradiction))
          pure gs.isEmpty
        catch _ => pure false
      if closed then continue
      saved.restore
      res := res ++ (← relAutoGo g')
    return res
  else
    let saved ← saveState
    try
      let gs ← runT g (← `(tactic| rel_prim))
      return gs
    catch ex =>
      saved.restore
      -- the right program differs from the left only in host reads: align and retry
      if m != m' then
        if let some g' ← relAlign g m m' then
          let saved2 ← saveState
          try
            let gs ← runT g' (← `(tactic| rel_prim))
            return gs
          catch _ => saved2.restore
      saved.restore
      -- an unknown helper on both sides: unfold its definition and continue
      if nm == nm' then
        match ← unfoldDefinition? m, ← unfoldDefinition? m' with
        | some u, some u' =>
          let g' ← g.replaceTargetDefEq (mkAppN t.getAppFn #[T, α, W, u, u'])
          relAutoGo g'
        | _, _ => throw ex
      else return [g]

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| rel_auto) => do
    let g ← getMainGoal
    let rs ← relAutoGo g
    setGoals rs


/-! ## 6. Primitives: gas -/

section
variable {s0 s0' : St} {k : Nat} {A : Nat → Prop}

theorem rel_withGas (f : Gas → Gas × Option String) :
    Rel2 (Tw s0 s0' k A) (fun _ => True) (withGas f) (withGas f) := by
  unfold withGas; rel_auto

theorem rel_payBaseH (c : Cost) : Rel2 (Tw s0 s0' k A) (fun _ => True) (payBaseH c) (payBaseH c) := rel_withGas _
theorem rel_payPerH (c : Cost) (n : Nat) : Rel2 (Tw s0 s0' k A) (fun _ => True) (payPerH c n) (payPerH c n) :=
  rel_withGas _
theorem rel_payActionH (b bc u : Nat) :
    Rel2 (Tw s0 s0' k A) (fun _ => True) (payActionH b bc u) (payActionH b bc u) := rel_withGas _
theorem rel_burnH (x : Nat) : Rel2 (Tw s0 s0' k A) (fun _ => True) (burnH x) (burnH x) := rel_withGas _

end

macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible exact rel_withGas _)
macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible exact rel_payBaseH _)
macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible exact rel_payPerH _ _)
macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible exact rel_payActionH _ _ _)
macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible exact rel_burnH _)

/-! ## 7. Primitives: the operand stack and memory -/

/-- The integer an operand-stack value pops as (`popN`). -/
def valNat : Val → Nat
  | .i32 v => v.toNat
  | .i64 v => v.toNat
  | .f32 v => v.toNat
  | .f64 v => v.toNat
  | .ref _ => 0

theorem popN_eq (s : St) : popN s = (valNat (s.stack.back?.getD (.i32 0)), { s with stack := s.stack.pop }) := by
  unfold popN popV
  cases s.stack.back?.getD (.i32 0) <;> rfl

/-- `n` pops, accumulating the values (the loop of `popArgs`). -/
def popsF : Nat → St → Array Nat → Array Nat × St
  | 0, s, out => (out, s)
  | j + 1, s, out => popsF j (popN s).2 (out.push (popN s).1)

theorem popLoop : ∀ (j a : Nat) (out : Array Nat) (s : St),
    forIn (m := HM) (List.range' a j) out (fun _ r => EStateM.bind get fun d =>
      EStateM.bind (set (popN d).snd) fun _ => pure (ForInStep.yield (r.push (popN d).fst))) s =
      .ok (popsF j s out).1 (popsF j s out).2
  | 0, a, out, s => rfl
  | j + 1, a, out, s => by
    rw [List.range'_succ, List.forIn_cons]
    exact popLoop j (a + 1) _ _

theorem popsF_size : ∀ (j : Nat) (s : St) (out : Array Nat), (popsF j s out).1.size = out.size + j
  | 0, _, _ => rfl
  | j + 1, s, out => by simp only [popsF]; rw [popsF_size j]; simp; omega

/-- **`popArgs` computed**: the popped values (first argument first) and the popped state. -/
theorem popArgs_eq (n : Nat) (s : St) :
    popArgs n s = .ok ⟨(popsF n s #[]).1.reverse, by simp [popsF_size]⟩ (popsF n s #[]).2 := by
  unfold popArgs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', bind, EStateM.bind]
  rw [show [:n].size = n by simp, popLoop]
  dsimp only
  rw [dif_pos (by simp [popsF_size])]
  rfl

/-- Pops from two stacks with a common top `C` (lists, top last): equal values, the common top
shortened, everything else kept. -/
theorem popsF_two : ∀ (j : Nat) (x x' : St) (B B' C : List Val) (out : Array Nat),
    x.stack.toList = B ++ C → x'.stack.toList = B' ++ C → j ≤ C.length →
    (popsF j x out).1 = (popsF j x' out).1 ∧
    (popsF j x out).2 = { x with stack := (B ++ C.take (C.length - j)).toArray } ∧
    (popsF j x' out).2 = { x' with stack := (B' ++ C.take (C.length - j)).toArray }
  | 0, x, x', B, B', C, out, h, h', _ => by
    refine ⟨rfl, ?_, ?_⟩
    · show x = _; rw [Nat.sub_zero, List.take_length, ← h]
    · show x' = _; rw [Nat.sub_zero, List.take_length, ← h']
  | j + 1, x, x', B, B', C, out, h, h', hj => by
    have hC : C ≠ [] := by intro e; subst e; simp at hj
    have hb : x.stack.back? = C.getLast? := by
      rw [← Array.getLast?_toList, h, List.getLast?_append]; simp [List.getLast?_eq_some_getLast hC]
    have hb' : x'.stack.back? = C.getLast? := by
      rw [← Array.getLast?_toList, h', List.getLast?_append]; simp [List.getLast?_eq_some_getLast hC]
    have hp : ({ x with stack := x.stack.pop } : St).stack.toList = B ++ C.dropLast := by
      simp only [Array.toList_pop, h, List.dropLast_append_of_ne_nil hC]
    have hp' : ({ x' with stack := x'.stack.pop } : St).stack.toList = B' ++ C.dropLast := by
      simp only [Array.toList_pop, h', List.dropLast_append_of_ne_nil hC]
    have hl : j ≤ C.dropLast.length := by simp; omega
    simp only [popsF, popN_eq, hb, hb']
    obtain ⟨e1, e2, e3⟩ := popsF_two j _ _ B B' C.dropLast _ hp hp' hl
    refine ⟨e1, ?_, ?_⟩
    · rw [e2, List.dropLast_eq_take, List.take_take]
      congr 4; simp; omega
    · rw [e3, List.dropLast_eq_take, List.take_take]
      congr 4; simp; omega

section
variable {s0 s0' : St} {k : Nat} {A : Nat → Prop}

theorem base_append_topK (k : Nat) (s : St) : base k s ++ topK k s = s.stack := by
  unfold base topK
  rw [Array.extract_append_extract]; simp

/-- The start pair is twinned (nothing popped, nothing written). -/
theorem tw_start (h : Low A k s0 s0') : Tw s0 s0' k A s0 s0' := by
  refine ⟨h.host, h.mem, topK k s0, [], ⟨(base_append_topK k s0).symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨by rw [h.top, base_append_topK], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **`popArgs` from a low-equivalent start pair** (at most `k` arguments): the same arguments, and
the popped states are twinned. -/
theorem popArgs_two (h : Low A k s0 s0') {n : Nat} (hn : n ≤ k) :
    ∃ a y y', popArgs n s0 = .ok a y ∧ popArgs n s0' = .ok a y' ∧ Tw s0 s0' k A y y' := by
  have h1 : s0.stack.toList = (base k s0).toList ++ (topK k s0).toList := by
    rw [← Array.toList_append, base_append_topK]
  have h2 : s0'.stack.toList = (base k s0').toList ++ (topK k s0).toList := by
    rw [h.top, ← Array.toList_append, base_append_topK]
  have hl : n ≤ (topK k s0).toList.length := by simp [topK]; have := h.kle; omega
  obtain ⟨e1, e2, e3⟩ := popsF_two n s0 s0' _ _ _ #[] h1 h2 hl
  refine ⟨_, (popsF n s0 #[]).2, (popsF n s0' #[]).2, popArgs_eq n s0, ?_, ?_⟩
  · simp only [popArgs_eq, e1]
  · rw [e2, e3]
    refine ⟨h.host, agree_congr h.mem rfl rfl, ((topK k s0).toList.take ((topK k s0).toList.length - n)).toArray, [],
      ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · show List.toArray _ = _; apply Array.toList_inj.mp; simp
    · show List.toArray _ = _; apply Array.toList_inj.mp; simp

/-- Twinned states stay twinned under a common push. -/
theorem tw_pushV {x x' : St} (h : Tw s0 s0' k A x x') (v : Val) : Tw s0 s0' k A (pushV x v) (pushV x' v) := by
  obtain ⟨hh, hA, top, W, h1, h2⟩ := h
  exact ⟨hh, agree_congr hA rfl rfl, top.push v, W, ⟨by simp [pushV, h1.stack], h1.pages, h1.frames, h1.globals, h1.table,
    h1.tableMax, h1.elems, h1.datas, h1.stackRem⟩, ⟨by simp [pushV, h2.stack], h2.pages, h2.frames,
    h2.globals, h2.table, h2.tableMax, h2.elems, h2.datas, h2.stackRem⟩⟩

theorem tw_pushI64 {x x' : St} (h : Tw s0 s0' k A x x') (v : Nat) : Tw s0 s0' k A (pushI64 x v) (pushI64 x' v) :=
  tw_pushV h _
theorem tw_pushI32 {x x' : St} (h : Tw s0 s0' k A x x') (v : Nat) : Tw s0 s0' k A (pushI32 x v) (pushI32 x' v) :=
  tw_pushV h _

/-- Twinned states stay twinned under a common write. -/
theorem tw_writeBytes {x x' : St} (h : Tw s0 s0' k A x x') (a : Nat) (d : ByteArray) :
    Tw s0 s0' k A (writeBytes x a d) (writeBytes x' a d) := by
  have hA := agree_writeBytes h.2.1 a d
  obtain ⟨hh, -, top, W, h1, h2⟩ := h
  rw [writeBytes_split] at hA ⊢
  rw [writeBytes_split] at hA ⊢
  refine ⟨hh, hA, top, W ++ [(a, d)], ⟨h1.stack, ?_, h1.frames, h1.globals, h1.table, h1.tableMax, h1.elems,
    h1.datas, h1.stackRem⟩, ⟨h2.stack, ?_, h2.frames, h2.globals, h2.table, h2.tableMax, h2.elems, h2.datas,
    h2.stackRem⟩⟩
  · show wbPages x.pages a d = _; rw [wbAll_append, ← h1.pages]; rfl
  · show wbPages x'.pages a d = _; rw [wbAll_append, ← h2.pages]; rfl

/-- The memory size of a twinned state is the start state's. -/
theorem Tw.mem0 {x x' : St} (h : Tw s0 s0' k A x x') : memBytes x = memBytes s0 := by
  obtain ⟨-, -, top, W, h1, -⟩ := h
  simp only [memBytes, h1.pages, wbAll_size]

end

/-- `tw_close`, extended: pushes and writes of twinned states. -/
syntax "tw_step" : tactic
open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| tw_step) => withMainContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      unless (← whnfR (← instantiateMVars d.type)).isAppOf ``Tw do continue
      let stx ← Term.exprToSyntax d.toExpr
      for t in [← `(tactic| exact tw_writeBytes $stx _ _), ← `(tactic| exact tw_pushI64 $stx _),
                ← `(tactic| exact tw_pushI32 $stx _), ← `(tactic| (split <;> first | exact tw_pushI64 $stx _ | exact tw_pushI32 $stx _))] do
        let saved ← saveState
        try
          Term.withoutErrToSorry (evalTactic t)
          if (← getGoals).isEmpty then return
          saved.restore
        catch _ => saved.restore
    throwError "tw_step: no `Tw` hypothesis closes the goal"

section
variable {s0 s0' : St} {k : Nat} {A : Nat → Prop}

theorem rel_pushRet (v : Nat) (is64 : Bool) :
    Rel2 (Tw s0 s0' k A) (fun _ => True) (pushRet v is64) (pushRet v is64) :=
  rel_modify fun _ _ h => by cases is64 <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> tw_step

theorem rel_writeMemH (ptr : Nat) (d : ByteArray) :
    Rel2 (Tw s0 s0' k A) (fun _ => True) (writeMemH ptr d) (writeMemH ptr d) := by
  unfold writeMemH; rel_auto
  all_goals tw_step

theorem rel_regGetH (id : Nat) : Rel2 (Tw s0 s0' k A) (fun _ => True) (regGetH id) (regGetH id) := by
  unfold regGetH; rel_auto

theorem rel_regSetH (id : Nat) (d : ByteArray) (cb : Bool) :
    Rel2 (Tw s0 s0' k A) (fun _ => True) (regSetH id d cb) (regSetH id d cb) := by
  unfold regSetH; rel_auto

/-- **`readMemH` reads only its range**: related as long as the range is in `A` whenever the bounds
check passes. -/
theorem rel_readMemH {ptr len : Nat} (hA : ptr + len ≤ memBytes s0 → ∀ i, i < len → A (ptr + i)) :
    Rel2 (Tw s0 s0' k A) (fun _ => True) (readMemH ptr len) (readMemH ptr len) := by
  unfold readMemH; rel_auto
  all_goals
    refine (Tw.readBytes (s0 := s0) (s0' := s0') (k := k) (A := A) ?_ ?_).symm
    · assumption
    · apply hA
      have := Tw.mem0 (s0 := s0) (s0' := s0') (k := k) (A := A) ‹_›
      omega

end

macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible exact rel_pushRet _ _)
macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible exact rel_writeMemH _ _)
macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible exact rel_regGetH _)
macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible exact rel_regSetH _ _ _)
/-- `readMemH` leaves its read-set obligation as a goal. -/
macro_rules | `(tactic| rel_prim) => `(tactic| with_reducible refine rel_readMemH ?_)

end TwoRun
end WasmBase
