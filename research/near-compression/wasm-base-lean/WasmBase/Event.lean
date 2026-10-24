import WasmBase.Prelude
import WasmBase.Check
import WasmBase.Mem
/-!
# WasmBase.Event — channel messages, the spec-state relation, and the gas/charge step

The value channel (bus CH) carries `Msg`s.  A spec state `s` with current frame `f` is related to a
set `live` of channel messages (`RelW`, README §10) when `live` is exactly the encoding of the whole
operand stack (space 0, slot = absolute stack index), of the current frame's locals (space
`16 + cid`, slot = local index), each with some producer time `< t`, and of an outer part `E.live`
(caller frames' locals, and later globals, memory words and call records) in other spaces.  The
frame environment `E : Env` carries the stack base, the activation id and the caller frames.
-/
namespace WasmBase
open NearSpecV3.Wasm

structure Msg where
  space : Nat
  slot : Nat
  tag : Nat
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  tp : Nat
  deriving DecidableEq, Repr

def Msg.val (m : Msg) : Nat := val4 m.l0 m.l1 m.l2 m.l3

/-- Limbs are 16-bit; i32 values have zero upper limbs; tags are 0/1. -/
def Msg.ok (m : Msg) : Prop :=
  m.l0 < 65536 ∧ m.l1 < 65536 ∧ m.l2 < 65536 ∧ m.l3 < 65536 ∧
  ((m.tag = 0 ∧ m.l2 = 0 ∧ m.l3 = 0) ∨ m.tag = 1)

def vTag : Val → Nat
  | .i64 _ => 1
  | _ => 0

def vNum : Val → Nat
  | .i32 v => v.toNat
  | .i64 v => v.toNat
  | .f32 b => b.toNat
  | .f64 b => b.toNat
  | .ref _ => 0

/-- The AIR's value channel is integer-only.  The D1 checker rejects every float instruction
(`kindOf` has no float arm), so a D1 program never pushes an `f32`/`f64`; `isNum` is stated to
exclude them so that `enc_toVal` is honest rather than silently reinterpreting float bits as an
`i32`. -/
def isNum : Val → Prop
  | .i32 _ => True
  | .i64 _ => True
  | _ => False

/-- Encoding of a value as a channel message. -/
def enc (space slot : Nat) (v : Val) (tp : Nat) : Msg :=
  ⟨space, slot, vTag v, vNum v % 65536, vNum v / 65536 % 65536, vNum v / 2 ^ 32 % 65536,
   vNum v / 2 ^ 48 % 65536, tp⟩

/-- The decoded value of a well-formed message. -/
def Msg.toVal (m : Msg) : Val :=
  if m.tag = 1 then .i64 (UInt64.ofNat m.val) else .i32 (UInt32.ofNat m.val)

theorem vNum_lt_i32 (v : UInt32) : vNum (.i32 v) < 2 ^ 32 := v.toNat_lt
theorem vNum_lt_i64 (v : UInt64) : vNum (.i64 v) < 2 ^ 64 := v.toNat_lt

theorem enc_ok {v : Val} (hv : isNum v) (space slot tp : Nat) : (enc space slot v tp).ok := by
  cases v with
  | i32 x =>
    have := x.toNat_lt
    simp only [enc, Msg.ok, vTag, vNum, Nat.reducePow, true_and, or_true, and_true, Nat.reduceEqDiff, or_false] at *
    omega
  | i64 x =>
    have := x.toNat_lt
    simp only [enc, Msg.ok, vTag, vNum, Nat.reducePow, true_and, or_true, and_true, Nat.reduceEqDiff, or_false] at *
    omega
  | f32 _ | f64 _ | ref _ => exact absurd hv id

theorem enc_val {v : Val} (hv : isNum v) (space slot tp : Nat) : (enc space slot v tp).val = vNum v := by
  cases v with
  | i32 x =>
    have := x.toNat_lt
    simp only [enc, Msg.val, val4, vNum, Nat.reducePow] at *
    omega
  | i64 x =>
    have := x.toNat_lt
    simp only [enc, Msg.val, val4, vNum, Nat.reducePow] at *
    omega
  | f32 _ | f64 _ | ref _ => exact absurd hv id

theorem enc_toVal {v : Val} (hv : isNum v) (space slot tp : Nat) : (enc space slot v tp).toVal = v := by
  cases v with
  | i32 x =>
    have hv := enc_val (v := .i32 x) trivial space slot tp
    have ht : (enc space slot (.i32 x) tp).tag = 0 := rfl
    simp only [Msg.toVal, hv, ht, vNum]
    simp
  | i64 x =>
    have hv := enc_val (v := .i64 x) trivial space slot tp
    have ht : (enc space slot (.i64 x) tp).tag = 1 := rfl
    simp only [Msg.toVal, hv, ht, vNum]
    simp
  | f32 _ | f64 _ | ref _ => exact absurd hv id

/-- A message `m` equals the encoding of its decoded value when well-formed. -/
theorem enc_of_ok {m : Msg} (hm : m.ok) : enc m.space m.slot m.toVal m.tp = m := by
  obtain ⟨h0, h1, h2, h3, ht⟩ := hm
  have hv : m.val < 2 ^ 64 := by simp only [Msg.val, val4, Nat.reducePow]; omega
  rcases ht with ⟨ht, z2, z3⟩ | ht
  · have hv32 : m.val < 2 ^ 32 := by simp only [Msg.val, val4, Nat.reducePow]; omega
    have : m.tag ≠ 1 := by omega
    simp only [enc, Msg.toVal, this, ite_false, vTag, vNum, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hv32]
    cases m; simp_all [Msg.val, val4, Nat.reducePow]; omega
  · simp only [enc, Msg.toVal, ht, ite_true, vTag, vNum, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hv]
    cases m; simp_all [Msg.val, val4, Nat.reducePow]; omega

end WasmBase

namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-! ## Views of the spec state as channel messages -/

def stackView (stk : Array Val) (tps : Nat → Nat) : List Msg :=
  (List.range stk.size).map fun i => enc 0 i (stk[i]?.getD default) (tps i)

/-- The locals of one activation, in channel space `sp` (`16 + cid`). -/
def localView (sp : Nat) (locs : Array Val) (tpl : Nat → Nat) : List Msg :=
  (List.range locs.size).map fun j => enc sp j (locs[j]?.getD default) (tpl j)

theorem mem_stackView {x : Msg} {stk : Array Val} {tps : Nat → Nat} :
    x ∈ stackView stk tps ↔ ∃ i, i < stk.size ∧ x = enc 0 i (stk[i]?.getD default) (tps i) := by
  simp only [stackView, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem mem_localView {x : Msg} {sp : Nat} {locs : Array Val} {tpl : Nat → Nat} :
    x ∈ localView sp locs tpl ↔ ∃ j, j < locs.size ∧ x = enc sp j (locs[j]?.getD default) (tpl j) := by
  simp only [localView, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

@[simp] theorem enc_space (a b : Nat) (v : Val) (tp : Nat) : (enc a b v tp).space = a := rfl
@[simp] theorem enc_slot (a b : Nat) (v : Val) (tp : Nat) : (enc a b v tp).slot = b := rfl
@[simp] theorem enc_tp (a b : Nat) (v : Val) (tp : Nat) : (enc a b v tp).tp = tp := rfl
@[simp] theorem enc_tag (a b : Nat) (v : Val) (tp : Nat) : (enc a b v tp).tag = vTag v := rfl

/-- Live messages after an event: consumed ones removed, produced ones added. -/
def stepLive (live : Msg → Prop) (cons prod : List Msg) : Msg → Prop :=
  fun x => (live x ∧ x ∉ cons) ∨ x ∈ prod

/-- The static context of one run: the prepared module, the entry function and its module-level
check (the checked functions, their code offsets and the global code records). -/
structure Ctx where
  cfg : NearCfg
  p : Prepared
  fn : Nat
  M : ModOut
  g0 : Nat
  hM : checkModule cfg p fn = some M

def Ctx.R (X : Ctx) : Nat := X.cfg.regularOpCost
/-- Number of checked functions. -/
def Ctx.nf (X : Ctx) : Nat := X.M.fns.length
/-- Defined-function index of checked function `k`. -/
def Ctx.fnOf (X : Ctx) (k : Nat) : Nat := X.M.fns.getD k 0
def Ctx.pfOf (X : Ctx) (k : Nat) : PFunc := (X.p.funcs[X.fnOf k]?).getD default
def Ctx.ckOf (X : Ctx) (k : Nat) : CheckOut := X.M.cks.getD k default
/-- Global pc of local pc 0 of checked function `k`. -/
def Ctx.offOf (X : Ctx) (k : Nat) : Nat := X.M.offs.getD k 0
/-- The entry function (checked function 0). -/
def Ctx.pf (X : Ctx) : PFunc := X.pfOf 0
def Ctx.ck (X : Ctx) : CheckOut := X.ckOf 0
/-- Module-wide bound on the fee units of one instruction. -/
def Ctx.maxFee (X : Ctx) : Nat := X.M.maxFee

/-- The part of the machine a straight-line instruction does not touch: the current frame's stack
base and activation id, the caller frames, and the live channel messages of everything except the
operand stack and the current locals (callers' locals, call records, globals, memory words, dead
activations).  Families 2–4 refine `live` by their views. -/
structure Env where
  sb : Nat
  cid : Nat
  rest : List Frame
  live : Msg → Prop
  /-- the checked function (index into the module's function list) of the current frame -/
  k : Nat

/-- Channel space of the current activation's locals. -/
def Env.lsp (E : Env) : Nat := 16 + E.cid

/-- Spec label heights are absolute; the checker's are relative to the frame base. -/
def shiftLabels (sb : Nat) (ls : List Label) : List Label := ls.map fun l => { l with height := l.height + sb }

@[simp] theorem shiftLabels_zero (ls : List Label) : shiftLabels 0 ls = ls := by
  simp [shiftLabels]

/-! ## Linear memory as channel messages (space 3, one message per touched byte) -/

/-- A memory message: byte `x` at address `a`, produced at time `tp`. -/
def encB (a x tp : Nat) : Msg := ⟨3, a, 0, x, 0, 0, 0, tp⟩

/-- The touched bytes `T` of the memory of `s`, with producer times `tpm`. -/
def memView (T : List Nat) (s : St) (tpm : Nat → Nat) : List Msg :=
  T.map fun a => encB a (readByte s a).toNat (tpm a)

theorem mem_memView {x : Msg} {T : List Nat} {s : St} {tpm : Nat → Nat} :
    x ∈ memView T s tpm ↔ ∃ a ∈ T, x = encB a (readByte s a).toNat (tpm a) := by
  simp only [memView, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

/-- The globals as channel messages (space 2, slot = global index), producer times `tpg`. -/
def globView (gs : Array Val) (tpg : Nat → Nat) : List Msg :=
  (List.range gs.size).map fun g => enc 2 g (gs[g]?.getD default) (tpg g)

theorem mem_globView {x : Msg} {gs : Array Val} {tpg : Nat → Nat} :
    x ∈ globView gs tpg ↔ ∃ g, g < gs.size ∧ x = enc 2 g (gs[g]?.getD default) (tpg g) := by
  simp only [globView, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩

/-- The heap part of the outer live set: every page has `pageSize` bytes, and the space-3 messages
of `E.live` are exactly one message per touched byte `a ∈ T` (in bounds), carrying the current
byte, produced before `t`.  `T` is fixed for the whole run (the MEMINIT rows). -/
structure HeapOK (E : Env) (s : St) (t : Nat) : Prop where
  pages : PagesOK s
  mem : ∃ (T : List Nat) (tpm : Nat → Nat), T.Nodup ∧ (∀ a ∈ T, a < memBytes s) ∧ (∀ a ∈ T, tpm a < t) ∧
    ∀ x, x.space = 3 → (E.live x ↔ x ∈ memView T s tpm)
  /-- The globals (space 2): numeric, one live message each, produced before `t`. -/
  glob : ∃ (tpg : Nat → Nat), (∀ g, g < s.globals.size → tpg g < t ∧ isNum (s.globals[g]?.getD default)) ∧
    ∀ x, x.space = 2 → (E.live x ↔ x ∈ globView s.globals tpg)

theorem readByte_congr {s s' : St} (h : s'.pages = s.pages) (a : Nat) : readByte s' a = readByte s a := by
  simp only [readByte, h]

theorem memBytes_congr {s s' : St} (h : s'.pages = s.pages) : memBytes s' = memBytes s := by
  simp only [memBytes, h]

theorem HeapOK.mono {E : Env} {s s' : St} {t t' : Nat} (H : HeapOK E s t) (hpg : s'.pages = s.pages)
    (hgl : s'.globals = s.globals) (ht : t ≤ t') : HeapOK E s' t' := by
  obtain ⟨T, tpm, hnd, hlt, htp, hv⟩ := H.mem
  obtain ⟨tpg, hg, hgv⟩ := H.glob
  refine ⟨fun i h => by have := H.pages i (by rw [← hpg]; exact h); simpa only [hpg] using this,
    ⟨T, tpm, hnd, fun a ha => by rw [memBytes_congr hpg]; exact hlt a ha, fun a ha => by have := htp a ha; omega,
    fun x hx => ?_⟩, ⟨tpg, fun g h => ?_, fun x hx => ?_⟩⟩
  · rw [hv x hx]
    simp only [memView, readByte_congr hpg]
  · rw [hgl] at h ⊢; have := hg g h; exact ⟨by omega, this.2⟩
  · rw [hgv x hx, hgl]

/-! ## Calls: the caller chain and the stack budget -/

/-- A saved caller context: its checked function, frame base, activation id, locals producer
times, and the producer time of the call record. -/
structure Saved where
  k : Nat
  sb : Nat
  cid : Nat
  tpl : Nat → Nat
  tpc : Nat

/-- Call record of activation `c` (space 4): return pc (global), the caller's `sb` and `cid`, and
the callee's stack charge. -/
def callMsg (c retpc sb cid charge tp : Nat) : Msg := ⟨4, c, 0, retpc, sb, cid, charge, tp⟩

/-- The stack-budget register (space 5, slot 0): the spec's `stackRem` as two 16-bit limbs. -/
def budMsg (rem tp : Nat) : Msg := ⟨5, 0, 0, rem % 65536, rem / 65536, 0, 0, tp⟩

/-- The caller frames below the current frame (activation `cid`, base `sb`, function `k`). -/
def Chain (X : Ctx) (t : Nat) : Nat → Nat → Nat → List Frame → List Saved → Prop
  | cid, sb, _, [], [] => cid = 0 ∧ sb = 0
  | cid, sb, k, fc :: rest, c :: sv =>
      c.k < X.nf ∧ fc.fn = X.fnOf c.k ∧ fc.base = c.sb ∧ c.sb ≤ sb ∧ c.cid < cid ∧ c.tpc < t ∧
      fc.pc < (X.pfOf c.k).code.size ∧
      (∃ ls, (X.ckOf c.k).labels[fc.pc]? = some ls ∧ fc.labels = shiftLabels c.sb ls) ∧
      (X.ckOf c.k).heights[fc.pc]? = some (sb - c.sb + (X.pfOf k).type.results.size) ∧
      fc.locals.size = (X.pfOf c.k).type.params.size + (X.pfOf c.k).locals.size ∧
      (∀ j, j < fc.locals.size → isNum (fc.locals[j]?.getD default) ∧ c.tpl j < t) ∧
      c.sb < 2 ^ 28 ∧
      Chain X t c.cid c.sb c.k rest sv
  | _, _, _, _, _ => False

/-- The live messages of the caller chain: one call record and the locals of each caller. -/
def chainMsgs (X : Ctx) : Nat → Nat → List Frame → List Saved → Msg → Prop
  | cid, k, fc :: rest, c :: sv, x =>
      x = callMsg cid (X.offOf c.k + fc.pc) c.sb c.cid (X.pfOf k).stackCharge c.tpc ∨
      x ∈ localView (16 + c.cid) fc.locals c.tpl ∨ chainMsgs X c.cid c.k rest sv x
  | _, _, _, _, _ => False

/-- The stack charges of the pending calls along the chain (callee of each saved caller). -/
def chainCharge (X : Ctx) : Nat → List Saved → Nat
  | _, [] => 0
  | k, c :: sv => (X.pfOf k).stackCharge + chainCharge X c.k sv

/-- A locals space of a returned activation (`16 + c`, `c < t`, not an active activation). -/
def deadSp (t cid : Nat) (sv : List Saved) (x : Msg) : Prop :=
  16 ≤ x.space ∧ x.space < 16 + t ∧ x.space ≠ 16 + cid ∧ ∀ c ∈ sv, x.space ≠ 16 + c.cid

/-- The call part of the outer live set: the caller chain's messages are live, every live
message in space 4 or `≥ 16` is a chain message or in a dead locals space, and the stack budget is
exactly one live register message. -/
structure CallsOK (X : Ctx) (E : Env) (s : St) (t : Nat) : Prop where
  cidLtT : E.cid < t
  chain : ∃ sv, Chain X t E.cid E.sb E.k E.rest sv ∧
    (∀ x, chainMsgs X E.cid E.k E.rest sv x → E.live x) ∧
    (∀ x, E.live x → (x.space = 4 ∨ 16 ≤ x.space) → chainMsgs X E.cid E.k E.rest sv x ∨ deadSp t E.cid sv x) ∧
    s.stackRem + chainCharge X E.k sv < 2 ^ 30
  budget : ∃ tpb, tpb < t ∧ ∀ x, x.space = 5 → (E.live x ↔ x = budMsg s.stackRem tpb)

theorem Chain.mono {X : Ctx} {t t' : Nat} (ht : t ≤ t') :
    ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved}, Chain X t cid sb k rest sv → Chain X t' cid sb k rest sv
  | _, _, _, [], [], h => h
  | _, _, _, _ :: _, _ :: _, h => by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
    exact ⟨a1, a2, a3, a4, a5, by omega, a7, a8, a9, a10, fun j hj => ⟨(a11 j hj).1, by have := (a11 j hj).2; omega⟩,
      a12, Chain.mono ht a13⟩
  | _, _, _, [], _ :: _, h => h.elim
  | _, _, _, _ :: _, [], h => h.elim

/-- `CallsOK` survives a step that keeps the frame environment's call part, the stack budget and
the activation (only later times). -/
theorem CallsOK.mono {X : Ctx} {E E' : Env} {s s' : St} {t t' : Nat} (C : CallsOK X E s t) (ht : t ≤ t')
    (hsb : E'.sb = E.sb) (hcid : E'.cid = E.cid) (hk : E'.k = E.k) (hrest : E'.rest = E.rest)
    (hlive : ∀ x, (x.space = 4 ∨ x.space = 5 ∨ 16 ≤ x.space) → (E'.live x ↔ E.live x))
    (hrem : s'.stackRem = s.stackRem) : CallsOK X E' s' t' := by
  obtain ⟨sv, hc, hin, hout, hrl⟩ := C.chain
  obtain ⟨tpb, htpb, hb⟩ := C.budget
  have chainSp : ∀ {cid k : Nat} {rest : List Frame} {sv : List Saved} {x : Msg}, chainMsgs X cid k rest sv x →
      x.space = 4 ∨ 16 ≤ x.space := by
    intro cid k rest sv x h
    induction rest generalizing cid k sv with
    | nil => cases sv <;> simp [chainMsgs] at h
    | cons fc rest ih =>
      cases sv with
      | nil => simp [chainMsgs] at h
      | cons c sv =>
        rcases h with rfl | h | h
        · exact Or.inl rfl
        · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; right; simp [enc]
        · exact ih h
  refine ⟨by rw [hcid]; have := C.cidLtT; omega, ⟨sv, ?_, fun x h => ?_, fun x h hs => ?_, by rw [hrem, hk]; exact hrl⟩,
    ⟨tpb, by omega, fun x hx => by rw [hlive x (Or.inr (Or.inl hx)), hrem]; exact hb x hx⟩⟩
  · rw [hcid, hsb, hk, hrest]; exact Chain.mono ht hc
  · rw [hcid, hk, hrest] at h
    have hs := chainSp h
    rw [hlive x (hs.elim Or.inl (fun h => Or.inr (Or.inr h)))]
    exact hin x h
  · rw [hlive x (hs.elim Or.inl (fun h => Or.inr (Or.inr h)))] at h
    rw [hcid, hk, hrest]
    rcases hout x h hs with h1 | ⟨d1, d2, d3, d4⟩
    · exact Or.inl h1
    · exact Or.inr ⟨d1, by omega, d3, d4⟩

/-- **The simulation relation** between a spec state and the AIR view at time `t` (design note:
results/pq-wasm-base/README.md §10).

`S_seg` and `segb` delimit the current **gas segment** (JOIN-INTERFACE.md §4.2a): the instruction
counter at the last host boundary and the budget the state side fixed there.  Between host calls
the budget satisfies `R · (S − S_seg) + g = segb`; a host call resynchronises `g := remaining` and
starts a new segment (`S_seg := S`, `segb := g_after`).  With `S_seg = 0`, `segb = g0` this is the
original invariant `R · S + g = g0`, recovered by `RelW.gas_from_zero`. -/
structure RelW (X : Ctx) (E : Env) (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat)
    (live : Msg → Prop) (S_seg segb : Nat) : Prop where
  frames : s.frames = f :: E.rest
  kLt : E.k < X.nf
  fn : f.fn = X.fnOf E.k
  pcEq : f.pc = pc
  pcLt : pc < (X.pfOf E.k).code.size
  labels : ∃ ls, (X.ckOf E.k).labels[pc]? = some ls ∧ f.labels = shiftLabels E.sb ls
  base : f.base = E.sb
  sbLe : E.sb ≤ s.stack.size
  height : (X.ckOf E.k).heights[pc]? = some (s.stack.size - E.sb)
  nloc : f.locals.size = (X.pfOf E.k).type.params.size + (X.pfOf E.k).locals.size
  /-- The per-segment gas invariant: `S_seg ≤ S` and `R · (S − S_seg) + g = segb`. -/
  gas : X.R * (S - S_seg) + s.gas.g = segb
  /-- The segment starts at or before the current instruction counter. -/
  segLt : S_seg ≤ S
  /-- The segment budget is a 64-bit budget (the HOSTR response limbs bound it). -/
  segbLt : segb < 2 ^ 64
  numS : ∀ i, i < s.stack.size → isNum (s.stack[i]?.getD default)
  numL : ∀ j, j < f.locals.size → isNum (f.locals[j]?.getD default)
  tpsLt : ∀ i, i < s.stack.size → tps i < t
  tplLt : ∀ j, j < f.locals.size → tpl j < t
  envSep : ∀ x, E.live x → x.space ≠ 0 ∧ x.space ≠ E.lsp
  /-- Activation id 0 is the entry frame: no caller frames, stack base 0. -/
  entry : E.cid = 0 → E.rest = [] ∧ E.sb = 0
  /-- Field-size bounds on the frame fields (the AIR carries `sb`, `cid` as field elements). -/
  sbLt : E.sb < 2 ^ 28
  cidLt : E.cid < 2 ^ 28
  /-- The memory (space 3) part of the outer live set matches the spec memory. -/
  heap : HeapOK E s t
  /-- The caller chain and the stack budget. -/
  calls : CallsOK X E s t
  live : ∀ x, live x ↔ x ∈ stackView s.stack tps ∨ x ∈ localView E.lsp f.locals tpl ∨ E.live x

/-- The relation with the frame data existential; `sb`/`cid` are the AIR state's, `k` the checked
function and `pc` the local pc (the AIR's global pc is `X.offOf k + pc`).  `S_seg`/`segb` delimit the
current gas segment (see `RelW`). -/
def Rel (X : Ctx) (s : St) (t k pc S sb cid : Nat) (live : Msg → Prop) (S_seg segb : Nat) : Prop :=
  ∃ E f tps tpl, E.sb = sb ∧ E.cid = cid ∧ E.k = k ∧ RelW X E s f tps tpl t pc S live S_seg segb

/-- **The old global gas invariant** in the no-host case (`S_seg = 0`, `segb = g0`): this is exactly
`wasm_base_sound`'s conclusion, and it is the specialisation of the per-segment invariant at the
start of a run. -/
theorem RelW.gas_global {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live 0 X.g0) : X.R * S + s.gas.g = X.g0 := by
  simpa using R.gas

/-- A `RelW` whose gas field is the old global form `R · S + g = g0` is a `RelW` at the initial
segment `(0, g0)`.  This is how constructions written against the original invariant (e.g. the entry
relation) feed the generalised one. -/
theorem RelW.of_global {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (h : RelW X E s f tps tpl t pc S live 0 X.g0) : X.R * S + s.gas.g = X.g0 :=
  h.gas_global

theorem Rel.gas_global {X : Ctx} {s : St} {t k pc S sb cid : Nat} {live : Msg → Prop}
    (R : Rel X s t k pc S sb cid live 0 X.g0) : X.R * S + s.gas.g = X.g0 := by
  obtain ⟨E, f, tps, tpl, -, -, -, h⟩ := R
  exact h.gas_global

/-- The segment's remaining budget covers this instruction's gas (the charge succeeds).  With
`S_seg = 0`, `segb = g0` this is the old `R · (S + fee) ≤ g0`. -/
theorem RelW.charge_ok {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb fee : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    (hg : X.R * (S + fee - S_seg) ≤ segb) : X.R * fee ≤ s.gas.g := by
  have h1 := R.gas
  have h2 := R.segLt
  have hs := R.segLt
  have hm : X.R * (S + fee - S_seg) = X.R * (S - S_seg) + X.R * fee := by
    rw [← Nat.mul_add]; congr 1; omega
  omega

/-- A step that keeps the segment (`S_seg`, `segb` fixed) while `S` advances by `fee`. -/
theorem RelW.step_gas {X : Ctx} {E : Env} {s s' : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb fee : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    (hg : X.R * (S + fee - S_seg) ≤ segb) (hgg : s'.gas.g = s.gas.g - X.R * fee) :
    X.R * (S + fee - S_seg) + s'.gas.g = segb := by
  rw [hgg]
  have h1 := R.gas
  have h2 := R.charge_ok hg
  have hs := R.segLt
  have hm : X.R * (S + fee - S_seg) = X.R * (S - S_seg) + X.R * fee := by
    rw [← Nat.mul_add]; congr 1; omega
  omega

/-- Splitting the gas advance of one step at a segment start `S_seg ≤ S`. -/
theorem seg_mul {R S S_seg fee p : Nat} (h : S_seg ≤ S) :
    R * (S + (fee + p) - S_seg) = R * (S - S_seg) + (R * fee + R * p) := by
  have harg : S + (fee + p) - S_seg = (S - S_seg) + (fee + p) := by omega
  rw [harg, Nat.mul_add, Nat.mul_add]

/-- The gas arithmetic of a `call`: advancing `S` by `fee + p` while the state charges
`X.R · fee + pro` (with `pro = X.R · p`) keeps the segment invariant. -/
theorem RelW.gas_call {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb fee p pro : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb)
    (hpro : X.R * p = pro) (hle : X.R * fee + pro ≤ s.gas.g) :
    X.R * (S + (fee + p) - S_seg) + (s.gas.g - X.R * fee - pro) = segb := by
  have harg : S + (fee + p) - S_seg = (S - S_seg) + (fee + p) := by
    have := R.segLt; omega
  have ha : X.R * (S + (fee + p) - S_seg) = X.R * (S - S_seg) + X.R * fee + X.R * p := by
    rw [harg, Nat.mul_add, Nat.mul_add, hpro]; omega
  rw [ha]
  have h1 := R.gas
  omega

/-- A live stack message at slot `i` is the encoding of stack entry `i`. -/
theorem RelW.stack_msg {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb) {x : Msg} (hx : live x)
    (hs : x.space = 0) (hi : x.slot < s.stack.size) :
    x = enc 0 x.slot (s.stack[x.slot]?.getD default) (tps x.slot) := by
  rcases (R.live x).mp hx with h | h | h
  · obtain ⟨i, hi', rfl⟩ := mem_stackView.mp h
    rfl
  · obtain ⟨j, _, rfl⟩ := mem_localView.mp h
    exfalso; simp only [enc_space, Env.lsp] at hs; omega
  · exact absurd hs (R.envSep x h).1

theorem RelW.local_msg {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {S_seg segb : Nat} (R : RelW X E s f tps tpl t pc S live S_seg segb) {x : Msg} (hx : live x)
    (hs : x.space = E.lsp) (hj : x.slot < f.locals.size) :
    x = enc E.lsp x.slot (f.locals[x.slot]?.getD default) (tpl x.slot) := by
  rcases (R.live x).mp hx with h | h | h
  · obtain ⟨i, _, rfl⟩ := mem_stackView.mp h
    exfalso; simp only [enc_space, Env.lsp] at hs; omega
  · obtain ⟨j, hj', rfl⟩ := mem_localView.mp h
    rfl
  · exact absurd hs (R.envSep x h).2

/-- **General view update.** The new stack keeps the first `n - k` entries and appends new ones
(producer time `t`); the locals change at most at index `J` (fresh producer time `t`). -/
theorem view_update {stk stk' locs locs' : Array Val} {tps tpl : Nat → Nat} {t k sp : Nat} (hsp : sp ≠ 0)
    (J : Option Nat) (hk : k ≤ stk.size)
    (keep : ∀ i, i < stk.size - k → stk'[i]? = stk[i]?) (hsz : stk.size - k ≤ stk'.size)
    (lsz : locs'.size = locs.size) (lkeep : ∀ j, some j ≠ J → locs'[j]? = locs[j]?)
    (hJ : ∀ j, J = some j → j < locs.size)
    (tpsLt : ∀ i, i < stk.size → tps i < t) (tplLt : ∀ j, j < locs.size → tpl j < t)
    (x : Msg) :
    (x ∈ stackView stk' (fun i => if i < stk.size - k then tps i else t) ∨
      x ∈ localView sp locs' (fun j => if some j = J then t else tpl j)) ↔
      ((x ∈ stackView stk tps ∨ x ∈ localView sp locs tpl) ∧
        x ∉ ((List.range k).map fun d => enc 0 (stk.size - k + d) (stk[stk.size - k + d]?.getD default)
          (tps (stk.size - k + d))) ++ J.toList.map (fun j => enc sp j (locs[j]?.getD default) (tpl j))) ∨
      x ∈ ((List.range (stk'.size - (stk.size - k))).map fun d =>
        enc 0 (stk.size - k + d) (stk'[stk.size - k + d]?.getD default) t) ++
        J.toList.map (fun j => enc sp j (locs'[j]?.getD default) t) := by
  simp only [mem_stackView, mem_localView, List.mem_append, List.mem_map, List.mem_range,
    Option.mem_toList]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · by_cases hlt : i < stk.size - k
      · left
        refine ⟨Or.inl ⟨i, by omega, ?_⟩, ?_⟩
        · simp [hlt, keep i hlt]
        · rintro (⟨d, hd, he⟩ | ⟨j, _, he⟩)
          · have := congrArg Msg.slot he; simp at this; omega
          · have := congrArg Msg.space he; simp at this; omega
      · right; left
        refine ⟨i - (stk.size - k), ?_, ?_⟩
        · exact Nat.sub_lt_sub_right (Nat.le_of_not_lt hlt) hi
        · have e : stk.size - k + (i - (stk.size - k)) = i := by omega
          simp only [hlt, ite_false, e]
    · by_cases hj' : some j = J
      · right; right
        exact ⟨j, hj'.symm, by simp [hj']⟩
      · left
        refine ⟨Or.inr ⟨j, by omega, ?_⟩, ?_⟩
        · simp [hj', lkeep j hj']
        · rintro (⟨d, hd, he⟩ | ⟨j0, hj0, he⟩)
          · have := congrArg Msg.space he; simp at this; omega
          · have := congrArg Msg.slot he; simp at this; subst this; exact hj' hj0.symm
  · rintro (⟨(⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩), hn⟩ | (⟨d, hd, rfl⟩ | ⟨j0, hj0, rfl⟩))
    · have hlt : i < stk.size - k := by
        refine Classical.byContradiction fun hc => hn (Or.inl ⟨i - (stk.size - k), by omega, ?_⟩)
        have e : stk.size - k + (i - (stk.size - k)) = i := by omega
        rw [e]
      left; exact ⟨i, by omega, by simp [hlt, keep i hlt]⟩
    · have hjJ : some j ≠ J := by
        intro hc; exact hn (Or.inr ⟨j, hc.symm, rfl⟩)
      right; exact ⟨j, by omega, by simp [hjJ, lkeep j hjJ]⟩
    · left; refine ⟨stk.size - k + d, by omega, ?_⟩
      rw [if_neg (by omega)]
    · right; exact ⟨j0, by rw [lsz]; exact hJ j0 hj0, by simp [hj0]⟩

end WasmBase
