import WasmBase.Main.SegRows
import StateM5a.StateView
import NearSpecV3.E2E.View

/-!
# WasmBase.Main.WasmView — the Wasm component `wasmD` of lane E's `ViewImpl` (E2E M4b, sub-lane V)

`NearSpecV3.E2E.Bnd.ViewImpl` has one commitment per configuration component; the Wasm component
is `wasmD : WmV → Option WasmBnd` (`WmV = Option (CallArgs × CallConf)`), and
`viewImpl_binding_bad` needs `Coll V.wasmD → Bad`.  This file gives a **concrete** `wasmD` built
from the segment AIR's single boundary digest (`ctxDigest = cutDigest (cutView X s)`,
`Main/SegRows.lean`) and its SHA-384 memory Merkle root, and proves it binding modulo `bdigest`
collisions.  Pattern and reused lemmas: lane B's `StateM5a.StateView` (`nodeH`, `merkle_binding`,
`sha384_coll`, `root_some`, `Merkle.root`).

## The record (`wasmD none = none`; `wasmD (some w) = some (wasmBnd P w)`)

`airOf P w` selects the **AIR branch**: `w = (q, .ent p k (.cont s) n)`, `P.ctxOf q p k = some X`,
`InDom X s` and `n < 2^64` (classical `if`); otherwise the **fallback**.  With `f` the top frame
(`s.frames.headD default`) and `fd = bdigest (cutBytes (cutView X s))`:

| `WasmBnd` field | AIR branch (`airBnd`) | fallback (`fbBnd`) |
|---|---|---|
| `pc` | `gpc X f = X.offOf (X.kOf f.fn) + f.pc` (the AIR's global pc) | `0` |
| `sp` | `f.base` (the AIR's public `sb`) | `0` |
| `stackRem` | `s.stackRem` | `0` |
| `fuel` | `n` | `0` |
| `framesDigest` | `fd` = the AIR's `ctxDigest` truncated to 42 bytes | `bdigest []` |
| `memRoot` | `(memRootOf s).take 42` | `bdigest []` |
| `memPages` | `s.pages.size` | `0` |
| `globalsDigest`, `registersDigest` | `fd` (derived: one digest covers stack, locals, call records, globals, budget, registers) | `bdigest []` |
| `vmCtxDigest` | `bdigest (P.encRest (.air q p k (blank s)))` | `bdigest (P.encRest (.other w))` |
| `promisesDigest` | `bdigest []` (promises are in the remainder) | `bdigest []` |
| `codeRoot`, `funcRoot` | `P.codeRootOf q p`, `P.funcRootOf q p` | `bdigest []` |

`blank s` empties `stack`, `frames`, `pages`, `globals`, sets `stackRem := 0` and keeps the
register **ids in order** with their data emptied (`regIds`): the view is a *set* of messages and
cannot carry the register file's insertion order (`regSetH` appends), so the order goes in the
remainder.  `s.gas` stays whole in the remainder (a `WasmBnd` gas field is for the lane lead to
propose).  No change to `BndRec`/`WasmBnd` is needed for binding; `t`, `S`, the gas segment
`(S_seg, segb)`, the depth `D`, `nblk`, `halted` are AIR-internal or derived (`D`, `nblk` from
`memPages`).

**The memory tree** (`memRootOf`, exactly `seg.rs` `Tree`): `nblk = 64 · pages` blocks of 1 KiB,
depth `d = bitlen (max nblk 2 − 1)` (`memDepth`, `≥ 1`, `nblk ≤ 2^d`: `nblk_le`), leaf `b < nblk`
= `sha384` of the 1024 bytes at addresses `1024 b + i`, `i = 0 … 1023`, **in address order**
(`blkBytes`; `seg.rs` `be_words` and `SegRows.beWord` load each 8-byte group big-endian, i.e. the
lowest address is the most significant byte, which is SHA-512's standard message-word loading, so
the leaf is the plain FIPS 180-4 SHA-384 of the byte string), leaves `≥ nblk` = `sha384 0¹⁰²⁴`,
node = `nodeH l r = sha384 (l48 ‖ r48)` (`node_block`: 96 bytes + standard padding).

## Proved here

* `memRoot_binding` — equal 42-byte memory roots of equal-size memories: every block's bytes are
  equal, or `Sha384Coll` (the root is an inner node, so a truncated-root collision is a `bdigest`
  collision; `merkle_binding` for the tree; a leaf collision is `sha384_coll`); `pages_eq` — equal
  blocks are equal pages (`PagesOK`).
* `reconstruct` (**the reconstruction lemma**) — `InDom X s → InDom X s' → cutView X s =
  cutView X s' →` same top-frame global pc and base, same register-id order `→ s.stack = s'.stack
  ∧ s.frames = s'.frames ∧ s.globals = s'.globals ∧ s.registers = s'.registers`.  Per space:
  0 (`stack_eq`), 2 (`globals_eq`), `16 + d` (`locals_eq`; `enc` is injective on numeric values,
  `enc_fields_inj`), 4 (`rec_xfer`: the record of activation `d` gives the caller's global pc and
  base; `nframes_eq`: the frame count is fixed by the record slots), the top frame from `pc`/`sp`
  (`frm_top`), `(fn, pc)` from the global pc (`off_decode`, from the checker's `layoutOk`, and
  `fnOf_kOf`), labels from `FrameOK` (`frame_eq`, `frames_eq`), 6 (`regs_eq`: length and byte
  messages, `Register.byteSlot_inj`, distinct ids).
* `wasmBnd_binding` / **`wasmD_binding : Coll (wasmD P) → Sha384Coll`**, and
  **`viewImpl_hwasm`**: for any `V : ViewImpl` with `V.wasmD = wasmD P`, `Coll V.wasmD → Bad`
  given `Sha384Coll → Bad` (the `hwasm` premise of `viewImpl_binding_bad`).
* `wasmD_air` — on the AIR branch, `framesDigest = (cutDigest (cutView X s)).take 42`,
  `memRoot = (memRootOf s).take 42`, `pc`, `sp`, `stackRem`, `fuel`, `memPages` as in the table:
  the equalities segment soundness uses to say the AIR's public `ctxDigest`/`memRoot` are this
  view's.
* `wasmBnd_ok` — every record satisfies `WasmBnd.codec.ok` (counters `< 2^64`, digests 42 bytes),
  so the Wasm part never breaks `BndRec.WF`.

## Parameters (`WasmViewParams`)

* `ctxOf : CallArgs → Prepared → EntK → Option Ctx` — the static context of an entry (lane A/E).
* `codeRootOf`, `funcRootOf` with **`codeRoot_len`**, **`funcRoot_len`** (42 bytes); no binding
  obligation (`q`, `p` are in the remainder).
* `encRest : WRest → Bytes` with **`encRest_inj`** (lane E's `CallArgs`/`Prepared`/`EntK`/`St`
  encoders).

## The domain (`InDom X s`, plus `n < 2^64` in `airOf`)

`ne` (a frame is running), `wf` (every message of `cutView X s` is `MsgWF`: 7 fields `< 2^30`),
`frames` (`FrameOK` for every frame: `fn ∈ X.M.fns`, `pc < ` code size of `X.kOf fn`, labels
`= shiftLabels base ((X.ckOf (X.kOf fn)).labels[pc])`, numeric locals), `numS`/`numG` (numeric
stack and globals), `pages` (`PagesOK`), `regs` (`RegOK`: distinct register ids, data `< 2^24`
bytes), `lt64` (top global pc, base, `stackRem`, page count `< 2^64`).  All are facts of honest
cut states; deriving them from `RelW`/`Chain` needs, besides the cut facts listed at the end of
`SegRows.lean`: `X.M.fns.Nodup` (so `X.kOf f.fn` is `RelW`'s `E.k`; the binding itself does not
need it).  Note that `MsgWF` on space 6 bounds the slot `rid · 2^24 + i + 1 < 2^30`, i.e.
**register ids `< 64`**: a cut with a register id `≥ 64` (the spec allows any `u64` id) is outside
the AIR branch (it still binds, through the fallback).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedVariables false

namespace WasmBase.WasmView

open NearSpecV3.Wasm NearSpecV3.Wasm.CallCut
open NearSpecV3.E2E.Bnd (WasmBnd ViewImpl WmV Coll Sha384Coll bdigest sha384 sha384_length
  bdigest_length digestLen)
open StateM5a.StateView (nodeH merkle_binding sha384_coll root_some)
open StateM5a (Merkle.root Merkle.up)

/-! ## 1. The memory Merkle tree (as `seg.rs` `Tree` computes it) -/

/-- Number of 1 KiB blocks of the memory (`nblk = mem >> 10`, `mem = pages · 64 KiB`). -/
def nblkOf (s : St) : Nat := s.pages.size * 64

/-- Tree depth `d = bitlen (max nblk 2 − 1)` (`usize::BITS − leading_zeros`), so `2^d ≥ nblk`. -/
def memDepth (s : St) : Nat := Nat.log2 (max (nblkOf s) 2 - 1) + 1

/-- The 1024 bytes of block `b`, in address order (byte `1024 b + i` is message byte `i`). -/
def blkBytes (s : St) (b : Nat) : ArenaCore.Bytes :=
  (List.range 1024).map fun i => readByte s (1024 * b + i)

/-- The zero block's leaf (leaves `≥ nblk`). -/
def zleaf : ArenaCore.Bytes := sha384 (List.replicate 1024 0)

/-- The `2^d` leaves: SHA-384 of each block's bytes, then zero-block leaves. -/
def memLeaves (s : St) : List ArenaCore.Bytes :=
  (List.range (nblkOf s)).map (fun b => sha384 (blkBytes s b)) ++
    List.replicate (2 ^ memDepth s - nblkOf s) zleaf

/-- **The memory root** (48 bytes): `Merkle.root nodeH d (memLeaves s)`, `nodeH l r = sha384 (l ‖ r)`. -/
def memRootOf (s : St) : ArenaCore.Bytes := (Merkle.root nodeH (memDepth s) (memLeaves s)).getD []

theorem nblk_le (s : St) : nblkOf s ≤ 2 ^ memDepth s := by
  have := @Nat.lt_log2_self (max (nblkOf s) 2 - 1)
  simp only [memDepth]
  omega

theorem memLeaves_length (s : St) : (memLeaves s).length = 2 ^ memDepth s := by
  have := nblk_le s
  simp only [memLeaves, List.length_append, List.length_map, List.length_range,
    List.length_replicate]
  omega

theorem memLeaves_mem (s : St) : ∀ x ∈ memLeaves s, x.length = 48 := by
  intro x hx
  simp only [memLeaves, List.mem_append, List.mem_map, List.mem_replicate] at hx
  rcases hx with ⟨b, -, h⟩ | ⟨-, h⟩
  · rw [← h]; exact sha384_length _
  · rw [h]; exact sha384_length _

theorem up_mem_node : ∀ (l : List ArenaCore.Bytes) (x : ArenaCore.Bytes), x ∈ Merkle.up nodeH l →
    ∃ a b, x = nodeH a b
  | a :: b :: r, x, hx => by
    simp only [Merkle.up, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨a, b, rfl⟩
    · exact up_mem_node r x hx
  | [], x, hx => by simp [Merkle.up] at hx
  | [_], x, hx => by simp [Merkle.up] at hx

/-- A root is a leaf or an inner node. -/
theorem root_cases : ∀ (D : Nat) (l : List ArenaCore.Bytes) (x : ArenaCore.Bytes),
    Merkle.root nodeH D l = some x → x ∈ l ∨ ∃ a b, x = nodeH a b
  | 0, l, x, h => by
    match l, h with
    | [y], h =>
      simp only [Merkle.root, Option.some.injEq] at h
      exact .inl (by simp [h])
  | D + 1, l, x, h => by
    rcases root_cases D _ x h with h | h
    · exact .inr (up_mem_node l x h)
    · exact .inr h

/-- The root of a tree of depth `≥ 1` is an inner node. -/
theorem root_succ_node (D : Nat) (l : List ArenaCore.Bytes) (x : ArenaCore.Bytes)
    (h : Merkle.root nodeH (D + 1) l = some x) : ∃ a b, x = nodeH a b := by
  rcases root_cases D _ x h with h | h
  · exact up_mem_node l x h
  · exact h

/-- The memory root is an inner node (`memDepth ≥ 1`), i.e. a SHA-384 value. -/
theorem memRoot_sha (s : St) : ∃ m, Merkle.root nodeH (memDepth s) (memLeaves s) = some (sha384 m) := by
  obtain ⟨x, hx⟩ := root_some _ _ (memLeaves_length s)
  obtain ⟨a, b, rfl⟩ := root_succ_node _ _ x hx
  exact ⟨a ++ b, hx⟩

theorem memRootOf_take (s : St) : ∃ m, Merkle.root nodeH (memDepth s) (memLeaves s) = some (sha384 m) ∧
    (memRootOf s).take 42 = bdigest m := by
  obtain ⟨m, hm⟩ := memRoot_sha s
  exact ⟨m, hm, by simp only [memRootOf, hm, Option.getD_some, bdigest, digestLen]⟩

/-- **Memory root binding.** Equal 42-byte memory roots of two memories of the same size: every
block has the same bytes, or there is a `Sha384Coll`. -/
theorem memRoot_binding (s s' : St) (hn : s.pages.size = s'.pages.size)
    (h : (memRootOf s).take 42 = (memRootOf s').take 42) :
    (∀ b, b < nblkOf s → blkBytes s b = blkBytes s' b) ∨ Sha384Coll := by
  obtain ⟨m, hm, e⟩ := memRootOf_take s
  obtain ⟨m', hm', e'⟩ := memRootOf_take s'
  rw [e, e'] at h
  classical
  by_cases hmm : m = m'
  · subst hmm
    have hb : nblkOf s = nblkOf s' := by simp only [nblkOf, hn]
    have hd : memDepth s = memDepth s' := by simp only [memDepth, hb]
    have l1 := memLeaves_length s
    have l2 := memLeaves_length s'
    rw [hd] at l1 hm
    rcases merkle_binding _ _ _ l1 l2 (memLeaves_mem s) (memLeaves_mem s') (by rw [hm, hm']) with
      hl | hl
    · simp only [memLeaves] at hl
      obtain ⟨hl, -⟩ := List.append_inj hl (by simp [hb])
      rw [hb, List.map_inj_left] at hl
      by_cases hc : ∀ b, b < nblkOf s → blkBytes s b = blkBytes s' b
      · exact .inl hc
      · right
        obtain ⟨b, hb'⟩ := Classical.not_forall.mp hc
        have hbl : b < nblkOf s := Classical.byContradiction fun hn => hb' (fun h => absurd h hn)
        have hne : blkBytes s b ≠ blkBytes s' b := fun he => hb' (fun _ => he)
        exact sha384_coll hne (hl b (List.mem_range.2 (hb ▸ hbl)))
    · exact .inr hl
  · exact .inr ⟨m, m', hmm, h⟩

/-- In-bounds bytes of a well-formed memory are page bytes. -/
theorem readByte_page {s : St} {i j : Nat} (hi : i < s.pages.size)
    (hj : j < pageSize) : readByte s (i * pageSize + j) = (s.pages[i]'hi).get! j := by
  have hps : 0 < pageSize := by decide
  have e1 : (i * pageSize + j) / pageSize = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hps, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (i * pageSize + j) % pageSize = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [readByte, e1, e2, Array.getElem?_eq_getElem hi]

theorem ba_ext {a b : ByteArray} (hs : a.size = b.size) (h : ∀ j, j < a.size → a.get! j = b.get! j) :
    a = b := by
  obtain ⟨x⟩ := a
  obtain ⟨y⟩ := b
  simp only [ByteArray.size, ByteArray.get!] at hs h
  congr 1
  refine Array.ext hs fun j h1 h2 => ?_
  have := h j h1
  simp only [getElem!_pos x j h1, getElem!_pos y j h2] at this
  exact this

/-- **Equal blocks are equal pages** (memories of the same size, every page `pageSize` bytes). -/
theorem pages_eq {s s' : St} (hP : WasmBase.PagesOK s) (hP' : WasmBase.PagesOK s')
    (hn : s.pages.size = s'.pages.size) (hb : ∀ b, b < nblkOf s → blkBytes s b = blkBytes s' b) :
    s.pages = s'.pages := by
  refine Array.ext hn fun i h1 h2 => ba_ext (by rw [hP i h1, hP' i h2]) fun j hj => ?_
  rw [hP i h1] at hj
  rw [← readByte_page h1 hj, ← readByte_page h2 hj]
  have hps : pageSize = 1024 * 64 := rfl
  have hbl : (i * pageSize + j) / 1024 < nblkOf s := by
    simp only [nblkOf]; rw [hps] at hj ⊢; omega
  have e := congrArg (fun l => l[(i * pageSize + j) % 1024]?) (hb _ hbl)
  have hm : (i * pageSize + j) % 1024 < 1024 := Nat.mod_lt _ (by decide)
  simp only [blkBytes, List.getElem?_map, List.getElem?_range hm, Option.map_some,
    Option.some.injEq] at e
  rwa [Nat.div_add_mod] at e

/-! ## 2. The boundary messages of a state, per channel space -/

/-- The frame at depth `d` (entry frame at depth 0). -/
def frm (s : St) (d : Nat) : Frame := s.frames.reverse.getD d default

/-- The AIR's global pc of a frame. -/
def gpc (X : Ctx) (f : Frame) : Nat := X.offOf (X.kOf f.fn) + f.pc

/-- The stack charge of a frame's function (field 6 of its call record). -/
def chg (X : Ctx) (f : Frame) : Nat := ((X.p.funcs[f.fn]?).getD default).stackCharge

/-- An array of values as messages in space `sp` (producer times 0). -/
def arrView (sp : Nat) (a : Array Val) : List Msg :=
  (List.range a.size).map fun i => enc sp i (a[i]?.getD default) 0

theorem mem_arrView {sp : Nat} {a : Array Val} {x : Msg} :
    x ∈ arrView sp a ↔ ∃ i, i < a.size ∧ x = enc sp i (a[i]?.getD default) 0 := by
  simp only [arrView, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

/-- The record of activation `d ≥ 1`. -/
def recOf (X : Ctx) (s : St) (d : Nat) : Msg :=
  callMsg d (gpc X (frm s (d - 1))) (frm s (d - 1)).base (d - 1) (chg X (frm s d)) 0

theorem frameMsgs_eq (X : Ctx) (s : St) (d : Nat) :
    frameMsgs X s.frames.reverse d =
      arrView (16 + d) (frm s d).locals ++ (if d = 0 then [] else [recOf X s d]) := rfl

theorem cutMsgs_eq (X : Ctx) (s : St) :
    cutMsgs X s = arrView 0 s.stack ++
      (List.range s.frames.length).flatMap (fun d =>
        arrView (16 + d) (frm s d).locals ++ (if d = 0 then [] else [recOf X s d])) ++
      arrView 2 s.globals ++ [budMsg s.stackRem 0] ++ Register.view s.registers (fun _ => 0) := rfl

/-- **The messages of `cutMsgs`.** -/
theorem mem_cutMsgs {X : Ctx} {s : St} {x : Msg} :
    x ∈ cutMsgs X s ↔ x ∈ arrView 0 s.stack ∨
      (∃ d, d < s.frames.length ∧ x ∈ arrView (16 + d) (frm s d).locals) ∨
      (∃ d, 0 < d ∧ d < s.frames.length ∧ x = recOf X s d) ∨
      x ∈ arrView 2 s.globals ∨ x = budMsg s.stackRem 0 ∨ x ∈ Register.view s.registers (fun _ => 0) := by
  rw [cutMsgs_eq]
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_singleton, or_assoc]
  constructor
  · rintro (h | ⟨d, hd, h | h⟩ | h | h | h)
    · exact .inl h
    · exact .inr (.inl ⟨d, hd, h⟩)
    · split at h
      · simp at h
      · simp only [List.mem_singleton] at h
        exact .inr (.inr (.inl ⟨d, by omega, hd, h⟩))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr (.inl h))))
    · exact .inr (.inr (.inr (.inr (.inr h))))
  · rintro (h | ⟨d, hd, h⟩ | ⟨d, h0, hd, h⟩ | h | h | h)
    · exact .inl h
    · exact .inr (.inl ⟨d, hd, .inl h⟩)
    · refine .inr (.inl ⟨d, hd, .inr ?_⟩)
      split
      · omega
      · exact List.mem_singleton.2 h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))

theorem arrView_space {sp : Nat} {a : Array Val} {x : Msg} (h : x ∈ arrView sp a) : x.space = sp := by
  obtain ⟨i, -, rfl⟩ := mem_arrView.1 h; rfl

theorem regView_space {regs : Array (Nat × ByteArray)} {x : Msg}
    (h : x ∈ Register.view regs (fun _ => 0)) : x.space = 6 := by
  obtain ⟨rid, d, -, h⟩ := Register.mem_view.1 h
  rcases Register.mem_regMsgs.1 h with rfl | ⟨i, -, rfl⟩ <;> rfl

/-- Space 0 of the boundary messages is the operand stack. -/
theorem sp_stack {X : Ctx} {s : St} {x : Msg} (h : x ∈ cutMsgs X s) (hs : x.space = 0) :
    x ∈ arrView 0 s.stack := by
  rcases mem_cutMsgs.1 h with h | ⟨d, -, h⟩ | ⟨d, -, -, rfl⟩ | h | rfl | h
  · exact h
  · have := arrView_space h; omega
  · exact absurd hs (by simp [recOf, callMsg] <;> omega)
  · have := arrView_space h; omega
  · exact absurd hs (by simp [budMsg] <;> omega)
  · have := regView_space h; omega

/-- Space 2 is the globals. -/
theorem sp_glob {X : Ctx} {s : St} {x : Msg} (h : x ∈ cutMsgs X s) (hs : x.space = 2) :
    x ∈ arrView 2 s.globals := by
  rcases mem_cutMsgs.1 h with h | ⟨d, -, h⟩ | ⟨d, -, -, rfl⟩ | h | rfl | h
  · have := arrView_space h; omega
  · have := arrView_space h; omega
  · exact absurd hs (by simp [recOf, callMsg] <;> omega)
  · exact h
  · exact absurd hs (by simp [budMsg] <;> omega)
  · have := regView_space h; omega

/-- Space `16 + d` is the locals of the frame at depth `d`. -/
theorem sp_loc {X : Ctx} {s : St} {x : Msg} {d : Nat} (h : x ∈ cutMsgs X s) (hs : x.space = 16 + d) :
    d < s.frames.length ∧ x ∈ arrView (16 + d) (frm s d).locals := by
  rcases mem_cutMsgs.1 h with h | ⟨d', hd, h⟩ | ⟨d', -, -, rfl⟩ | h | rfl | h
  · have := arrView_space h; omega
  · have := arrView_space h
    have e : d' = d := by omega
    subst e; exact ⟨hd, h⟩
  · exact absurd hs (by simp [recOf, callMsg] <;> omega)
  · have := arrView_space h; omega
  · exact absurd hs (by simp [budMsg] <;> omega)
  · have := regView_space h; omega

/-- Space 4 is the call records. -/
theorem sp_rec {X : Ctx} {s : St} {x : Msg} (h : x ∈ cutMsgs X s) (hs : x.space = 4) :
    ∃ d, 0 < d ∧ d < s.frames.length ∧ x = recOf X s d := by
  rcases mem_cutMsgs.1 h with h | ⟨d', hd, h⟩ | h | h | rfl | h
  · have := arrView_space h; omega
  · have := arrView_space h; omega
  · exact h
  · have := arrView_space h; omega
  · exact absurd hs (by simp [budMsg] <;> omega)
  · have := regView_space h; omega

/-- Space 6 is the registers. -/
theorem sp_reg {X : Ctx} {s : St} {x : Msg} (h : x ∈ cutMsgs X s) (hs : x.space = 6) :
    x ∈ Register.view s.registers (fun _ => 0) := by
  rcases mem_cutMsgs.1 h with h | ⟨d', hd, h⟩ | ⟨d', -, -, rfl⟩ | h | rfl | h
  · have := arrView_space h; omega
  · have := arrView_space h; omega
  · exact absurd hs (by simp [recOf, callMsg] <;> omega)
  · have := arrView_space h; omega
  · exact absurd hs (by simp [budMsg] <;> omega)
  · exact h

/-! ## 3. Values and arrays from their messages -/

/-- The hashed fields of a numeric value's message determine space, slot and value. -/
theorem enc_fields_inj {sp sp' i j tp tp' : Nat} {v v' : Val} (hv : isNum v) (hv' : isNum v')
    (h : fieldsOf (enc sp i v tp) = fieldsOf (enc sp' j v' tp')) : sp = sp' ∧ i = j ∧ v = v' := by
  have e1 := enc_val hv sp i tp
  have e2 := enc_val hv' sp' j tp'
  simp only [fieldsOf, enc, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, ?_⟩
  have hn : vNum v = vNum v' := by
    rw [← e1, ← e2]; simp only [Msg.val, enc, h4, h5, h6, h7]
  cases v with
  | i32 x => cases v' with
    | i32 y => exact congrArg Val.i32 (UInt32.toNat_inj.1 hn)
    | i64 y => simp [vTag] at h3
    | f32 _ | f64 _ | ref _ => exact absurd hv' id
  | i64 x => cases v' with
    | i32 y => simp [vTag] at h3
    | i64 y => exact congrArg Val.i64 (UInt64.toNat_inj.1 hn)
    | f32 _ | f64 _ | ref _ => exact absurd hv' id
  | f32 _ | f64 _ | ref _ => exact absurd hv id

theorem fieldsOf_space {x y : Msg} (h : fieldsOf y = fieldsOf x) : y.space = x.space := by
  simp only [fieldsOf, List.cons.injEq] at h; exact h.1

/-- Equal views: every boundary message of `s` has a twin (same hashed fields) in `s'`. -/
theorem xfer {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') {x : Msg}
    (hx : x ∈ cutMsgs X s) : ∃ y ∈ cutMsgs X s', fieldsOf y = fieldsOf x := by
  have := mem_cutView.2 ⟨x, hx, rfl⟩
  rw [hV] at this
  exact mem_cutView.1 this

/-- Numeric arrays. -/
def NumArr (a : Array Val) : Prop := ∀ i, i < a.size → isNum (a[i]?.getD default)

/-- Two numeric arrays whose messages in one space match both ways are equal. -/
theorem arr_eq (sp : Nat) {a a' : Array Val} (hn : NumArr a) (hn' : NumArr a')
    (h : ∀ i, i < a.size → ∃ j, j < a'.size ∧
      fieldsOf (enc sp j (a'[j]?.getD default) 0) = fieldsOf (enc sp i (a[i]?.getD default) 0))
    (h' : ∀ j, j < a'.size → ∃ i, i < a.size ∧
      fieldsOf (enc sp i (a[i]?.getD default) 0) = fieldsOf (enc sp j (a'[j]?.getD default) 0)) :
    a = a' := by
  have hs : a.size = a'.size := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_lt; intro hlt
      obtain ⟨j, hj, he⟩ := h _ hlt
      have := (enc_fields_inj (hn' j hj) (hn _ hlt) he).2.1; omega
    · apply Nat.le_of_not_lt; intro hlt
      obtain ⟨i, hi, he⟩ := h' _ hlt
      have := (enc_fields_inj (hn i hi) (hn' _ hlt) he).2.1; omega
  refine Array.ext hs fun i h1 h2 => ?_
  obtain ⟨j, hj, he⟩ := h i h1
  obtain ⟨-, rfl, hv⟩ := enc_fields_inj (hn' j hj) (hn i h1) he
  simpa only [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some]
    using hv.symm

/-- Transfer of an array view between equal boundary views. -/
theorem arr_xfer {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') (sp : Nat) {a a' : Array Val}
    (hin : ∀ x, x ∈ arrView sp a → x ∈ cutMsgs X s)
    (hout : ∀ y, y ∈ cutMsgs X s' → y.space = sp → y ∈ arrView sp a') :
    ∀ i, i < a.size → ∃ j, j < a'.size ∧
      fieldsOf (enc sp j (a'[j]?.getD default) 0) = fieldsOf (enc sp i (a[i]?.getD default) 0) := by
  intro i hi
  obtain ⟨y, hy, he⟩ := xfer hV (hin _ (mem_arrView.2 ⟨i, hi, rfl⟩))
  obtain ⟨j, hj, rfl⟩ := mem_arrView.1 (hout y hy (fieldsOf_space he))
  exact ⟨j, hj, he⟩

theorem frm_mem {s : St} {d : Nat} (hd : d < s.frames.length) : frm s d ∈ s.frames := by
  have hd' : d < s.frames.reverse.length := by simpa using hd
  simp only [frm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd', Option.getD_some]
  exact List.mem_reverse.1 (List.getElem_mem hd')

theorem stack_eq {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') (hn : NumArr s.stack)
    (hn' : NumArr s'.stack) : s.stack = s'.stack :=
  arr_eq 0 hn hn'
    (arr_xfer hV 0 (fun x h => mem_cutMsgs.2 (.inl h)) (fun y hy hs => sp_stack hy hs))
    (arr_xfer hV.symm 0 (fun x h => mem_cutMsgs.2 (.inl h)) (fun y hy hs => sp_stack hy hs))

theorem globals_eq {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') (hn : NumArr s.globals)
    (hn' : NumArr s'.globals) : s.globals = s'.globals :=
  arr_eq 2 hn hn'
    (arr_xfer hV 2 (fun x h => mem_cutMsgs.2 (.inr (.inr (.inr (.inl h)))))
      (fun y hy hs => sp_glob hy hs))
    (arr_xfer hV.symm 2 (fun x h => mem_cutMsgs.2 (.inr (.inr (.inr (.inl h)))))
      (fun y hy hs => sp_glob hy hs))

theorem locals_eq {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') {d : Nat}
    (hd : d < s.frames.length) (hd' : d < s'.frames.length) (hn : NumArr (frm s d).locals)
    (hn' : NumArr (frm s' d).locals) : (frm s d).locals = (frm s' d).locals :=
  arr_eq (16 + d) hn hn'
    (arr_xfer hV _ (fun x h => mem_cutMsgs.2 (.inr (.inl ⟨d, hd, h⟩))) (fun y hy hs => (sp_loc hy hs).2))
    (arr_xfer hV.symm _ (fun x h => mem_cutMsgs.2 (.inr (.inl ⟨d, hd', h⟩)))
      (fun y hy hs => (sp_loc hy hs).2))


/-! ## 4. Frames from their messages -/

theorem fieldsOf_eq {x y : Msg} (h : fieldsOf y = fieldsOf x) :
    y.space = x.space ∧ y.slot = x.slot ∧ y.tag = x.tag ∧ y.l0 = x.l0 ∧ y.l1 = x.l1 ∧ y.l2 = x.l2 ∧
      y.l3 = x.l3 := by
  simpa only [fieldsOf, List.cons.injEq, and_true] using h

theorem rec_mem {X : Ctx} {s : St} {d : Nat} (h0 : 0 < d) (hd : d < s.frames.length) :
    recOf X s d ∈ cutMsgs X s :=
  mem_cutMsgs.2 (.inr (.inr (.inl ⟨d, h0, hd, rfl⟩)))

/-- The record of activation `d` in `s` has a twin record of the same activation in `s'`. -/
theorem rec_xfer {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') {d : Nat} (h0 : 0 < d)
    (hd : d < s.frames.length) :
    d < s'.frames.length ∧ gpc X (frm s' (d - 1)) = gpc X (frm s (d - 1)) ∧
      (frm s' (d - 1)).base = (frm s (d - 1)).base := by
  obtain ⟨y, hy, he⟩ := xfer hV (rec_mem h0 hd)
  obtain ⟨d', -, hd', rfl⟩ := sp_rec hy ((fieldsOf_space he).trans rfl)
  obtain ⟨-, h1, -, h2, h3, -⟩ := fieldsOf_eq he
  simp only [recOf, callMsg] at h1 h2 h3
  subst h1
  exact ⟨hd', h2, h3⟩

/-- **Equal views have equally many frames** (both nonempty). -/
theorem nframes_eq {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') (h1 : s.frames ≠ [])
    (h2 : s'.frames ≠ []) : s.frames.length = s'.frames.length := by
  have p1 : 0 < s.frames.length := List.length_pos_iff.2 h1
  have p2 : 0 < s'.frames.length := List.length_pos_iff.2 h2
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt; intro hlt
    have := (rec_xfer hV p2 hlt).1; omega
  · apply Nat.le_of_not_lt; intro hlt
    have := (rec_xfer hV.symm p1 hlt).1; omega

/-- The top frame is at depth `n − 1`. -/
theorem frm_top {s : St} {f : Frame} {rest : List Frame} (h : s.frames = f :: rest) :
    frm s (s.frames.length - 1) = f := by
  simp only [frm, h, List.reverse_cons, List.length_cons, Nat.add_sub_cancel,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- **Offsets decode uniquely** (the checker's `layoutOk`). -/
theorem off_decode (X : Ctx) {k k' pc pc' : Nat} (hk : k < X.nf) (hk' : k' < X.nf)
    (hp : pc < (X.pfOf k).code.size) (hp' : pc' < (X.pfOf k').code.size)
    (h : X.offOf k + pc = X.offOf k' + pc') : k = k' ∧ pc = pc' := by
  have hl := X.hM.layout
  simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hl
  have sz : ∀ k, k < X.nf → (X.pfOf k).code.size = X.M.sizes.getD k 0 := by
    intro k hk
    obtain ⟨pf, h1, h2⟩ := X.hM.pfs k hk
    simp only [Ctx.pfOf, Ctx.fnOf, h1, Option.getD_some, h2]
  have e1 := (hl.2 k hk).2 pc (by rw [← sz k hk]; exact hp)
  have e2 := (hl.2 k' hk').2 pc' (by rw [← sz k' hk']; exact hp')
  simp only [Ctx.offOf] at h
  rw [h, e2] at e1
  simp only [Prod.mk.injEq] at e1
  exact ⟨e1.1.symm, e1.2.symm⟩

/-- The domain facts of one frame: its function is checked, its pc is in its code, its labels are
the checker's at that pc (shifted by the base), and its locals are numeric. -/
def FrameOK (X : Ctx) (f : Frame) : Prop :=
  f.fn ∈ X.M.fns ∧ f.pc < (X.pfOf (X.kOf f.fn)).code.size ∧
    (∃ ls, (X.ckOf (X.kOf f.fn)).labels[f.pc]? = some ls ∧ f.labels = shiftLabels f.base ls) ∧
    NumArr f.locals

theorem kOf_lt {X : Ctx} {fn : Nat} (h : fn ∈ X.M.fns) : X.kOf fn < X.nf :=
  List.idxOf_lt_length_of_mem h

theorem fnOf_kOf {X : Ctx} {fn : Nat} (h : fn ∈ X.M.fns) : X.fnOf (X.kOf fn) = fn := by
  simp only [Ctx.fnOf, Ctx.kOf, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h), Option.getD_some, List.getElem_idxOf]

/-- **A frame is determined by its global pc, base and locals** (on the domain). -/
theorem frame_eq {X : Ctx} {f f' : Frame} (h : FrameOK X f) (h' : FrameOK X f')
    (hg : gpc X f = gpc X f') (hb : f.base = f'.base) (hl : f.locals = f'.locals) : f = f' := by
  obtain ⟨m1, p1, ⟨ls, l1, l2⟩, -⟩ := h
  obtain ⟨m1', p1', ⟨ls', l1', l2'⟩, -⟩ := h'
  obtain ⟨hk, hp⟩ := off_decode X (kOf_lt m1) (kOf_lt m1') p1 p1' hg
  have hfn : f.fn = f'.fn := by rw [← fnOf_kOf m1, ← fnOf_kOf m1', hk]
  rw [hk, hp, l1'] at l1
  cases Option.some.inj l1
  obtain ⟨fn, pc, locs, lab, base⟩ := f
  obtain ⟨fn', pc', locs', lab', base'⟩ := f'
  simp only at hfn hp hb hl l2 l2' ⊢
  subst hfn hp hb hl
  rw [l2, l2']


/-- **The frame list is determined** by the view, the top frame's global pc and base, and the
frame domain facts. -/
theorem frames_eq {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') {f f' : Frame}
    {rest rest' : List Frame} (ht : s.frames = f :: rest) (ht' : s'.frames = f' :: rest')
    (ok : ∀ g ∈ s.frames, FrameOK X g) (ok' : ∀ g ∈ s'.frames, FrameOK X g)
    (hg : gpc X f = gpc X f') (hb : f.base = f'.base) : s.frames = s'.frames := by
  have hn := nframes_eq hV (by rw [ht]; simp) (by rw [ht']; simp)
  have hfd : ∀ d, d < s.frames.length → frm s d = frm s' d := by
    intro d hd
    have hd' : d < s'.frames.length := hn ▸ hd
    have hgb : gpc X (frm s d) = gpc X (frm s' d) ∧ (frm s d).base = (frm s' d).base := by
      by_cases hlt : d + 1 < s.frames.length
      · have := rec_xfer hV (Nat.succ_pos d) hlt
        exact ⟨this.2.1.symm, this.2.2.symm⟩
      · have e : d = s.frames.length - 1 := by omega
        have e' : d = s'.frames.length - 1 := by omega
        have t1 := frm_top ht
        have t2 := frm_top ht'
        rw [← e] at t1
        rw [← e'] at t2
        rw [t1, t2]
        exact ⟨hg, hb⟩
    exact frame_eq (ok _ (frm_mem hd)) (ok' _ (frm_mem hd')) hgb.1 hgb.2
      (locals_eq hV hd hd' (ok _ (frm_mem hd)).2.2.2 (ok' _ (frm_mem hd')).2.2.2)
  rw [← List.reverse_inj]
  refine List.ext_getElem (by simp [hn]) fun d h1 h2 => ?_
  have := hfd d (by simpa using h1)
  simpa only [frm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] using this


/-! ## 5. Registers from their messages -/

/-- Register domain facts: distinct ids, data shorter than `2^24` (the space-6 slot encoding). -/
def RegOK (s : St) : Prop :=
  (s.registers.toList.map Prod.fst).Nodup ∧ ∀ r ∈ s.registers.toList, r.2.size < Register.cap

/-- The register ids in order (data blanked): kept in the remainder, since the view is a set. -/
def regIds (regs : Array (Nat × ByteArray)) : Array (Nat × ByteArray) :=
  regs.map fun r => (r.1, ByteArray.empty)

theorem lookup_unique : ∀ {L : List (Nat × ByteArray)} {a : Nat} {x y : ByteArray},
    (L.map Prod.fst).Nodup → (a, x) ∈ L → (a, y) ∈ L → x = y
  | [], _, _, _, _, hx, _ => by simp at hx
  | (b, z) :: L, a, x, y, hn, hx, hy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    simp only [List.mem_cons, Prod.mk.injEq] at hx hy
    rcases hx with ⟨rfl, rfl⟩ | hx <;> rcases hy with ⟨e, rfl⟩ | hy
    · rfl
    · exact absurd ⟨_, hy, rfl⟩ hn.1
    · subst e; exact absurd ⟨_, hx, rfl⟩ hn.1
    · exact lookup_unique hn.2 hx hy

theorem reg_mem {X : Ctx} {s : St} {x : Msg} (h : x ∈ Register.view s.registers (fun _ => 0)) :
    x ∈ cutMsgs X s :=
  mem_cutMsgs.2 (.inr (.inr (.inr (.inr (.inr h)))))

/-- A register's length message has a twin in `s'`: a register with the same id and length. -/
theorem reg_xfer_len {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') {rid : Nat}
    {d : ByteArray} (hd : (rid, d) ∈ s.registers.toList) :
    ∃ e, (rid, e) ∈ s'.registers.toList ∧ e.size = d.size := by
  obtain ⟨y, hy, he⟩ := xfer hV (reg_mem (X := X) (Register.view_len_mem (tp := fun _ => 0) hd))
  have hy6 := sp_reg hy ((fieldsOf_space he).trans rfl)
  obtain ⟨rid', e, hm, hy'⟩ := Register.mem_view.1 hy6
  obtain ⟨-, h1, h2, h3, -⟩ := fieldsOf_eq he
  rcases Register.mem_regMsgs.1 hy' with rfl | ⟨i, -, rfl⟩
  · simp only [Register.lenMsg_slot, Register.lenSlot_eq, Register.lenMsg_l0] at h1 h3
    have := Nat.mul_right_cancel Register.cap_pos h1
    subst this
    exact ⟨e, hm, h3⟩
  · simp [Register.byteMsg, Register.lenMsg, Register.byteTag, Register.lenTag] at h2

/-- A register byte message has a twin in `s'`: a register with the same id and that byte. -/
theorem reg_xfer_byte {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') (hr : RegOK s)
    (hr' : RegOK s') {rid : Nat} {d : ByteArray} (hd : (rid, d) ∈ s.registers.toList) {i : Nat}
    (hi : i < d.size) : ∃ e, (rid, e) ∈ s'.registers.toList ∧ e.get! i = d.get! i := by
  obtain ⟨y, hy, he⟩ :=
    xfer hV (reg_mem (X := X) (Register.view_byte (tp := fun _ => 0) hd hi))
  have hy6 := sp_reg hy ((fieldsOf_space he).trans rfl)
  obtain ⟨rid', e, hm, hy'⟩ := Register.mem_view.1 hy6
  obtain ⟨-, h1, h2, h3, -⟩ := fieldsOf_eq he
  rcases Register.mem_regMsgs.1 hy' with rfl | ⟨j, hj, rfl⟩
  · simp [Register.byteMsg, Register.lenMsg, Register.byteTag, Register.lenTag] at h2
  · simp only [Register.byteMsg_slot, Register.byteMsg_l0] at h1 h3
    have c1 := hr.2 _ hd
    have c2 := hr'.2 _ hm
    simp only at c1 c2
    obtain ⟨rfl, rfl⟩ := Register.byteSlot_inj h1 (by omega) (by omega)
    exact ⟨e, hm, UInt8.toNat_inj.1 h3⟩

/-- **The registers are determined** by the view and the id order. -/
theorem regs_eq {X : Ctx} {s s' : St} (hV : cutView X s = cutView X s') (hr : RegOK s)
    (hr' : RegOK s') (hid : regIds s.registers = regIds s'.registers) :
    s.registers = s'.registers := by
  have hl := congrArg Array.toList hid
  simp only [regIds, Array.toList_map] at hl
  have hlen : s.registers.toList.length = s'.registers.toList.length := by
    simpa using congrArg List.length hl
  suffices h : s.registers.toList = s'.registers.toList by
    exact Array.toList_inj.1 h
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  have hfst : (s.registers.toList[i]).1 = (s'.registers.toList[i]).1 := by
    have := congrArg (fun l => (l[i]?).map Prod.fst) hl
    simpa [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] using this
  have m1 : s.registers.toList[i] ∈ s.registers.toList := List.getElem_mem h1
  have m2 : s'.registers.toList[i] ∈ s'.registers.toList := List.getElem_mem h2
  generalize s.registers.toList[i] = x at m1 hfst ⊢
  generalize s'.registers.toList[i] = y at m2 hfst ⊢
  obtain ⟨rid, d⟩ := x
  obtain ⟨rid', d'⟩ := y
  simp only at hfst
  subst hfst
  obtain ⟨e, he, hs⟩ := reg_xfer_len hV m1
  cases lookup_unique hr'.1 he m2
  congr 1
  refine ba_ext hs.symm fun j hj => ?_
  obtain ⟨e2, he2, hb⟩ := reg_xfer_byte hV hr hr' m1 hj
  cases lookup_unique hr'.1 he2 m2
  exact hb.symm


/-! ## 6. The domain, the remainder and the reconstruction lemma -/

/-- **The AIR-branch domain** of a cut state (classical; facts honest cut states have, to be shown
from `RelW` at a cut): a frame is running, every boundary message is `MsgWF` (fields `< 2^30`),
every frame satisfies `FrameOK`, stack and globals are numeric, every page has `pageSize` bytes,
and the register file has distinct ids and data shorter than `2^24`. -/
structure InDom (X : Ctx) (s : St) : Prop where
  ne : s.frames ≠ []
  wf : ∀ m ∈ cutView X s, MsgWF m
  frames : ∀ f ∈ s.frames, FrameOK X f
  numS : NumArr s.stack
  numG : NumArr s.globals
  pages : WasmBase.PagesOK s
  regs : RegOK s
  /-- the record's counters are `u64`s -/
  lt64 : gpc X (s.frames.headD default) < 2 ^ 64 ∧ (s.frames.headD default).base < 2 ^ 64 ∧
    s.stackRem < 2 ^ 64 ∧ s.pages.size < 2 ^ 64

/-- The state with its viewed parts blanked (the register ids are kept, in order). -/
def blank (s : St) : St :=
  { s with stack := #[], frames := [], pages := #[], globals := #[], stackRem := 0,
           registers := regIds s.registers }

theorem blank_inj {s s' : St} (hb : blank s = blank s') (h1 : s.stack = s'.stack)
    (h2 : s.frames = s'.frames) (h3 : s.pages = s'.pages) (h4 : s.globals = s'.globals)
    (h5 : s.stackRem = s'.stackRem) (h6 : s.registers = s'.registers) : s = s' := by
  cases s
  cases s'
  simp only [blank, St.mk.injEq] at hb h1 h2 h3 h4 h5 h6 ⊢
  simp_all

/-- **The reconstruction lemma.** Two domain states with the same boundary view, the same top
frame global pc and base (`WasmBnd.pc`, `sp`) and the same register id order have the same operand
stack, frames, globals and registers. -/
theorem reconstruct {X : Ctx} {s s' : St} (h : InDom X s) (h' : InDom X s')
    (hV : cutView X s = cutView X s')
    (hpc : gpc X (s.frames.headD default) = gpc X (s'.frames.headD default))
    (hsp : (s.frames.headD default).base = (s'.frames.headD default).base)
    (hid : regIds s.registers = regIds s'.registers) :
    s.stack = s'.stack ∧ s.frames = s'.frames ∧ s.globals = s'.globals ∧
      s.registers = s'.registers := by
  refine ⟨stack_eq hV h.numS h'.numS, ?_, globals_eq hV h.numG h'.numG, regs_eq hV h.regs h'.regs hid⟩
  obtain ⟨f, rest, ht⟩ := List.exists_cons_of_ne_nil h.ne
  obtain ⟨f', rest', ht'⟩ := List.exists_cons_of_ne_nil h'.ne
  rw [ht, ht'] at hpc hsp
  exact frames_eq hV ht ht' h.frames h'.frames hpc hsp

/-! ## 7. The Wasm view -/

/-- The remainder of a Wasm component: on the AIR branch the query, module, entry and the state
with its viewed parts blanked; otherwise the whole component (a different constructor). -/
inductive WRest where
  | air (q : CallArgs) (p : Prepared) (k : EntK) (s : St)
  | other (w : CallArgs × CallConf)

/-- **The parameters of the Wasm view.** -/
structure WasmViewParams where
  /-- the static context (checked module, entry function) of an entry of a query -/
  ctxOf : CallArgs → Prepared → EntK → Option Ctx
  /-- the code and function-table commitments (no binding needed: `q`, `p` are in the remainder) -/
  codeRootOf : CallArgs → Prepared → ArenaCore.Bytes
  funcRootOf : CallArgs → Prepared → ArenaCore.Bytes
  /-- the remainder's byte encoder (lane E: `CallArgs`, `Prepared`, `EntK`, `St` encoders) -/
  encRest : WRest → ArenaCore.Bytes
  encRest_inj : ∀ a b, encRest a = encRest b → a = b
  /-- digest widths (for `BndRec.WF`) -/
  codeRoot_len : ∀ q p, (codeRootOf q p).length = digestLen
  funcRoot_len : ∀ q p, (funcRootOf q p).length = digestLen

variable (P : WasmViewParams)

open Classical in
/-- The AIR branch: a running entry whose context is defined and whose state is in the domain. -/
noncomputable def airOf : CallArgs × CallConf → Option (Ctx × Prepared × EntK × St × Nat)
  | (q, .ent p k (.cont s) n) =>
    match P.ctxOf q p k with
    | some X => if InDom X s ∧ n < 2 ^ 64 then some (X, p, k, s, n) else none
    | none => none
  | _ => none

theorem airOf_spec {w : CallArgs × CallConf} {X : Ctx} {p : Prepared} {k : EntK} {s : St} {n : Nat}
    (h : airOf P w = some (X, p, k, s, n)) :
    w = (w.1, .ent p k (.cont s) n) ∧ P.ctxOf w.1 p k = some X ∧ InDom X s ∧ n < 2 ^ 64 := by
  obtain ⟨q, cc⟩ := w
  cases cc with
  | ent p' k' r n' =>
    cases r with
    | cont s' =>
      simp only [airOf] at h
      split at h
      · rename_i X' hX
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
          rename_i hD
          exact ⟨rfl, hX, hD⟩
        · simp at h
      · simp at h
    | _ => simp [airOf] at h
  | _ => simp [airOf] at h

theorem airOf_some {q : CallArgs} {p : Prepared} {k : EntK} {s : St} {n : Nat} {X : Ctx}
    (hX : P.ctxOf q p k = some X) (hD : InDom X s) (hn : n < 2 ^ 64) :
    airOf P (q, .ent p k (.cont s) n) = some (X, p, k, s, n) := by
  simp [airOf, hX, hD, hn]

/-- The AIR-branch record. -/
def airBnd (q : CallArgs) (X : Ctx) (p : Prepared) (k : EntK) (s : St) (n : Nat) : WasmBnd :=
  let f := s.frames.headD default
  let fd := bdigest (cutBytes (cutView X s))
  { pc := gpc X f, sp := f.base, stackRem := s.stackRem, fuel := n, framesDigest := fd,
    memRoot := (memRootOf s).take 42, memPages := s.pages.size, globalsDigest := fd,
    registersDigest := fd, vmCtxDigest := bdigest (P.encRest (.air q p k (blank s))),
    promisesDigest := bdigest [], codeRoot := P.codeRootOf q p, funcRoot := P.funcRootOf q p }

/-- The fallback record: only the remainder digest is not constant. -/
def fbBnd (w : CallArgs × CallConf) : WasmBnd :=
  { pc := 0, sp := 0, stackRem := 0, fuel := 0, framesDigest := bdigest [], memRoot := bdigest [],
    memPages := 0, globalsDigest := bdigest [], registersDigest := bdigest [],
    vmCtxDigest := bdigest (P.encRest (.other w)), promisesDigest := bdigest [],
    codeRoot := bdigest [], funcRoot := bdigest [] }

/-- The record of an in-call component. -/
noncomputable def wasmBnd (w : CallArgs × CallConf) : WasmBnd :=
  match airOf P w with
  | some (X, p, k, s, n) => airBnd P w.1 X p k s n
  | none => fbBnd P w

/-- **The Wasm component of `ViewImpl`** (`wasmD none = none`). -/
noncomputable def wasmD (c : WmV) : Option WasmBnd := c.map (wasmBnd P)

/-- The remainder of a component. -/
noncomputable def restOf (w : CallArgs × CallConf) : WRest :=
  match airOf P w with
  | some (_, p, k, s, _) => .air w.1 p k (blank s)
  | none => .other w

theorem wasmBnd_rest (w : CallArgs × CallConf) :
    (wasmBnd P w).vmCtxDigest = bdigest (P.encRest (restOf P w)) := by
  unfold wasmBnd restOf
  split <;> rfl

/-- **The AIR's public `ctxDigest` and `memRoot` are this view's** (on the AIR branch). -/
theorem wasmD_air {w : CallArgs × CallConf} {X : Ctx} {p : Prepared} {k : EntK} {s : St} {n : Nat}
    (h : airOf P w = some (X, p, k, s, n)) :
    wasmD P (some w) = some (wasmBnd P w) ∧
    (wasmBnd P w).framesDigest = (cutDigest (cutView X s)).take 42 ∧
    (wasmBnd P w).memRoot = (memRootOf s).take 42 ∧
    (wasmBnd P w).pc = gpc X (s.frames.headD default) ∧
    (wasmBnd P w).sp = (s.frames.headD default).base ∧
    (wasmBnd P w).stackRem = s.stackRem ∧ (wasmBnd P w).fuel = n ∧
    (wasmBnd P w).memPages = s.pages.size := by
  refine ⟨rfl, ?_⟩
  unfold wasmBnd
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem memRootOf_length (s : St) : (memRootOf s).length = 48 := by
  obtain ⟨m, hm⟩ := memRoot_sha s
  simp only [memRootOf, hm, Option.getD_some, sha384_length]

/-- **Every record is well-formed** (`WasmBnd.codec.ok`: counters `< 2^64`, digests 42 bytes), so
`BndRec.WF` holds for the Wasm part of any configuration. -/
theorem wasmBnd_ok (w : CallArgs × CallConf) : WasmBnd.codec.ok (wasmBnd P w) := by
  have b0 : (bdigest []).length = digestLen := bdigest_length _
  unfold wasmBnd
  split
  · rename_i X p k s n ha
    obtain ⟨-, -, hD, hn⟩ := airOf_spec P ha
    obtain ⟨l1, l2, l3, l4⟩ := hD.lt64
    simp only [WasmBnd.codec, NearSpecV3.E2E.Bnd.mapC, NearSpecV3.E2E.Bnd.pairC,
      NearSpecV3.E2E.Bnd.natC, NearSpecV3.E2E.Bnd.bytesC, airBnd]
    refine ⟨l1, l2, l3, hn, bdigest_length _, ?_, l4, bdigest_length _, bdigest_length _,
      bdigest_length _, b0, P.codeRoot_len _ _, P.funcRoot_len _ _⟩
    simp only [List.length_take, memRootOf_length, digestLen]; decide
  · simp only [WasmBnd.codec, NearSpecV3.E2E.Bnd.mapC, NearSpecV3.E2E.Bnd.pairC,
      NearSpecV3.E2E.Bnd.natC, NearSpecV3.E2E.Bnd.bytesC, fbBnd]
    exact ⟨by decide, by decide, by decide, by decide, b0, b0, by decide, b0, b0,
      bdigest_length _, b0, b0, b0⟩

/-! ## 8. Binding -/

/-- **Binding of one in-call record**: equal records are equal components, or a `Sha384Coll`. -/
theorem wasmBnd_binding {w w' : CallArgs × CallConf} (h : wasmBnd P w = wasmBnd P w') :
    w = w' ∨ Sha384Coll := by
  classical
  have hr : bdigest (P.encRest (restOf P w)) = bdigest (P.encRest (restOf P w')) := by
    rw [← wasmBnd_rest, ← wasmBnd_rest, h]
  by_cases he : P.encRest (restOf P w) = P.encRest (restOf P w')
  rotate_left
  · exact .inr ⟨_, _, he, hr⟩
  have hR := P.encRest_inj _ _ he
  unfold restOf at hR
  unfold wasmBnd at h
  cases ha : airOf P w with
  | none =>
    cases hb : airOf P w' with
    | none =>
      rw [ha, hb] at hR
      exact .inl (WRest.other.inj hR)
    | some b =>
      obtain ⟨X', p', k', s', n'⟩ := b
      rw [ha, hb] at hR
      cases hR
  | some a =>
    obtain ⟨X, p, k, s, n⟩ := a
    cases hb : airOf P w' with
    | none =>
      rw [ha, hb] at hR
      cases hR
    | some b =>
      obtain ⟨X', p', k', s', n'⟩ := b
      rw [ha, hb] at hR h
      obtain ⟨hq, rfl, rfl, hbl⟩ := WRest.air.inj hR
      obtain ⟨hw, hX, hD, -⟩ := airOf_spec P ha
      obtain ⟨hw', hX', hD', -⟩ := airOf_spec P hb
      rw [hq, hX'] at hX
      cases Option.some.inj hX
      simp only [airBnd, WasmBnd.mk.injEq] at h
      obtain ⟨hpc, hsp, hrem, rfl, hfd, hmr, hmp, -, -, -, -, -, -⟩ := h
      -- the boundary view
      by_cases hcb : cutBytes (cutView X s) = cutBytes (cutView X s')
      rotate_left
      · exact .inr ⟨_, _, hcb, hfd⟩
      have hV := cutBytes_inj hD.wf hD'.wf hcb
      -- the memory
      rcases memRoot_binding s s' hmp hmr with hblk | hc
      rotate_left
      · exact .inr hc
      have hpg := pages_eq hD.pages hD'.pages hmp hblk
      obtain ⟨h1, h2, h3, h4⟩ :=
        reconstruct hD hD' hV hpc hsp (congrArg St.registers hbl)
      have hs := blank_inj hbl h1 h2 hpg h3 hrem h4
      subst hs
      exact .inl (by rw [hw, hw', hq])

/-- **The binding theorem**: a collision of `wasmD` is a 42-byte SHA-384 (`bdigest`) collision. -/
theorem wasmD_binding (h : Coll (wasmD P)) : Sha384Coll := by
  obtain ⟨a, b, hne, he⟩ := h
  cases a with
  | none =>
    cases b with
    | none => exact absurd rfl hne
    | some w => simp [wasmD] at he
  | some w =>
    cases b with
    | none => simp [wasmD] at he
    | some w' =>
      simp only [wasmD, Option.map_some, Option.some.injEq] at he
      rcases wasmBnd_binding P he with h | h
      · exact absurd (by rw [h]) hne
      · exact h

/-- **The `hwasm` premise of `viewImpl_binding_bad`** for any view whose Wasm component is this
instance. -/
theorem viewImpl_hwasm (V : ViewImpl) (hV : V.wasmD = wasmD P) (Bad : Prop)
    (hsha : Sha384Coll → Bad) : Coll V.wasmD → Bad := by
  rw [hV]; exact fun h => hsha (wasmD_binding P h)

#print axioms memRoot_binding
#print axioms pages_eq
#print axioms reconstruct
#print axioms wasmD_air
#print axioms wasmBnd_ok
#print axioms wasmBnd_binding
#print axioms wasmD_binding
#print axioms viewImpl_hwasm

end WasmBase.WasmView
