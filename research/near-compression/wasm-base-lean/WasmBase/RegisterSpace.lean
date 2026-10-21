import WasmBase.Event
import WasmBase.Chips
/-!
# WasmBase.RegisterSpace — channel space 6: the host register file

`results/pq-wasm-base/README.md` §14.2 proposes the register file as a **new channel space 6**, keyed
by `(register_id, pos)` with **one length message per register**.  This file builds that space as a
pure message model (no AIR rows yet, no `Holds`): the key encoding, its injectivity, the decidable
domain conditions, the view of a register file as messages, and the two obligation Props the join
has to discharge.  The AIR table that carries these messages is `Chips.Reg`
(`WasmBase/HostChip.lean`).

## Key encoding

A channel `Msg` has a single `slot` field, so `(register_id, pos)` is encoded as

```
slot rid pos = rid * 2^posBits + pos,      posBits = 24
```

which is **injective** on the domain `rid ≤ 99 ∧ pos < 2^24` (`slot_inj`), and lands below the
BabyBear modulus (`slot_lt_P`: `99 * 2^24 + 2^24 = 100 * 2^24 < p`), so the encoding is exact in the
field and a lookup on the encoded slot is a lookup on the pair.

## Messages

Two message shapes share the space and differ in `tag`:

* a **byte** message `[6, rid·2^24 + 1 + i, 0, b, 0, 0, 0, tp]` — byte `i` of register `rid`;
  the `+1` keeps slot `0` free for the length message;
* a **length** message `[6, rid·2^24, 2, len, 0, 0, 0, tp]` — the byte count of register `rid`.

`tag = 2` (not 1) is essential: `Msg.ok` treats tag `1` as an `i64` value, and a register length is
not a value.  A length message is therefore *not* a well-formed value message, which is what makes
"the register file is not the operand stack" checkable (`lenMsg_not_ok`).

## Domain conditions (explicit, decidable)

`regOK` / `posOK` / `lenOK` below are `Bool`-valued, with `…_iff` lemmas; `domainOK` bundles them.
They are stated as **domain conditions**, not constraints: `rid ≤ 99` (the spec's
`maxNumberRegisters = 100`), `pos < 2^24` and `len ≤ 2^24 − 1`.

## What is proved here and what is only stated

Proved (no `Holds`, no axioms beyond the standard three): the encoding facts (`slot_mod`,
`slot_inj`, `slot_lt_P`, `byteSlot_eq`/`_div`/`_mod`/`_inj`/`_ne`, `lenSlot_eq`,
`lenSlot_ne_byteSlot`), the message constructors and their fields (`byteMsg_*`, `lenMsg_*`), the
well-formedness of a byte message (`byteMsg_ok`), the fact that a length message is not a value
message (`lenMsg_not_ok`), the view (`view`, `mem_view`, `view_len_mem`, `view_byte`), the
disjointness of two registers (`regMsgs_disjoint`) and the `Nodup`ness of one register's view
(`regMsgs_nodup`), and the decidable domain predicates.

Stated only (`Prop`): `RegBusSound` (every live space-6 message in a trace is a message of the final
register file), the state-side obligation.

**`RegLenAgree` is proved, but not in the form stated here.**  The stated definition is false for a
length-only access (`regLenAgree_lone_length`, `Main/RegWalk.lean`).  The AIR obligation is
group-local and is proved as `regLenAgree_group` (`Main/RegWalk.lean`) from the group walk
(`reg_group_walk`): a length row terminates a group whose byte rows are exactly `pos = 0 … len−1`.
-/
namespace WasmBase
namespace Register
open ZkFormal.Algebra
set_option maxRecDepth 8000

/-- Channel space of the register file (README §14.2: "a new channel space 6"). -/
def space : Nat := 6

/-- Width of the `pos` field in the encoded slot. -/
def posBits : Nat := 24

/-- Largest register id (`maxNumberRegisters = 100`, so ids `0..99`). -/
def maxRegId : Nat := 99

/-- `2^24`, the width of the `pos` field. -/
def cap : Nat := 2 ^ posBits

theorem cap_pos : 0 < cap := by decide

/-- `slot rid pos = rid · 2^24 + pos`. -/
def slot (rid pos : Nat) : Nat := rid * cap + pos

/-- Slot of the length message of register `rid` (the only slot no byte can use). -/
def lenSlot (rid : Nat) : Nat := slot rid 0

/-- Slot of byte `i` of register `rid`. -/
def byteSlot (rid i : Nat) : Nat := slot rid (i + 1)

/-- Tag of a byte message. -/
def byteTag : Nat := 0
/-- Tag of a length message (`2`: neither an `i32` nor an `i64` value). -/
def lenTag : Nat := 2

def byteMsg (rid i b tp : Nat) : Msg :=
  ⟨space, byteSlot rid i, byteTag, b, 0, 0, 0, tp⟩

def lenMsg (rid len tp : Nat) : Msg :=
  ⟨space, lenSlot rid, lenTag, len, 0, 0, 0, tp⟩

/-! ## Domain conditions -/

def regOK (rid : Nat) : Bool := rid ≤ maxRegId
def posOK (pos : Nat) : Bool := pos < 2 ^ posBits
def lenOK (len : Nat) : Bool := len < 2 ^ posBits

/-- All register-file domain conditions at one key. -/
def domainOK (rid pos len : Nat) : Bool := regOK rid && posOK pos && lenOK len && pos < len

theorem regOK_iff (rid : Nat) : regOK rid = true ↔ rid ≤ 99 := by
  simp only [regOK, maxRegId]
  exact decide_eq_true_iff

theorem posOK_iff (pos : Nat) : posOK pos = true ↔ pos < 2 ^ 24 := by
  simp only [posOK, posBits]
  exact decide_eq_true_iff

theorem lenOK_iff (len : Nat) : lenOK len = true ↔ len < 2 ^ 24 := by
  simp only [lenOK, posBits]
  exact decide_eq_true_iff

theorem domainOK_iff (rid pos len : Nat) :
    domainOK rid pos len = true ↔ rid ≤ 99 ∧ pos < 2 ^ 24 ∧ len < 2 ^ 24 ∧ pos < len := by
  unfold domainOK regOK posOK lenOK maxRegId posBits
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff,
    decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact ⟨fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩, fun h => ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩⟩

theorem domainOK.rid {rid pos len : Nat} (h : domainOK rid pos len = true) : rid ≤ 99 :=
  ((domainOK_iff rid pos len).mp h).1
theorem domainOK.pos {rid pos len : Nat} (h : domainOK rid pos len = true) : pos < 2 ^ 24 :=
  ((domainOK_iff rid pos len).mp h).2.1
theorem domainOK.len {rid pos len : Nat} (h : domainOK rid pos len = true) : len < 2 ^ 24 :=
  ((domainOK_iff rid pos len).mp h).2.2.1
theorem domainOK.lt {rid pos len : Nat} (h : domainOK rid pos len = true) : pos < len :=
  ((domainOK_iff rid pos len).mp h).2.2.2

/-! ## The key encoding is injective and lands below the modulus -/

theorem slot_mod (rid pos : Nat) (hp : pos < cap) : slot rid pos % cap = pos := by
  rw [slot, Nat.add_comm (rid * cap) pos, Nat.mul_comm rid cap]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]

/-- **Injectivity of the encoded register key** on the domain `pos < 2^24`. -/
theorem slot_inj {rid pos rid' pos' : Nat} (hp : pos < cap) (hp' : pos' < cap)
    (h : slot rid pos = slot rid' pos') : rid = rid' ∧ pos = pos' := by
  have h1 : pos = pos' := by rw [← slot_mod rid pos hp, ← slot_mod rid' pos' hp', h]
  refine ⟨?_, h1⟩
  rw [h1] at h
  exact Nat.mul_right_cancel cap_pos (by unfold slot at h; omega)

/-- The encoded slot fits in the field: `slot rid pos < p` on the domain. -/
theorem slot_lt_P {rid pos : Nat} (hr : rid ≤ 99) (hp : pos < cap) : slot rid pos < P := by
  have h1 : rid * cap ≤ 99 * cap := Nat.mul_le_mul hr (Nat.le_refl _)
  have h2 : slot rid pos < 100 * cap := by simp only [slot] at h1 ⊢; omega
  have hc : cap = 16777216 := by decide
  have hP : P = 2013265921 := rfl
  omega

/-- `byteSlot rid i = rid · 2^24 + (i + 1)` (the `+1` keeps the length slot free). -/
theorem byteSlot_add (rid i : Nat) : byteSlot rid i = rid * cap + (i + 1) := by
  simp [byteSlot, slot]

/-- `lenSlot rid = rid · 2^24`. -/
theorem lenSlot_eq (rid : Nat) : lenSlot rid = rid * cap := by
  simp [lenSlot, slot]

/-- The length slot and any byte slot of the same register differ. -/
theorem lenSlot_ne_byteSlot (rid i : Nat) : lenSlot rid ≠ byteSlot rid i := by
  rw [lenSlot_eq, byteSlot_add]; omega

/-- The register id is the quotient of a byte slot by `2^24`. -/
theorem byteSlot_div {rid i : Nat} (hi : i + 1 < cap) : byteSlot rid i / cap = rid := by
  rw [byteSlot_add]
  have h : rid * cap + (i + 1) = cap * rid + (i + 1) := by rw [Nat.mul_comm]
  rw [h, Nat.mul_add_div cap_pos, Nat.div_eq_of_lt hi, Nat.add_zero]

/-- The byte position is the remainder of a byte slot modulo `2^24`, minus one. -/
theorem byteSlot_mod {rid i : Nat} (hi : i + 1 < cap) : byteSlot rid i % cap = i + 1 := by
  rw [byteSlot_add, Nat.add_comm (rid * cap) (i + 1), Nat.mul_comm rid cap]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

/-- **Byte slots are injective** in `(register_id, pos)` on the domain. -/
theorem byteSlot_inj {rid rid' i j : Nat} (h : byteSlot rid i = byteSlot rid' j)
    (hi : i + 1 < cap) (hj : j + 1 < cap) : rid = rid' ∧ i = j := by
  have hr : rid = rid' :=
    (byteSlot_div (rid := rid) hi).symm.trans
      ((congrArg (· / cap) h).trans (byteSlot_div (rid := rid') hj))
  have hj2 : i + 1 = j + 1 := by
    rw [← byteSlot_mod (rid := rid) hi, h, byteSlot_mod (rid := rid') hj]
  exact ⟨hr, by omega⟩

/-- The length slot of one register and a byte slot of a different register differ. -/
theorem lenSlot_ne_byteSlot' {rid rid' j : Nat} (hr : rid ≠ rid') (hj : j + 1 < cap) :
    lenSlot rid ≠ byteSlot rid' j := by
  intro h
  have h1 : lenSlot rid / cap = rid := by
    rw [lenSlot_eq, Nat.mul_comm rid cap, Nat.mul_div_right _ cap_pos]
  have h2 : byteSlot rid' j / cap = rid' := byteSlot_div hj
  exact hr (by rw [← h1, h, h2])

/-- Byte slots of different registers, or different positions, are distinct. -/
theorem byteSlot_ne {rid rid' i j : Nat} (h : rid ≠ rid' ∨ i ≠ j) (hi : i + 1 < cap)
    (hj : j + 1 < cap) : byteSlot rid i ≠ byteSlot rid' j := by
  intro he
  obtain ⟨h1, h2⟩ := byteSlot_inj he hi hj
  rcases h with h | h
  · exact h h1
  · exact h h2

/-! ## Message field projections -/

@[simp] theorem byteMsg_space (rid i b tp : Nat) : (byteMsg rid i b tp).space = 6 := rfl
@[simp] theorem byteMsg_slot (rid i b tp : Nat) : (byteMsg rid i b tp).slot = byteSlot rid i := rfl
@[simp] theorem byteMsg_tag (rid i b tp : Nat) : (byteMsg rid i b tp).tag = 0 := rfl
@[simp] theorem byteMsg_l0 (rid i b tp : Nat) : (byteMsg rid i b tp).l0 = b := rfl
@[simp] theorem lenMsg_space (rid len tp : Nat) : (lenMsg rid len tp).space = 6 := rfl
@[simp] theorem lenMsg_slot (rid len tp : Nat) : (lenMsg rid len tp).slot = lenSlot rid := rfl
@[simp] theorem lenMsg_tag (rid len tp : Nat) : (lenMsg rid len tp).tag = 2 := rfl
@[simp] theorem lenMsg_l0 (rid len tp : Nat) : (lenMsg rid len tp).l0 = len := rfl

/-- A byte message with `b < 256` is a well-formed value message (tag 0). -/
theorem byteMsg_ok {rid i b tp : Nat} (hb : b < 256) : (byteMsg rid i b tp).ok := by
  have hlt : b < 65536 := by omega
  unfold byteMsg Msg.ok
  dsimp only
  refine ⟨hlt, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A length message is **not** a value message: its tag is 2, so `Msg.toVal` would decode it as an
`i32`, but its `ok` predicate requires tag `0` or `1`. -/
theorem lenMsg_not_ok (rid len tp : Nat) : ¬ (lenMsg rid len tp).ok := by
  simp [lenMsg, Msg.ok, lenTag]

theorem byteMsg_ne_lenMsg (rid i b tp rid' len tp' : Nat) :
    byteMsg rid i b tp ≠ lenMsg rid' len tp' := by
  intro h
  have := congrArg Msg.tag h
  simp [byteMsg, lenMsg, byteTag, lenTag] at this

/-! ## The register file as a list of messages

`view` maps a register file `Array (Nat × ByteArray)` to its messages: for each register one length
message and one byte message per byte, all produced at time `tp rid`. -/

def regMsgs (rid : Nat) (d : ByteArray) (tp : Nat) : List Msg :=
  lenMsg rid d.size tp :: (List.range d.size).map (fun i => byteMsg rid i (d.get! i).toNat tp)

def view (regs : Array (Nat × ByteArray)) (tp : Nat → Nat) : List Msg :=
  regs.toList.flatMap fun (rid, d) => regMsgs rid d (tp rid)

theorem mem_regMsgs {x : Msg} {rid : Nat} {d : ByteArray} {tp : Nat} :
    x ∈ regMsgs rid d tp ↔
      x = lenMsg rid d.size tp ∨ ∃ i, i < d.size ∧ x = byteMsg rid i (d.get! i).toNat tp := by
  simp only [regMsgs, List.mem_cons, List.mem_map, List.mem_range]
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, h.symm⟩
  · rintro (h | ⟨i, hi, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, h.symm⟩

theorem mem_view {x : Msg} {regs : Array (Nat × ByteArray)} {tp : Nat → Nat} :
    x ∈ view regs tp ↔ ∃ rid d, (rid, d) ∈ regs.toList ∧ x ∈ regMsgs rid d (tp rid) := by
  simp [view, List.mem_flatMap, Prod.exists]

/-- **The length message of a register is in its view** and carries the byte count. -/
theorem view_len_mem {regs : Array (Nat × ByteArray)} {tp : Nat → Nat} {rid : Nat} {d : ByteArray}
    (h : (rid, d) ∈ regs.toList) : lenMsg rid d.size (tp rid) ∈ view regs tp :=
  (mem_view).mpr ⟨rid, d, h, (mem_regMsgs).mpr (Or.inl rfl)⟩

/-- **The byte message at `(rid, i)` is in the view** and carries the byte. -/
theorem view_byte {regs : Array (Nat × ByteArray)} {tp : Nat → Nat} {rid : Nat} {d : ByteArray}
    (h : (rid, d) ∈ regs.toList) {i : Nat} (hi : i < d.size) :
    byteMsg rid i (d.get! i).toNat (tp rid) ∈ view regs tp :=
  (mem_view).mpr ⟨rid, d, h, (mem_regMsgs).mpr (Or.inr ⟨i, hi, rfl⟩)⟩

/-- Two distinct registers contribute disjoint message sets on the domain. -/
theorem regMsgs_disjoint {rid rid' : Nat} {d d' : ByteArray} {tp tp' : Nat}
    (hr : rid ≠ rid') (hd : d.size < cap) (hd' : d'.size < cap) :
    ∀ x ∈ regMsgs rid d tp, ∀ y ∈ regMsgs rid' d' tp', x ≠ y := by
  intro x hx y hy hxy
  rw [mem_regMsgs] at hx hy
  have hs : x.slot = y.slot := congrArg Msg.slot hxy
  have hcap : 0 < cap := cap_pos
  obtain hx0 | ⟨i, hi, hx0⟩ := hx
  · obtain hy0 | ⟨j, hj, hy0⟩ := hy
    · rw [hx0, hy0] at hs
      simp only [lenMsg_slot, lenSlot_eq] at hs
      exact hr (Nat.mul_right_cancel cap_pos hs)
    · rw [hx0, hy0] at hs
      exact lenSlot_ne_byteSlot' hr (by omega) hs
  · obtain hy0 | ⟨j, hj, hy0⟩ := hy
    · rw [hx0, hy0] at hs
      exact lenSlot_ne_byteSlot' (Ne.symm hr) (by omega) (hs.symm)
    · rw [hx0, hy0] at hs
      simp only [byteMsg_slot] at hs
      exact hr (byteSlot_inj hs (by omega) (by omega)).1

/-- Byte messages of one register have distinct slots, hence distinct message values. -/
theorem regMsgs_bytes_pairwise {rid : Nat} {d : ByteArray} (tp : Nat) :
    List.Pairwise (fun a b => a ≠ b)
      ((List.range d.size).map (fun i => byteMsg rid i (d.get! i).toNat tp)) := by
  refine List.Pairwise.map _ (R := fun a b : Nat => a ≠ b) ?_ List.nodup_range
  intro a b hne heq
  have hs : byteSlot rid a = byteSlot rid b := congrArg Msg.slot heq
  simp only [byteSlot_add] at hs
  omega

/-- **The view of one register is `Nodup`.**  (`d.size < 2^24` is the register-file domain
condition; the slot encoding is injective without it, so the proof does not need it.) -/
theorem regMsgs_nodup {rid : Nat} {d : ByteArray} {tp : Nat} (_hd : d.size < 2 ^ 24) :
    (regMsgs rid d tp).Nodup := by
  rw [regMsgs, List.nodup_cons]
  refine ⟨?_, regMsgs_bytes_pairwise (d := d) (rid := rid) tp⟩
  intro h
  rw [List.mem_map] at h
  obtain ⟨i, hi, he⟩ := h
  rw [List.mem_range] at hi
  exact lenSlot_ne_byteSlot rid i (by rw [← lenMsg_slot]; exact (congrArg Msg.slot he).symm)

/-! ## Obligation Props (stated, not proved)

These are the two things the register space defers to the join/row layers.  They are `Prop`s on
purpose: `RegBusSound` needs the state side and the top-level execution theorem, and `RegLenAgree`
needs the AIR's group walk (`Main/RegFacts.lean` has the row-local half). -/

/-- **Stated, not proved.**  Every live space-6 message of a host trace is a message of the final
register file: no byte of a register can appear on the bus without the state side having put it
there (through `input`, a context getter, or `write_register`), and no byte can disappear from it
except through a register overwrite or a register read. -/
def RegBusSound (live : Msg → Prop) (regs : Array (Nat × ByteArray)) (tp : Nat → Nat) : Prop :=
  ∀ x, x.space = space → (live x ↔ x ∈ view regs tp)

/-- **Deprecated statement: this is false.**  Counting byte messages at the *same producer time* as
the length message fails for a length-only access (`register_len`): that call emits one length row
and no byte row, so the register has a length message and zero byte messages at that time
(`regLenAgree_lone_length` in `Main/RegWalk.lean` is the machine-checked counterexample, and the
trace generator really produces this shape).

The AIR's real obligation is **group-local**: a length message is produced by the length row that
terminates a group, and that group has exactly `len` byte rows at `pos = 0 … len−1`.  That is
`regLenAgree_group` (`Main/RegWalk.lean`), proved from the group walk over `Chips.Reg`'s
constraints.  This definition is kept only so the false statement and its refutation stay
side by side; do not use it as a proof obligation. -/
def RegLenAgree (msgs : List Msg) (rid : Nat) : Prop :=
  ∀ len tp, lenMsg rid len tp ∈ msgs →
    msgs.countP (fun m => m.space = space ∧ m.tag = byteTag ∧ m.slot / 2 ^ posBits = rid ∧
      m.tp = tp) = len

end Register
end WasmBase
