import M5T1.Ent
import ZkFormal.Sha.Sound.Bridge

/-!
# M5T1.SegRt — the semantics of the `rt` enter leaf's constraints, field by field (F-2, F-3)

The `rt` enter leaf (`Ent.lean`) proves `Holds entAir pub tr` with `pub` = the boundary pair's
`BndRec.encode` bytes (`B_in` 450 B, then `B_out` 834 B, `BndLay.engF` / `callF`). Its rows read
nothing else. On row 0 of any satisfying trace every `ENT` constraint vanishes (`ent_row0`), so,
per output field and its rule `BndLay.outRule`:

* `copy_sem` — a copied field equals the input's field, byte for byte;
* `num_sem` — a constant field's little-endian byte `k` is `v / 256^k % 256`;
* `dig_sem` — a constant digest field is the constant bytes;
* `pad_sem` — `codeRoot`'s last 10 bytes are zero (S2);
* `in_sem` — the input record has `phase 1`, `inCall 0`, no Wasm part.

`EnterC.lean` turns these into the record-level statement (`enter_relC`). The F-2 statement
`segSoundRt_enter_from` (under the named contract `EnterView`) is superseded by `EnterC.enter_relC`
and removed.
-/

namespace M5T1.SegRt

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.BndLay

/-- Public value `i` as a natural. -/
def pv (pub : List Fp) (i : Nat) : Nat := (pub.getD i 0).toNat

/-- The byte strings of the two sides (each public value read as a byte). -/
def bytesOf (pub : List Fp) (a n : Nat) : ArenaCore.Bytes :=
  (List.range n).map fun i => UInt8.ofNat (pv pub (a + i))

section
variable {pub : List Fp} {tr : Trace Fp}

theorem ev_pub (r i : Nat) : ev tr 0 r pub (.pub i) = pv pub i := rfl

/-- Every `ENT` constraint vanishes on row 0. -/
theorem ent_row0 (H : Holds Ent.entAir pub tr) : ∀ e ∈ Ent.table.constraints, ev tr 0 0 pub e = 0 := by
  intro e he
  have hpos : 0 < tr.height 0 := Nat.pos_of_ne_zero (by unfold Trace.height; exact Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
  exact ev_of_eval (H.constr 0 (by decide) 0 hpos e he)

/-- A gated difference of two public values vanishing on row 0 makes them equal. -/
theorem gate_pub_eq {a b : Nat} (h : ev tr 0 0 pub (gate (Expr.pub a - Expr.pub b)) = 0) :
    pv pub a = pv pub b := by
  have h1 : ev tr 0 0 pub .isFirst = 1 := rfl
  have h2 := h
  unfold gate at h2
  rw [show (Expr.isFirst * (Expr.pub a - Expr.pub b)) = Expr.mul .isFirst (Expr.pub a - Expr.pub b) from rfl,
    ev_mul_gate _ h1] at h2
  have ha := ev_lt (tr := tr) (t := 0) (r := 0) (pub := pub) (.pub a)
  have hb := ev_lt (tr := tr) (t := 0) (r := 0) (pub := pub) (.pub b)
  rw [show (Expr.pub a - Expr.pub b) = Expr.add (.pub a) (.neg (.pub b)) from rfl, ev_add, ev_neg] at h2
  rw [ev_pub, ev_pub] at h2
  rw [ev_pub] at ha hb
  omega

/-- A gated public value minus a constant `v < p` vanishing on row 0 makes it `v`. -/
theorem gate_const_eq {a v : Nat} (hv : v < 2013265921) (h : ev tr 0 0 pub (gate (Expr.pub a - K v)) = 0) :
    pv pub a = v := by
  have h1 : ev tr 0 0 pub .isFirst = 1 := rfl
  have h2 := h
  unfold gate at h2
  rw [show (Expr.isFirst * (Expr.pub a - K v)) = Expr.mul .isFirst (Expr.pub a - K v) from rfl,
    ev_mul_gate _ h1] at h2
  have ha := ev_lt (tr := tr) (t := 0) (r := 0) (pub := pub) (.pub a)
  rw [show (Expr.pub a - K v) = Expr.add (.pub a) (.neg (.const v)) from rfl, ev_add, ev_neg, ev_const,
    ev_pub] at h2
  rw [ev_pub] at ha
  rw [Nat.mod_eq_of_lt hv] at h2
  omega

/-- A gated public value vanishing on row 0 is `0`. -/
theorem gate_zero_eq {a : Nat} (h : ev tr 0 0 pub (gate (Expr.pub a)) = 0) : pv pub a = 0 := by
  have h1 : ev tr 0 0 pub .isFirst = 1 := rfl
  unfold gate at h
  rw [show (Expr.isFirst * Expr.pub a) = Expr.mul .isFirst (Expr.pub a) from rfl, ev_mul_gate _ h1,
    ev_pub] at h
  exact h
end

/-- The input / output sides of the enter leaf's public values. -/
def SI : Side := ⟨engF, 0⟩
def SO : Side := ⟨callF, 450⟩

theorem mem_enter {e : Expr} (h : e ∈ enterCons SI SO) : e ∈ Ent.table.constraints := h

theorem field_mem {p : String × Nat} (hp : p ∈ callF) {r : ORule} (hr : outRule p.1 = r) {e : Expr}
    (he : e ∈ ruleCons SI SO p.1 p.2 r) : e ∈ Ent.table.constraints := by
  subst hr
  exact mem_enter (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, he⟩))

section
variable {pub : List Fp} {tr : Trace Fp} (H : Holds Ent.entAir pub tr)
include H

/-- **A copied field equals the input's**, byte for byte. -/
theorem copy_sem {p : String × Nat} (hp : p ∈ callF) (hr : outRule p.1 = .copy) :
    ∀ j < fw engF p.1, pv pub (engF.off p.1 + j) = pv pub (450 + callF.off p.1 + j) := by
  intro j hj
  have hm : gate (SI.b p.1 j - SO.b p.1 j) ∈ ruleCons SI SO p.1 p.2 .copy :=
    List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have := gate_pub_eq (ent_row0 H _ (field_mem hp hr hm))
  simpa [Side.b, SI, SO, Nat.zero_add, Nat.add_assoc] using this

/-- **A constant field**: little-endian byte `k` of the big-endian field is `v / 256^k % 256`. -/
theorem num_sem {p : String × Nat} (hp : p ∈ callF) {v : Nat} (hr : outRule p.1 = .num v) :
    ∀ k < fw callF p.1, pv pub (450 + callF.off p.1 + (fw callF p.1 - 1 - k)) = v / 256 ^ k % 256 := by
  intro k hk
  have hm : gate (SO.le p.1 k - K (v / 256 ^ k % 256)) ∈ ruleCons SI SO p.1 p.2 (.num v) :=
    List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩
  have := gate_const_eq (by have := Nat.mod_lt (v / 256 ^ k) (show 0 < 256 by decide); omega)
    (ent_row0 H _ (field_mem hp hr hm))
  simpa [Side.le, Side.b, SO] using this

/-- **A constant digest field** is the constant bytes. -/
theorem dig_sem {p : String × Nat} (hp : p ∈ callF) {b : List Nat} (hr : outRule p.1 = .dig b)
    (hb : ∀ j, b.getD j 0 < 256) : ∀ j < p.2, pv pub (450 + callF.off p.1 + j) = b.getD j 0 := by
  intro j hj
  have hm : gate (SO.b p.1 j - K (b.getD j 0)) ∈ ruleCons SI SO p.1 p.2 (.dig b) :=
    List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have := gate_const_eq (by have := hb j; omega) (ent_row0 H _ (field_mem hp hr hm))
  simpa [Side.b, SO] using this

/-- **A padded field**: the bytes after the first `n` are zero (S2: `codeRoot = h ‖ 0^10`). -/
theorem pad_sem {p : String × Nat} (hp : p ∈ callF) {n : Nat} (hr : outRule p.1 = .pad n) :
    ∀ j < p.2 - n, pv pub (450 + callF.off p.1 + (n + j)) = 0 := by
  intro j hj
  have hm : gate (SO.b p.1 (n + j)) ∈ ruleCons SI SO p.1 p.2 (.pad n) :=
    List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have := gate_zero_eq (ent_row0 H _ (field_mem hp hr hm))
  simpa [Side.b, SO] using this

/-- **The input side**: `phase 1`, `inCall 0`, no Wasm part. -/
theorem in_sem {f : String} {v : Nat} (hf : (f, v) ∈ [("phase", 1), ("inCall", 0), ("wasmTag", 0)]) :
    ∀ k < fw engF f, pv pub (engF.off f + (fw engF f - 1 - k)) = v / 256 ^ k % 256 := by
  intro k hk
  have hs : constF SI f v ⊆ enterCons SI SO := by
    intro e he
    unfold enterCons
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hf
    simp only [List.mem_append]
    rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [he]
  have hm : gate (SI.le f k - K (v / 256 ^ k % 256)) ∈ constF SI f v :=
    List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩
  have := gate_const_eq (by have := Nat.mod_lt (v / 256 ^ k) (show 0 < 256 by decide); omega)
    (ent_row0 H _ (mem_enter (hs hm)))
  simpa [Side.le, Side.b, SI] using this
end

#print axioms copy_sem
#print axioms num_sem
#print axioms dig_sem
#print axioms pad_sem
#print axioms in_sem

end M5T1.SegRt
