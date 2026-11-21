import M5T1.Obl
import M5T1.Ent
import ZkFormal.Sha.Sound.Bridge

/-!
# M5T1.SegRt — `SegSoundRt` (relative form) for the `rt` enter leaf, as a reduction (F-2)

The `rt` enter leaf (`Ent.lean`) proves `Holds entAir pub tr` with `pub` = the boundary pair's
`BndRec.encode` bytes (`B_in` 408 B, then `B_out` 784 B). Its rows read nothing else.

* `ent_row0`: every constraint of `ENT` vanishes on row 0 of any satisfying trace;
* **`enter_bytes`**: hence, field by field, `B_out` carries `B_in`'s claim digest, indices, state
  and context roots, totals, in-flight counters, accumulators and `vmAcc` byte for byte
  (`carried_eq`), `B_in` is out of a call (`phase 1`, `inCall 0`, no Wasm part) and `B_out` in a
  call (`phase 6`, `inCall 1`, Wasm part present, clock `0`) (`const_eq`);
* **`segSoundRt_enter_from`**: the relative obligation (`Obl.TmplSoundFrom`) for the enter edge,
  from the constraint semantics above and one **named view contract** `EnterView V`: a boundary
  pair in this byte relation, whose input record is the view of `x`, has `x = eng I c` with `c`
  non-final and its output record is the view of `call I c [] q .pre` for some query `q`. The
  contract is what the other components owe: the position kind inside `stRoot` (lane B,
  review-D7 I3: a finished engine must not enter a call), lane A's `.pre` Wasm record (PREP, the
  `.pre → .ent` seam) and the clear fields (`V.clear`, lane F/E: `t = 0`, `rPrepaid` = the
  query's prepaid gas — checked against the receipt by the resume leaf).

The resume edge's AIR (`Rx.lean` + `BndLay.resumeCons`) has the same byte-level structure; its
`SegSoundRt` additionally needs the composition of the row facts (`Bus.rx_rel_of_holds`,
`SpecLink`, `MsgSpec`, the `MSG` row lemma) into `estepO (strictO (K ++ [(q, r)])) I.prog c`
— open (README).
-/

namespace M5T1.SegRt

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.BndLay
open NearSpec NearSpecV3 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1

/-- Public value `i` as a natural. -/
def pv (pub : List Fp) (i : Nat) : Nat := (pub.getD i 0).toNat

section
variable {pub : List Fp} {tr : Trace Fp}

theorem ev_pub (r i : Nat) : ev tr 0 r pub (.pub i) = pv pub i := rfl

/-- Every `ENT` constraint vanishes on row 0. -/
theorem ent_row0 (H : Holds Ent.entAir pub tr) : ∀ e ∈ Ent.table.constraints, ev tr 0 0 pub e = 0 := by
  intro e he
  have hl := (H.logBound 0 (by decide)).1
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
end

/-- The input / output sides of the enter leaf's public values. -/
def SI : Side := ⟨engF, 0⟩
def SO : Side := ⟨callF, 408⟩

theorem mem_enter {e : Expr} (h : e ∈ enterCons SI SO) : e ∈ Ent.table.constraints := h

/-- **The carried fields, byte for byte.** -/
theorem carried_eq {pub : List Fp} {tr : Trace Fp} (H : Holds Ent.entAir pub tr) {f : String}
    (hf : f ∈ carried ++ ["gasUsed", "gasBurnt", "balanceBurnt", "compute", "rBurnt", "rUsed"])
    {j : Nat} (hj : j < fw engF f) :
    pv pub (engF.off f + j) = pv pub (408 + callF.off f + j) := by
  have hm : gate (SI.b f j - SO.b f j) ∈ enterCons SI SO := by
    unfold enterCons
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨f, hf, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩
  have := gate_pub_eq (ent_row0 H _ (mem_enter hm))
  simpa [Side.b, SI, SO, Nat.zero_add, Nat.add_assoc] using this

/-- The relabelled fields of the enter edge: `(side, field, value)`. -/
def relabel : List (Side × String × Nat) :=
  [(SI, "phase", 1), (SI, "inCall", 0), (SI, "wasmTag", 0), (SO, "phase", 6), (SO, "inCall", 1),
   (SO, "wasmTag", 1), (SO, "t", 0)]

/-- **The relabelled fields**: `B_in` is out of a call (`phase 1`, `inCall 0`, no Wasm part),
`B_out` in a call (`phase 6`, `inCall 1`, Wasm part present, clock `0`); little-endian byte `k` of
each big-endian field. -/
theorem const_eq {pub : List Fp} {tr : Trace Fp} (H : Holds Ent.entAir pub tr) :
    ∀ x ∈ relabel, ∀ k < fw x.1.L x.2.1,
      pv pub (x.1.base + x.1.L.off x.2.1 + (fw x.1.L x.2.1 - 1 - k)) = x.2.2 / 256 ^ k % 256 := by
  intro ⟨S, f, v⟩ hx k hk
  have hs : constF S f v ⊆ enterCons SI SO := by
    intro e he
    unfold enterCons relabel at *
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hx
    simp only [List.mem_append]
    rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [he]
  have hm : gate (S.le f k - K (v / 256 ^ k % 256)) ∈ constF S f v :=
    List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩
  exact gate_const_eq (by have := Nat.mod_lt (v / 256 ^ k) (show 0 < 256 by decide); omega)
    (ent_row0 H _ (mem_enter (hs hm)))

/-! ## The relative obligation for the enter edge -/

/-- The byte strings of the two sides (each public value read as a byte). -/
def bytesOf (pub : List Fp) (a n : Nat) : ArenaCore.Bytes :=
  (List.range n).map fun i => UInt8.ofNat (pv pub (a + i))

/-- The enter leaf's byte relation: what `ENT`'s constraints say about the public values. -/
def EnterRel (pub : List Fp) : Prop := ∃ tr : Trace Fp, ∀ e ∈ Ent.table.constraints, ev tr 0 0 pub e = 0

/-- **The view contract the enter edge relies on** (the other components' obligations, see the
module header): a public boundary pair in `EnterRel` whose input bytes are `x`'s record has
`x = eng I c` with `c` non-final, and its output bytes are the record of `call I c [] q .pre`
for some `q`. -/
def EnterView (V : ViewImpl) : Prop :=
  ∀ (pub : List Fp) (x : RConf), EnterRel pub → (∀ i < 1192, pv pub i < 256) →
    (V.bnd x).encode = bytesOf pub 0 408 →
    ∃ I c q, x = .base (.eng I c) ∧ (∀ out, c.pos ≠ .done out) ∧
      (V.bnd (.call I c [] q .pre)).encode = bytesOf pub 408 784

/-- The enter leaf's trace predicate at digest boundaries: the AIR holds, every public value is
a byte (the leaf hashes them as bytes), and the digests are those of the two sides. -/
def EntHolds (d d' : ArenaCore.Bytes) (w : List Fp × Trace Fp) : Prop :=
  Holds Ent.entAir w.1 w.2 ∧ (∀ i < 1192, pv w.1 i < 256) ∧
    d = bdigest (bytesOf w.1 0 408) ∧ d' = bdigest (bytesOf w.1 408 784)

/-- **`SegSoundRt` (relative form) for the enter edge**: under the view contract, an accepted enter
leaf whose input digest opens to `x` has an output digest that opens to an `MRt.enter` successor
of `x`, or there is a SHA-384 (42-B) collision. -/
theorem segSoundRt_enter_from (V : ViewImpl) (hV : EnterView V) (d d' : ArenaCore.Bytes)
    (w : List Fp × Trace Fp) (x : RConf) (hh : EntHolds d d' w) (hx : bndOf V.bnd x = d) :
    Sha384Coll ∨ ∃ x', bndOf V.bnd x' = d' ∧ Meaning .rt x x' := by
  classical
  obtain ⟨H, hb, hd, hd'⟩ := hh
  have hrel : EnterRel w.1 := ⟨w.2, ent_row0 H⟩
  by_cases he : (V.bnd x).encode = bytesOf w.1 0 408
  · obtain ⟨I, c, q, rfl, hc, ho⟩ := hV w.1 _ hrel hb he
    refine .inr ⟨.call I c [] q .pre, ?_, .enter I c q hc⟩
    simp only [bndOf]; rw [ho, hd']
  · exact .inl ⟨_, _, he, by rw [← hd]; exact hx⟩

#print axioms carried_eq
#print axioms const_eq
#print axioms segSoundRt_enter_from

end M5T1.SegRt
