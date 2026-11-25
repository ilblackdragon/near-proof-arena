import M5T1.Rx

/-!
# M5T1.Rb — `RB`: the resume edge's boundary rows (F-4)

One table, height 4, whose row 0 carries the resume leaf's boundary pair rules (`BndLay.rbCons`,
public values only: `bin` = the call record `callF`, `bout` = the engine record `engF`, at the
offsets of `Rx.PL`) and the edge's traffic with the two lanes it joins:

* **`STMQ`** (send; lane B's `STC`, cross-lane id 211): `[r_in, tag_out, rest_out]` — `r_in` is the
  input record's `stRoot` (14 three-byte limbs of the public bytes), `(tag_out, rest_out)` the
  output state's meta (`StHalfC.metaOf` of `stOfK κ I c'`: witnessed, 42 `RNG`-checked bytes);
* **`STMA`** (receive; id 212): `[r_out, tag_in, rest_in]` — `r_out` **is the output record's
  `stRoot`** (the public bytes: the field is not copied), `(tag_in, rest_in)` the input's opening;
* **`ACCD`** (send `[0]`, `[1]`): the two SHA-384 accumulator appends the `ACC` table must do
  (outcomes, outgoing receipts; `Acc.lean`).

Columns: `tgo`, `rso` (42), `tgi`, `rsi` (42), `cri` (7 carry bits of `receiptIdx + 1`).
-/

namespace M5T1

open ZkFormal.Air

namespace Rb

def L : Layout := [("tgo", 1), ("rso", 42), ("tgi", 1), ("rsi", 42), ("cri", 7)]
def T : Cols := ⟨L⟩
def c (s : String) (j : Nat := 0) : Expr := T.c s j

/-- The input side (`B_in`, a call record) and the output side (`B_out`) in the public values. -/
def SI : BndLay.Side := ⟨BndLay.callF, Rx.PL.off "bin"⟩
def SO : BndLay.Side := ⟨BndLay.engF, Rx.PL.off "bout"⟩

/-- Limb `j < 14` of a 42-byte string given byte-wise (big-endian within the limb). -/
def limb (b : Nat → Expr) (j : Nat) : Expr :=
  K 65536 * b (3 * j) + K 256 * b (3 * j + 1) + b (3 * j + 2)

def limbs (b : Nat → Expr) : List Expr := (List.range 14).map (limb b)

def constraints : List Expr :=
  ((List.range 7).map fun k => bool (c "cri" k)) ++
  (BndLay.rbCons SI SO (fun g k => Rx.pub g k) (fun k => c "cri" k) ++
  -- F-5: the input's Wasm part is lane A's `fin` record (`BndLay.finRule`)
  BndLay.finInCons SI)

def interactions : List Interaction :=
  [snd B_STMQ .isFirst (limbs (SI.b "stRoot") ++ [c "tgo"] ++ limbs (fun j => c "rso" j)),
   rcv B_STMA .isFirst (limbs (SO.b "stRoot") ++ [c "tgi"] ++ limbs (fun j => c "rsi" j))] ++
  ((List.range 42).map fun j => rcv B_RNG .isFirst [c "rso" j]) ++
  ((List.range 42).map fun j => rcv B_RNG .isFirst [c "rsi" j]) ++
  [snd B_ACCD .isFirst [K 0], snd B_ACCD .isFirst [K 1]]

def table : Table := { width := L.width, constraints, interactions, maxLog := 2 }

end Rb

end M5T1
