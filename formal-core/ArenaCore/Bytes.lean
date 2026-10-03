/-!
# ArenaCore.Bytes

Byte strings and the small set of encodings needed to *state* claims and
artifact bindings.  Everything here is structurally recursive so that the
Lean kernel can evaluate it (`decide +kernel`) on concrete inputs; no
well-founded recursion, no `partial`, no `implemented_by`.

`Bytes` is `List UInt8` (not `ByteArray`) on purpose: the kernel reduces
lists cheaply and proofs about lists need no extra library.
-/

namespace ArenaCore

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-- A 32-byte SHA-256 digest (length is not enforced by the type; statements
that need it state `d.length = 32`). -/
abbrev Digest := Bytes

namespace Bytes

/-- Byte at position `i`, `0` when out of range. -/
def getD0 (b : Bytes) (i : Nat) : UInt8 := b.getD i 0

/-- Big-endian encoding of `n mod 256^w` in exactly `w` bytes. -/
def beN : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, n => beN w (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- Little-endian encoding of `n mod 256^w` in exactly `w` bytes. -/
def leN : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: leN w (n / 256)

/-- Big-endian decoding (any length). -/
def beToNat (b : Bytes) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- Little-endian decoding (any length). -/
def leToNat : Bytes → Nat
  | [] => 0
  | x :: xs => x.toNat + 256 * leToNat xs

theorem beN_length (w n : Nat) : (beN w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [beN, ih]

theorem leN_length (w n : Nat) : (leN w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [leN, ih]

/-- Lowercase hex rendering (for `#eval` diagnostics only; never needed by a
certificate). -/
def toHex (b : Bytes) : String :=
  let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList (b.flatMap fun x => [digit (x.toNat / 16), digit (x.toNat % 16)])

/-- Parse lowercase/uppercase hex (diagnostics / test vectors). Returns `none`
on odd length or a non-hex character. -/
def ofHex? (s : String) : Option Bytes :=
  let val (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
    else none
  let rec go : List Char → Option Bytes
    | [] => some []
    | [_] => none
    | a :: b :: rest => do
        let x ← val a
        let y ← val b
        let tl ← go rest
        pure (UInt8.ofNat (16 * x + y) :: tl)
  go s.toList

/-- ASCII/UTF-8 bytes of a string literal (test vectors). -/
def ofString (s : String) : Bytes := s.toUTF8.toList

end Bytes

end ArenaCore
