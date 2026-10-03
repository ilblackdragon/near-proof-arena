/-!
# Bytes and borsh-style little-endian encodings

`Bytes` is `List UInt8`. Every definition here is structurally recursive so
that it reduces in the Lean kernel (`decide +kernel`); none uses well-founded
recursion, `implemented_by`, or `extern`.

Reference: borsh (as used by nearcore 2.13.4): integers are fixed-width little
endian; `Vec<T>`/`String` are a `u32` LE element count followed by elements.
-/

namespace NearSpec

abbrev Bytes := List UInt8

/-- `leN w x`: the `w` low-order bytes of `x`, little endian. -/
def leN : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, x => UInt8.ofNat (x % 256) :: leN w (x / 256)

def u8 (x : Nat) : Bytes := leN 1 x
def u16 (x : Nat) : Bytes := leN 2 x
def u32 (x : Nat) : Bytes := leN 4 x
def u64 (x : Nat) : Bytes := leN 8 x
def u128 (x : Nat) : Bytes := leN 16 x

/-- borsh `Vec<u8>` / `String`: `u32` length prefix then the raw bytes. -/
def borshBytes (b : Bytes) : Bytes := u32 b.length ++ b

/-- Little-endian bytes to `Nat`. -/
def leNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- Big-endian 32-bit words (used by SHA-256). -/
def be32 (x : Nat) : Bytes :=
  [UInt8.ofNat (x / 16777216 % 256), UInt8.ofNat (x / 65536 % 256),
   UInt8.ofNat (x / 256 % 256), UInt8.ofNat (x % 256)]

def be64 (x : Nat) : Bytes := be32 (x / 4294967296 % 4294967296) ++ be32 (x % 4294967296)

def zeros : Nat → Bytes
  | 0 => []
  | n + 1 => 0 :: zeros n

def zeroHash : Bytes := zeros 32

def concatAll : List Bytes → Bytes
  | [] => []
  | b :: bs => b ++ concatAll bs

/-! ## Strict decoding (executable checker side)

A `Parser α` consumes a prefix. Decoders are used by the checker executable and
by `Claim.decode`; the *relation* is stated in terms of the encoders. -/

abbrev Parser (α : Type) := Bytes → Option (α × Bytes)

def takeN : Nat → Parser Bytes
  | 0, bs => some ([], bs)
  | _ + 1, [] => none
  | n + 1, b :: bs => (takeN n bs).map fun (h, t) => (b :: h, t)

def readLE (w : Nat) : Parser Nat := fun bs => (takeN w bs).map fun (h, t) => (leNat h, t)

def readU8 : Parser Nat := readLE 1
def readU16 : Parser Nat := readLE 2
def readU32 : Parser Nat := readLE 4
def readU64 : Parser Nat := readLE 8
def readU128 : Parser Nat := readLE 16
def readHash : Parser Bytes := takeN 32

def readBorshBytes : Parser Bytes := fun bs =>
  match readU32 bs with
  | none => none
  | some (n, rest) => takeN n rest

/-- Read exactly `n` items with parser `p`. -/
def readMany {α : Type} (p : Parser α) : Nat → Parser (List α)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match p bs with
    | none => none
    | some (a, rest) =>
      match readMany p n rest with
      | none => none
      | some (as, rest') => some (a :: as, rest')

def expectBytes (want : Bytes) : Parser Unit := fun bs =>
  match readBorshBytes bs with
  | some (got, rest) => if got == want then some ((), rest) else none
  | none => none

end NearSpec
