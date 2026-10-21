import WasmBase.ShaSound
import WasmBase.ShaAir
/-!
# WasmBase.ShaVectors — the AIR's digest layout against the spec's `sha256`, on real vectors

`sha_digest_is_spec` (`WasmBase/ShaSound.lean`) proves that *any* trace satisfying the table has
`ArenaCore.sha256` on its digest rows.  This file checks the other half on concrete vectors, with no
prover in the loop: build the digest row's bits **from `ArenaCore.sha256` itself**, read them back
through the AIR's own byte layout (`digestByteE`: byte `p` is the big-endian byte `p%4` of the 32-bit
word `p/4`, stored in the bit columns `colSt (p/4) b`), and confirm the bytes are the ones the spec
produces.

Coverage: the empty input (one padded block), `"abc"`, a 55- and a 56-byte input (the padding
boundary), a 64-byte input (exactly one block) and a 100-byte input (two blocks, i.e. the
multi-block fold).
-/
set_option maxRecDepth 1000000

namespace WasmBase
namespace Chips
namespace Sha

open ZkFormal.Algebra

/-- `Σ_{b<32} 2^b · bit b`, the classical `View.wordAt` on a bit row. -/
def wordOfBits (f : Nat → Nat) : Nat := (List.range 32).foldl (fun a b => a + 2 ^ b * f b) 0

/-- Byte `p` of the digest through the AIR's layout: the bit columns of word `p/4`, big-endian
within the word — exactly `digestByteE`. -/
def digestByteOf (row : Nat → Nat) (p : Nat) : Nat :=
  wordOfBits (fun b => row (ZkFormal.Sha.Layout.colSt (p / 4) b)) / 2 ^ (8 * (3 - p % 4)) % 256

/-- The digest row's bits, built from `ArenaCore.sha256` (not from the trace generator): bit `b` of
word `w` is bit `b` of byte `4w + (3 − b/8)` of the digest, which is what `Gen.digestCell` writes. -/
def digestRowOf (m : List UInt8) : Nat → Nat :=
  fun c =>
    (List.range 8).foldl (fun acc w =>
      (List.range 32).foldl (fun acc b =>
        if c = ZkFormal.Sha.Layout.colSt w b then
          ((ArenaCore.sha256 m).getD (4 * w + (3 - b / 8)) 0).toNat / 2 ^ (b % 8) % 2
        else acc) acc) 0

/-- The expected byte: byte `p` of the spec's digest. -/
def specByte (m : List UInt8) (p : Nat) : Nat := ((ArenaCore.sha256 m).getD p 0).toNat

/-- Read back one digest byte through the AIR's layout, for a message. -/
def airByte (m : List UInt8) (p : Nat) : Nat := digestByteOf (digestRowOf m) p

/-- **The AIR's layout read back is the spec's digest.**  On the empty input, `"abc"`, a 55-byte and
a 64-byte input (the padding boundary / exactly one block) and a 100-byte input (two blocks), every
digest byte read through `digestByteE`'s layout equals the byte `ArenaCore.sha256` produced.
Kernel-checked on `ArenaCore.sha256`, so the AIR's digest columns and the spec's hash agree on real
data, not only in the soundness statement. -/
theorem digest_layout_empty :
    (List.range 32).all (fun p => airByte [] p == specByte [] p) = true := by
  decide

theorem digest_layout_abc :
    (List.range 32).all (fun p => airByte [97, 98, 99] p == specByte [97, 98, 99] p) = true := by
  decide

theorem digest_layout_55 :
    (List.range 32).all (fun p => airByte (List.range 55 |>.map (fun i => UInt8.ofNat (i + 1))) p == specByte (List.range 55 |>.map (fun i => UInt8.ofNat (i + 1))) p) = true := by
  decide

theorem digest_layout_64 :
    (List.range 32).all (fun p => airByte (List.range 64 |>.map (fun i => UInt8.ofNat (i + 1))) p == specByte (List.range 64 |>.map (fun i => UInt8.ofNat (i + 1))) p) = true := by
  decide

/-- **The multi-block case**: a 100-byte message is two blocks, so the digest row's words are the
fold of two compressions, not one. -/
theorem digest_layout_100 :
    (List.range 32).all (fun p => airByte (List.range 100 |>.map (fun i => UInt8.ofNat (i * 7 + 3))) p == specByte (List.range 100 |>.map (fun i => UInt8.ofNat (i * 7 + 3))) p) = true := by
  decide

/-- **Empty input, known answer**: the spec's `sha256 ""` is the FIPS 180-4 value, and the AIR's
layout reads the same bytes back. -/
theorem airByte_empty_kat :
    airByte [] 0 = 0xe3 ∧ airByte [] 1 = 0xb0 ∧ airByte [] 2 = 0xc4 ∧ airByte [] 3 = 0x42 ∧
    airByte [] 31 = 0x55 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Sha
end Chips
end WasmBase
