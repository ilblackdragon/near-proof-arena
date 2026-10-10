import NearSpecV3.PrepD0
import NearSpec.ClaimCodec

/-!
# A byte codec for the proof-carried `Hint`

The deployed v3 verifier splits the proof into a clear hint and a STARK proof
(V3-D0-DESIGN §2.1).  This module fixes the on-the-wire encoding of
`NearSpecV3.Hint` (`n`, `body`): `u32 n ‖ borshBytes body`, and proves the round
trip.  It is the `split`/`join`/`hintOf` half of the admission interface; the
`prep` half is `prepD0` composed with `Prep.encode`.
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

/-- Encode a hint: `u32 n ‖ borshBytes body`. -/
def Hint.encode (h : Hint) : Bytes := u32 h.n ++ borshBytes h.body

/-- Decode a hint, consuming all input. -/
def Hint.decode (bs : Bytes) : Option Hint :=
  match readU32 bs with
  | none => none
  | some (n, rest) =>
    match readBorshBytes rest with
    | none => none
    | some (body, rest') => if rest'.isEmpty then some ⟨n, body⟩ else none

theorem readBorshBytes_borsh (b : Bytes) (h : b.length < 256 ^ 4) :
    readBorshBytes (borshBytes b) = some (b, []) := by
  simpa using readBorshBytes_append b [] h

theorem Hint.decode_encode (h : Hint) (hn : h.n < 256 ^ 4) (hb : h.body.length < 256 ^ 4) :
    Hint.decode (Hint.encode h) = some h := by
  have h1 : readU32 (Hint.encode h) = some (h.n, borshBytes h.body) := by
    unfold Hint.encode readU32
    exact readLE_append 4 h.n (borshBytes h.body) hn
  have h2 : readBorshBytes (borshBytes h.body) = some (h.body, []) :=
    readBorshBytes_borsh h.body hb
  simp only [Hint.decode, h1, h2, List.isEmpty_nil, ↓reduceIte]

/-- The clear hint bytes followed by the STARK proof, with a length prefix. -/
def join (h π : Bytes) : Bytes := borshBytes h ++ π

/-- Split a proof back into the hint and the STARK proof. -/
def split (pb : Bytes) : Option (Bytes × Bytes) := readBorshBytes pb

theorem split_join (h π : Bytes) (hh : h.length < 256 ^ 4) :
    split (join h π) = some (h, π) := by
  show readBorshBytes (borshBytes h ++ π) = some (h, π)
  exact readBorshBytes_append h π hh

end ZkFormal.NearV3.Assembly
