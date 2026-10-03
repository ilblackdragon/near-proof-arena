import ArenaCore.SHA256Fast
open ArenaCore

/-!
Test vectors for the compiled fast SHA-256 (`ArenaCore.sha256Fast`).  These
are compiled-evaluation checks (`#guard`), complementary to the kernel proof
`sha256_eq_sha256Fast`: FIPS 180-2 vectors, and agreement with the
specification `SHA256` implementation run *without* the `@[csimp]` redirect
(`specSha256` below re-states the spec under a fresh name) on every padding
boundary length.
-/

/-- The specification algorithm under a name the `@[csimp]` lemma does not
redirect (compiled spec, for differential tests). -/
def specSha256 (m : Bytes) : Digest :=
  let p := SHA256.pad (m.map UInt8.toNat)
  SHA256.digestBytes (SHA256.blocks (p.length / 64) SHA256.H0 p)

#guard (sha256Fast []).toHex == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard (sha256Fast (Bytes.ofString "abc")).toHex ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard (sha256Fast (Bytes.ofString "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")).toHex ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard (sha256Fast (Bytes.ofString
  "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")).toHex ==
  "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
#guard (sha256Fast (List.replicate 1000000 0x61)).toHex ==
  "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"

/-- Pseudo-random test bytes. -/
def testBytes (n seed : Nat) : Bytes :=
  (List.range n).map fun i => UInt8.ofNat ((i * 7919 + seed * 104729 + i * i * 31) % 251)

#guard [0, 1, 3, 31, 32, 55, 56, 57, 63, 64, 65, 100, 119, 120, 127, 128, 129, 1000, 4096].all
  fun n => sha256Fast (testBytes n n) == specSha256 (testBytes n n)
-- `sha256` itself (redirected to `sha256Fast` when compiled) on the same inputs.
#guard [0, 55, 56, 63, 64, 65, 119, 120].all
  fun n => sha256 (testBytes n 3) == specSha256 (testBytes n 3)
