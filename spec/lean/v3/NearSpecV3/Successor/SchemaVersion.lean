import NearSpecV3.Successor.Config

/-!
# Versioned claim/witness envelope (workplan item 8, "versioned claim/witness schema")

`spec/claim-v3-versioning.md` defines a versioned envelope with an explicit schema-version field:

```
claim.bin   = bytes "near-arena-claim"   ‖ u32 schema_version ‖ body
witness.bin = bytes "near-arena-witness" ‖ u32 schema_version ‖ u8 encoding ‖ body
```

Schema version 3 is the only one defined. Its claim body is the `near-arena-claim-v3` file after
its format tag; its witness body is the `near-arena-witness-v3` (`encoding = 0`, state witness in
the clear) or `near-arena-cwitness-v3` (`encoding = 1`, the distributed zstd bytes) file after its
format tag.

**Legacy rule.** A file that does not start with an envelope tag is an unversioned file and is
schema version 3 by definition. It is passed to the existing decoders unchanged, so every existing
corpus, fixture and census case is decided exactly as before (`checkVersioned_legacy`).

The envelope is a transport format. The relation stays the relation over the canonical v3 bytes:
`normalizeClaim`/`normalizeWitness` rewrite an envelope to those bytes, and `checkVersioned` is
`checkSuccessor` after that rewrite (`checkVersioned_versioned`). An unsupported schema version or
encoding is rejected (`invalid:`), never decided as another version.

The tags are distinguished by their borsh length prefix: the envelope tags are 16 and 18 bytes, the
legacy tags 19 (`claim-v3`), 21 (`witness-v3`) and 22 (`cwitness-v3`), so the first byte of a file
already says which rule applies.
-/

namespace NearSpecV3.Successor.Schema

open NearSpec NearSpecV3 NearSpecV3.Successor

/-- `"near-arena-claim"` (16 bytes). -/
def claimFamily : Bytes :=
  [110, 101, 97, 114, 45, 97, 114, 101, 110, 97, 45, 99, 108, 97, 105, 109]

/-- `"near-arena-witness"` (18 bytes). -/
def witnessFamily : Bytes :=
  [110, 101, 97, 114, 45, 97, 114, 101, 110, 97, 45, 119, 105, 116, 110, 101, 115, 115]

/-- The schema version every currently defined body has. -/
def currentVersion : Nat := 3

/-- A borsh byte string: `u32` length ‖ bytes. -/
def bstr (b : Bytes) : Bytes := u32 b.length ++ b

/-- The canonical (unversioned) file for a claim body. -/
def legacyClaim (body : Bytes) : Bytes := bstr claimTag ++ body

/-- The canonical (unversioned) file for a witness body: encoding 0 is in the clear, 1 is the
compressed format. -/
def legacyWitness (encoding : Nat) (body : Bytes) : Bytes :=
  bstr (if encoding == 1 then witnessTagC else witnessTag) ++ body

/-- The versioned claim envelope. -/
def encodeClaimV (v : Nat) (body : Bytes) : Bytes := bstr claimFamily ++ u32 v ++ body

/-- The versioned witness envelope. -/
def encodeWitnessV (v encoding : Nat) (body : Bytes) : Bytes :=
  bstr witnessFamily ++ u32 v ++ u8 encoding ++ body

/-- Read the envelope of a claim: `(schema version, canonical bytes)`. -/
def normalizeClaim (bs : Bytes) : Except String (Nat × Bytes) :=
  match bs with
  | 16 :: 0 :: 0 :: 0 :: rest =>
    if rest.take 16 == claimFamily then
      match readU32 (rest.drop 16) with
      | some (3, body) => .ok (3, legacyClaim body)
      | some (v, _) => .error s!"invalid: unsupported claim schema version {v}"
      | none => .error "decode: truncated claim schema version"
    else .ok (currentVersion, bs)
  | _ => .ok (currentVersion, bs)

/-- Read the envelope of a witness: `(schema version, encoding, canonical bytes)`. An unversioned
file reports encoding 1 when it carries the compressed tag and 0 otherwise. -/
def normalizeWitness (bs : Bytes) : Except String (Nat × Nat × Bytes) :=
  match bs with
  | 18 :: 0 :: 0 :: 0 :: rest =>
    if rest.take 18 == witnessFamily then
      match readU32 (rest.drop 18) with
      | some (3, 0 :: body) => .ok (3, 0, legacyWitness 0 body)
      | some (3, 1 :: body) => .ok (3, 1, legacyWitness 1 body)
      | some (3, e :: _) => .error s!"invalid: unsupported witness encoding {e}"
      | some (3, []) => .error "decode: truncated witness encoding"
      | some (v, _) => .error s!"invalid: unsupported witness schema version {v}"
      | none => .error "decode: truncated witness schema version"
    else .ok (currentVersion, 0, bs)
  | 22 :: _ => .ok (currentVersion, 1, bs)
  | _ => .ok (currentVersion, 0, bs)

/-- The successor checker on a possibly versioned pair of files. -/
def checkVersioned (cfg : ProtocolCfg) (c w : Bytes) : Except String Unit := do
  let (_, c') ← normalizeClaim c
  let (_, _, w') ← normalizeWitness w
  checkSuccessor cfg c' w'

/-- The observable form, for `--emit`/`--blind`. -/
def checkVersionedObs (cfg : ProtocolCfg) (blind : Bool) (c w : Bytes) : Except String Observable := do
  let (_, c') ← normalizeClaim c
  let (_, _, w') ← normalizeWitness w
  checkSuccessorObs cfg blind c' w'

/-! ## The legacy rule: unversioned files are untouched -/

theorem normalizeClaim_unversioned (bs : Bytes) (h : bs.head? ≠ some 16) :
    normalizeClaim bs = .ok (currentVersion, bs) := by
  unfold normalizeClaim
  split
  · simp at h
  · rfl

theorem normalizeWitness_unversioned (bs : Bytes) (h : bs.head? ≠ some 18) :
    ∃ e, normalizeWitness bs = .ok (currentVersion, e, bs) := by
  unfold normalizeWitness
  split
  · simp at h
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-- Every existing `claim.bin` starts with the 19-byte `near-arena-claim-v3` tag. -/
theorem legacyClaim_head (body : Bytes) : (legacyClaim body).head? = some 19 := by
  simp [legacyClaim, bstr, claimTag, u32, leN]

/-- Every existing `witness.bin` starts with the 21- or 22-byte legacy tag. -/
theorem legacyWitness_head (e : Nat) (body : Bytes) :
    (legacyWitness e body).head? = some 21 ∨ (legacyWitness e body).head? = some 22 := by
  unfold legacyWitness
  split <;> simp [bstr, witnessTag, witnessTagC, u32, leN]

/-- **No verdict movement on unversioned inputs.** For every claim and witness that does not start
with an envelope tag — which includes every legacy file — `checkVersioned` is `checkSuccessor`. -/
theorem checkVersioned_legacy (cfg : ProtocolCfg) (c w : Bytes)
    (hc : c.head? ≠ some 16) (hw : w.head? ≠ some 18) :
    checkVersioned cfg c w = checkSuccessor cfg c w := by
  obtain ⟨e, he⟩ := normalizeWitness_unversioned w hw
  simp [checkVersioned, normalizeClaim_unversioned c hc, he, bind, Except.bind]

/-- The same for the canonical legacy files themselves. -/
theorem checkVersioned_legacy_files (cfg : ProtocolCfg) (cb wb : Bytes) (e : Nat) :
    checkVersioned cfg (legacyClaim cb) (legacyWitness e wb) =
      checkSuccessor cfg (legacyClaim cb) (legacyWitness e wb) := by
  apply checkVersioned_legacy
  · rw [legacyClaim_head]; decide
  · rcases legacyWitness_head e wb with h | h <;> rw [h] <;> decide

/-! ## The envelope decodes to the canonical bytes -/

theorem normalizeClaim_versioned (body : Bytes) :
    normalizeClaim (encodeClaimV 3 body) = .ok (3, legacyClaim body) := by
  simp [normalizeClaim, encodeClaimV, bstr, claimFamily, u32, leN, readU32, readLE, takeN, leNat]

theorem normalizeWitness_versioned (e : Nat) (he : e = 0 ∨ e = 1) (body : Bytes) :
    normalizeWitness (encodeWitnessV 3 e body) = .ok (3, e, legacyWitness e body) := by
  rcases he with rfl | rfl <;>
    simp [normalizeWitness, encodeWitnessV, bstr, witnessFamily, u32, u8, leN, readU32, readLE,
      takeN, leNat]

/-- **The envelope is faithful.** A version-3 envelope is decided exactly as its canonical file. -/
theorem checkVersioned_versioned (cfg : ProtocolCfg) (cb wb : Bytes) (e : Nat) (he : e = 0 ∨ e = 1) :
    checkVersioned cfg (encodeClaimV 3 cb) (encodeWitnessV 3 e wb) =
      checkSuccessor cfg (legacyClaim cb) (legacyWitness e wb) := by
  simp [checkVersioned, normalizeClaim_versioned, normalizeWitness_versioned e he, bind,
    Except.bind]

/-- An unsupported schema version is rejected, not decided as version 3. -/
theorem normalizeClaim_unsupported (body : Bytes) :
    ∃ e, normalizeClaim (encodeClaimV 4 body) = .error e := by
  simp [normalizeClaim, encodeClaimV, bstr, claimFamily, u32, leN, readU32, readLE, takeN, leNat]

theorem normalizeWitness_bad_encoding (body : Bytes) :
    ∃ e, normalizeWitness (encodeWitnessV 3 2 body) = .error e := by
  simp [normalizeWitness, encodeWitnessV, bstr, witnessFamily, u32, u8, leN, readU32, readLE, takeN,
    leNat]

#print axioms checkVersioned_legacy
#print axioms checkVersioned_legacy_files
#print axioms checkVersioned_versioned
#print axioms normalizeClaim_unsupported
#print axioms normalizeWitness_bad_encoding

end NearSpecV3.Successor.Schema
