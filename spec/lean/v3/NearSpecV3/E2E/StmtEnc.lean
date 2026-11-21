import NearSpecV3.E2E.View

/-!
# E2E-M11h: the canonical encoding of the public statement `S` and `claimDigest`

The wrap's only public input is the D-2 statement `PublicStmt` (section A: protocol version,
chain id, epoch id, `chunk_inner`; section C: the trusted facts). This file fixes its bytes.

**`S = PublicStmt.encode s`** is the claim-v3 encoding (`spec/claim-v3.md` §2,
`Claim.encode`) of the claim with an **empty section B**: every field in claim order, with the
block vector replaced by its empty encoding `u32 0` (`00 00 00 00`). Hence

* `S = stmtPre s ++ [0,0,0,0] ++ stmtPost s` (`encode_splice`), and the claim the relation checks is
  the same bytes with the private block vector in place of the four zero bytes:
  `assemble s.ci secB s.secC = stmtPre s ++ encList BlockRec.encode secB ++ stmtPost s`
  (`assemble_splice`). `stmtPre` runs from the claim tag through `chunk_inner`; `stmtPost` from
  `rs_data_parts` through `genesis_chunk_extra`. (Lane I's I-1 working encoding, the claim with
  the block vector *and its count* cut out, is `S` without the four zero bytes.)
* **Canonical and injective**: `PublicStmt.decode` (the strict claim decoder, then
  `blocks = []`) inverts it on well-formed statements (`decode_encode`), so `encode_inj`.
* **`claimDigest s = bdigest S`** (42-B truncated SHA-384, U-10), the value every boundary's
  `claimDigest` field carries and the wrap hashes into `D_wrap`; `claimDigest_binding`: equal
  digests of well-formed statements are equal statements or a SHA-384 collision.

Well-formedness (`PublicStmt.wf`) is `Claim.wf` of the empty-B claim: field widths (u16/u32/u64/
u128 ranges, 32-byte hashes, `u32` lengths). `assemble_wf`: a well-formed assembled claim has a
well-formed statement.
-/

namespace NearSpecV3.E2E
open NearSpec NearSpecV3 NearSpecV3.E2E.Bnd

/-- The public parts of a claim (section A). -/
def pubOf (c : Claim) : ChunkPub :=
  { protocolVersion := c.protocolVersion, chainId := c.chainId, epochId := c.epochId,
    chunkInner := c.chunkInner }

/-- Section C of a claim. -/
def secCOf (c : Claim) : SecC :=
  { rsDataParts := c.rsDataParts, rsTotalParts := c.rsTotalParts, epochs := c.epochs,
    epochStartAfter := c.epochStartAfter, applyFacts := c.applyFacts, txValid := c.txValid,
    genesisChunkExtra := c.genesisChunkExtra }

/-- Every claim is the assembly of its public parts, its section B and its section C. -/
theorem assembleClaim_pub (c : Claim) : assembleClaim (pubOf c) c.blocks (secCOf c) = c := by
  cases c; rfl

/-- The claim of a statement with an empty section B. -/
def PublicStmt.claim (s : PublicStmt) : Claim := assembleClaim s.ci [] s.secC

/-- **The canonical statement bytes `S`.** -/
def PublicStmt.encode (s : PublicStmt) : Bytes := s.claim.encode

/-- Well-formed statements (field widths). -/
def PublicStmt.wf (s : PublicStmt) : Bool := s.claim.wf

/-- The strict decoder: a claim with an empty section B. -/
def PublicStmt.decode (b : Bytes) : Option PublicStmt :=
  match decodeClaim b with
  | some c => if c.blocks.isEmpty then some ⟨pubOf c, secCOf c⟩ else none
  | none => none

theorem PublicStmt.eta (s : PublicStmt) : (⟨pubOf s.claim, secCOf s.claim⟩ : PublicStmt) = s := by
  obtain ⟨⟨a, b, c, d⟩, ⟨e, f, g, h, i, j, k⟩⟩ := s; rfl

/-- **Round trip.** -/
theorem PublicStmt.decode_encode (s : PublicStmt) (h : s.wf = true) :
    PublicStmt.decode s.encode = some s := by
  unfold PublicStmt.decode PublicStmt.encode
  rw [decodeClaim_encode _ h]
  simp only [PublicStmt.claim, assembleClaim, List.isEmpty_nil, ite_true]
  exact congrArg some (PublicStmt.eta s)

/-- **The encoding is injective on well-formed statements.** -/
theorem PublicStmt.encode_inj {s t : PublicStmt} (hs : s.wf = true) (ht : t.wf = true)
    (h : s.encode = t.encode) : s = t := by
  have a := PublicStmt.decode_encode s hs
  rw [h, PublicStmt.decode_encode t ht] at a
  exact (Option.some.inj a).symm

/-- **`claimDigest`**: the 42-B truncated SHA-384 of `S`. -/
def claimDigest (s : PublicStmt) : Bytes := bdigest s.encode

/-- **Binding of `claimDigest`.** -/
theorem claimDigest_binding {s t : PublicStmt} (hs : s.wf = true) (ht : t.wf = true)
    (h : claimDigest s = claimDigest t) : s = t ∨ Sha384Coll := by
  classical
  by_cases he : s.encode = t.encode
  · exact .inl (PublicStmt.encode_inj hs ht he)
  · exact .inr ⟨_, _, he, h⟩

/-! ## `S` and the assembled claim differ only in the block vector -/

/-- The bytes of `S` before the block vector (claim tag through `chunk_inner`). -/
def stmtPre (s : PublicStmt) : Bytes :=
  borshBytes claimTag ++ borshBytes statementIdV3 ++ u32 s.ci.protocolVersion ++
  borshBytes s.ci.chainId ++ s.ci.epochId ++ borshBytes s.ci.chunkInner

/-- The bytes of `S` after the block vector (`rs_data_parts` through `genesis_chunk_extra`). -/
def stmtPost (s : PublicStmt) : Bytes :=
  u16 s.secC.rsDataParts ++ u16 s.secC.rsTotalParts ++
  encList EpochRec.encode s.secC.epochs ++ borshBytes s.secC.epochStartAfter ++
  encList ApplyFacts.encode s.secC.applyFacts ++ borshBytes s.secC.txValid ++
  encOpt borshBytes s.secC.genesisChunkExtra

/-- **The assembled claim is `S` with the block vector spliced in.** -/
theorem assemble_splice (s : PublicStmt) (secB : List BlockRec) :
    assemble s.ci secB s.secC = stmtPre s ++ encList BlockRec.encode secB ++ stmtPost s := by
  simp only [assemble, assembleClaim, Claim.encode, stmtPre, stmtPost, List.append_assoc]

/-- The empty block vector is four zero bytes. -/
theorem encList_blocks_nil : encList BlockRec.encode [] = [0, 0, 0, 0] := by decide

/-- **`S` = prefix, `u32 0`, suffix.** -/
theorem encode_splice (s : PublicStmt) : s.encode = stmtPre s ++ [0, 0, 0, 0] ++ stmtPost s := by
  rw [← encList_blocks_nil, ← assemble_splice]; rfl

/-- A well-formed assembled claim has a well-formed statement. -/
theorem assemble_wf (s : PublicStmt) (secB : List BlockRec)
    (h : (assembleClaim s.ci secB s.secC).wf = true) : s.wf = true := by
  simp only [PublicStmt.wf, PublicStmt.claim, Claim.wf, assembleClaim, Bool.and_eq_true,
    List.length_nil, List.all_nil] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, rfl⟩, trivial⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩

#print axioms PublicStmt.decode_encode
#print axioms PublicStmt.encode_inj
#print axioms claimDigest_binding
#print axioms assemble_splice
#print axioms encode_splice
#print axioms assemble_wf

end NearSpecV3.E2E
