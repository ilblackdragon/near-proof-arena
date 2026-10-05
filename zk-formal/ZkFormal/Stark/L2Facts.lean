import ZkFormal.Stark.NpBounds
import ZkFormal.Stark.Compose
import ZkFormal.Bcs.TransFinal

/-!
# ZkFormal.Stark.L2Facts — side conditions of L2's transport for np-udr-stark

The hypotheses of `Bcs.Transport.stark_romSound_rbr_of` that are about L4's
IOP: position parameters, `queryLog ≤ posBits` on admissible headers, chunk
counts, and the verifier's unit query budget `NVu`.  The `QUERY`-weight budget
(`qWeight chunkDec ≤ numChunks`) is `ChunkQueryBoundStmt`, proved in
`Stark/ChunkBound.lean`.
-/

namespace ZkFormal.Stark

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Air

section
variable (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
  (A : Air)

theorem np_posPerChunk_pos : 0 < (Iop.verifier F K A Params.default).posPerChunk := by
  show 0 < 9; decide

theorem np_pos_bits :
    (Iop.verifier F K A Params.default).posPerChunk * (Iop.verifier F K A Params.default).posBits
      ≤ 256 := by
  show 9 * 26 ≤ 256; decide

theorem np_numChunks : 2 ≤ (Iop.verifier F K A Params.default).numChunks ∧
    (Iop.verifier F K A Params.default).numChunks ≤ 2 ^ 32 := by
  show 2 ≤ 24 ∧ 24 ≤ 2 ^ 32; decide

/-- `queryLog ≤ posBits` on admissible headers (any parameters). -/
theorem np_queryLog_le_posBits (prm : Params) (hdr : List Nat)
    (h : (Iop.verifier F K A prm).headerOk hdr = true) :
    (Iop.verifier F K A prm).queryLog hdr ≤ (Iop.verifier F K A prm).posBits := by
  show queryLog A prm hdr ≤ prm.posBits
  have hl : ∀ L ∈ layout A prm hdr, L.lde ≤ prm.posBits := by
    intro L hL
    change headerOk A prm hdr = true at h
    simp only [headerOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨_, hall⟩, _⟩, _⟩ := h
    simp only [layout, List.mem_map] at hL
    obtain ⟨⟨T, l⟩, hmem, rfl⟩ := hL
    exact (hall (T, l) hmem).2
  unfold queryLog
  apply foldr_max_le (Nat.zero_le _)
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨L, hL, rfl⟩ := hx
  exact hl L hL

/-- L2's `starkTree` of the np IOP is L4's deployed verifier. -/
theorem starkTree_np (prm : Params) :
    Bcs.starkTree (F := F) (Iop.verifier F K A prm) = verifier F K A prm := rfl

/-- Unit query budget of `starkTree (Iop.verifier …)`: `NVu`. -/
theorem np_starkTree_unit (prm : Params) (pub cb pb : Bytes) :
    OracleComp.QueryBound unitWeight
      ((Bcs.starkTree (F := F) (Iop.verifier F K A prm)).tree pub cb pb) (NVu A prm) :=
  verifier_queryBound' A prm pub cb pb

end

/-- **(Q3)** The compiled verifier makes at most `numChunks` `QUERY`-chunk
queries (all other queries carry tags `0x00..0x04`, which `chunkDec` rejects). -/
def ChunkQueryBoundStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F]
    (V : IopSpec F K) (pub cb pb : Bytes),
    OracleComp.QueryBound (qWeight Bcs.chunkDec) (Bcs.compile (F := F) V pub cb pb) V.numChunks

end ZkFormal.Stark
