import NearSpecV3.ChunkValidationD1

/-! # `Decode/Agree` — the D0 and D1 witness decoders agree on a D0-accepted stream

`decodeStateWitness` (D0, `NearSpecV3/WitnessV3.lean`) and `decodeStateWitnessD1`
(D1, `NearSpecV3/ChunkValidationD1.lean`) walk the same `ChunkStateWitness` byte
stream; the only difference is that at the two `transactions` / `new_transactions`
positions D0 reads a `pU32` count and demands `0`, while D1 reads a `pVec … pTxD1`.
A count of `0` is exactly a borsh empty vector, and `pVec` consumes the same four
bytes, so on a stream accepted by the D0 decoder the D1 decoder succeeds on the same
stream, sees `[]` in both transaction fields, and returns a witness whose every other
field is the D0 witness's field.

The work is done in two steps:

* `decodeStateWitness_shape` runs the D0 decoder once and records the whole parse
  (every parser application with its result, the succeeded tag checks, the
  empty-tail check, the size bound, and the fact that the returned record is built
  from exactly those results);
* `Agree` replays the D1 decoder against the same byte stream: `pU8` / `pHash` /
  `pChunkHeader` / `pTransition` / `pVec pEntry` / `pHash` are the same parser in
  both decoders, and the two `pU32` results are turned into `pVec … = .ok ([], …)`
  by `pVec_of_zero`.
-/

namespace Work.Decode.Agree

open NearSpec

/-- `pU32` ignores its label: the label shows up only in the error message. -/
theorem pU32_name_irrel (w₁ w₂ : String) (bs rest : Bytes) (n : Nat)
    (h : NearSpecV3.pU32 w₁ bs = .ok (n, rest)) :
    NearSpecV3.pU32 w₂ bs = .ok (n, rest) := by
  simp only [NearSpecV3.pU32, NearSpecV3.lift] at h ⊢
  cases hr : NearSpec.readU32 bs with
  | none => simp [hr] at h
  | some r => simpa [hr] using h

/-- **The arithmetic of the bridge.** A `u32` vector count of `0` followed by a `pVec`
at the same position: `pVec` reads the same four bytes and returns the empty list. -/
theorem pVec_of_zero {α : Type} (w₁ w₂ : String) (p : NearSpecV3.P α)
    (bs rest : Bytes) (h : NearSpecV3.pU32 w₁ bs = .ok (0, rest)) :
    NearSpecV3.pVec w₂ p bs = .ok ([], rest) := by
  simp only [NearSpecV3.pVec]
  rw [pU32_name_irrel w₁ (w₂ ++ " length") bs rest 0 h]
  rfl

/-- **The D0 decoder, unfolded.** If `decodeStateWitness bs` succeeds with `w0` then the
stream is under the size bound, every parser application of the decoder is pinned to
its result (the tags are `1` and the two transaction counts are `0`), nothing is left
over after the last field, and `w0` is the record built from exactly those results. -/
theorem decodeStateWitness_shape (bs : Bytes) (w0 : NearSpecV3.StateWitness)
    (h : NearSpecV3.decodeStateWitness bs = .ok w0) :
    ∃ (bs1 : Bytes) (eid : Bytes) (bs2 : Bytes) (ib : Bytes) (ci : NearSpecV3.ChunkInner)
      (bs3 : Bytes) (main : NearSpecV3.Transition) (bs4 : Bytes)
      (entries : List NearSpecV3.ProofEntry) (bs5 : Bytes) (arh : Bytes) (bs6 : Bytes)
      (bs7 : Bytes) (impl : List NearSpecV3.Transition) (bs8 : Bytes),
      ¬ NearSpecV3.lenT bs > NearSpecV3.MAX_WITNESS ∧
      NearSpecV3.pU8 "ChunkStateWitness tag" bs = .ok (1, bs1) ∧
      NearSpecV3.pHash "epoch_id" bs1 = .ok (eid, bs2) ∧
      NearSpecV3.pChunkHeader bs2 = .ok ((ib, ci), bs3) ∧
      NearSpecV3.pTransition bs3 = .ok (main, bs4) ∧
      NearSpecV3.pVec "source_receipt_proofs" NearSpecV3.pEntry bs4 = .ok (entries, bs5) ∧
      NearSpecV3.pHash "applied_receipts_hash" bs5 = .ok (arh, bs6) ∧
      NearSpecV3.pU32 "transactions" bs6 = .ok (0, bs7) ∧
      NearSpecV3.pVec "implicit_transitions" NearSpecV3.pTransition bs7 = .ok (impl, bs8) ∧
      NearSpecV3.pU32 "new_transactions" bs8 = .ok (0, []) ∧
      w0 = ⟨eid, ib, ci, main, entries, arh, 0, impl, 0⟩ := by
  unfold NearSpecV3.decodeStateWitness at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i hsz
    cases hp1 : NearSpecV3.pU8 "ChunkStateWitness tag" bs with
    | error e => rw [hp1] at h; dsimp only at h; simp at h
    | ok v =>
      obtain ⟨t, bs1⟩ := v
      rw [hp1] at h; dsimp only at h
      split at h
      · simp at h
      · rename_i ht'
        cases hp2 : NearSpecV3.pHash "epoch_id" bs1 with
        | error e => rw [hp2] at h; dsimp only at h; simp at h
        | ok v =>
          obtain ⟨eid, bs2⟩ := v
          rw [hp2] at h; dsimp only at h
          cases hp3 : NearSpecV3.pChunkHeader bs2 with
          | error e => rw [hp3] at h; dsimp only at h; simp at h
          | ok v =>
            obtain ⟨⟨ib, ci⟩, bs3⟩ := v
            rw [hp3] at h; dsimp only at h
            cases hp4 : NearSpecV3.pTransition bs3 with
            | error e => rw [hp4] at h; dsimp only at h; simp at h
            | ok v =>
              obtain ⟨main, bs4⟩ := v
              rw [hp4] at h; dsimp only at h
              cases hp5 : NearSpecV3.pVec "source_receipt_proofs" NearSpecV3.pEntry bs4 with
              | error e => rw [hp5] at h; dsimp only at h; simp at h
              | ok v =>
                obtain ⟨entries, bs5⟩ := v
                rw [hp5] at h; dsimp only at h
                cases hp6 : NearSpecV3.pHash "applied_receipts_hash" bs5 with
                | error e => rw [hp6] at h; dsimp only at h; simp at h
                | ok v =>
                  obtain ⟨arh, bs6⟩ := v
                  rw [hp6] at h; dsimp only at h
                  cases hp7 : NearSpecV3.pU32 "transactions" bs6 with
                  | error e => rw [hp7] at h; dsimp only at h; simp at h
                  | ok v =>
                    obtain ⟨ntx, bs7⟩ := v
                    rw [hp7] at h; dsimp only at h
                    split at h
                    · simp at h
                    · rename_i hn1b
                      cases hp8 : NearSpecV3.pVec "implicit_transitions" NearSpecV3.pTransition bs7 with
                      | error e => rw [hp8] at h; dsimp only at h; simp at h
                      | ok v =>
                        obtain ⟨impl, bs8⟩ := v
                        rw [hp8] at h; dsimp only at h
                        cases hp9 : NearSpecV3.pU32 "new_transactions" bs8 with
                        | error e => rw [hp9] at h; dsimp only at h; simp at h
                        | ok v =>
                          obtain ⟨nnew, bs9⟩ := v
                          rw [hp9] at h; dsimp only at h
                          split at h
                          · simp at h
                          · rename_i hn2b
                            split at h
                            · simp at h
                            · rename_i heb
                              obtain hR := Except.ok.inj h
                              have ht : t = 1 := by simpa using ht'
                              have hn1' : ntx = 0 := by simpa using hn1b
                              have hn2' : nnew = 0 := by simpa using hn2b
                              have he' : bs9 = [] := by simpa using heb
                              subst ht
                              subst hn1'
                              subst hn2'
                              subst he'
                              exact ⟨bs1, eid, bs2, ib, ci, bs3, main, bs4, entries, bs5, arh, bs6,
                                bs7, impl, bs8, hsz, rfl, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9,
                                hR.symm⟩

/-- A D0-accepted witness has no transactions (`nTransactions = 0`). -/
theorem nTransactions_eq_zero (bs : Bytes) (w0 : NearSpecV3.StateWitness)
    (h : NearSpecV3.decodeStateWitness bs = .ok w0) : w0.nTransactions = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ :=
    decodeStateWitness_shape bs w0 h
  rw [hR]

/-- A D0-accepted witness has no new transactions (`nNewTransactions = 0`). -/
theorem nNewTransactions_eq_zero (bs : Bytes) (w0 : NearSpecV3.StateWitness)
    (h : NearSpecV3.decodeStateWitness bs = .ok w0) : w0.nNewTransactions = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ :=
    decodeStateWitness_shape bs w0 h
  rw [hR]

end Work.Decode.Agree

namespace Work.Decode

open NearSpec
open Work.Decode.Agree (decodeStateWitness_shape pVec_of_zero)

/-- **D0 and D1 witness decoders agree.**  Every `(bytes, witness)` pair accepted by the
D0 witness decoder is accepted by the D1 witness decoder, with the same witness: both
decode the very same byte stream, and only the two transaction fields (necessarily
empty in D0) are `[]` in the D1 record. -/
theorem Agree (bs : NearSpec.Bytes) (w0 : NearSpecV3.StateWitness)
    (h : NearSpecV3.decodeStateWitness bs = .ok w0) :
    ∃ w1 : NearSpecV3.StateWitnessD1, NearSpecV3.decodeStateWitnessD1 bs = .ok w1 ∧
      w1.epochId = w0.epochId ∧ w1.innerBytes = w0.innerBytes ∧ w1.inner = w0.inner ∧
      w1.main = w0.main ∧ w1.entries = w0.entries ∧
      w1.appliedReceiptsHash = w0.appliedReceiptsHash ∧ w1.implicit = w0.implicit ∧
      w1.txs = [] ∧ w1.newTxs = [] := by
  obtain ⟨bs1, eid, bs2, ib, ci, bs3, main, bs4, entries, bs5, arh, bs6, bs7, impl, bs8,
    hsz, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hR⟩ := decodeStateWitness_shape bs w0 h
  refine ⟨⟨eid, ib, ci, main, entries, arh, [], impl, []⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the D1 decoder, replayed on the same stream
    unfold NearSpecV3.decodeStateWitnessD1
    rw [ite_eq_right hsz]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [hp1]
    dsimp only
    rw [ite_eq_right (by simp)]
    rw [hp2]
    dsimp only
    rw [hp3]
    dsimp only
    rw [hp4]
    dsimp only
    rw [hp5]
    dsimp only
    rw [hp6]
    dsimp only
    rw [pVec_of_zero "transactions" "transactions" NearSpecV3.pTxD1 bs6 bs7 hp7]
    dsimp only
    rw [hp8]
    dsimp only
    rw [pVec_of_zero "new_transactions" "new_transactions" NearSpecV3.pTxD1 bs8 [] hp9]
    dsimp only
    rw [ite_eq_right (by simp)]
  all_goals (first | rw [hR] | simp)

end Work.Decode
