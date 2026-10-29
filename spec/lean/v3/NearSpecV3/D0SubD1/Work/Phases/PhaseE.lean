import NearSpecV3.D0SubD1.Work.Root.Rel
import NearSpecV3.D0SubD1.Work.Root.Phases
import NearSpecV3.D0SubD1.Work.Root.Outcome

/-! Proof notes (the statement and route this lemma was proved against):

Phase E of the D0 ⊆ D1 lockstep: the tail. `Work.Root.d0PE c w H L idx B2 slotB2 implicitBlks receipts out own` / `d1PE c wD H L idx B2 slotB2 implicitBlks receipts outD own` (`NearSpecV3.D0SubD1.Work.Root.Phases`) are the FIFTH SLICE — implicit transitions, the final header comparison, and (D1 only) the `d1Outputs` the observable checker computes.

WHAT DIFFERS (exhaustive; verified by diffing the slices):
1. D1 has a FIRST statement D0 does not: `check (decide (out.localIds ++ receipts.map Receipt.receiptId).Nodup) "out of domain (e.distinct_ids)"`. This is D1's *moved* copy of D0's `e.distinct_ids` check, which D0 performed in phase D (where its continuation received it). It holds because `ho : ORel out outD` gives `outD.localIds = []` and `hN : decide (receipts.map receiptId).Nodup = true` is a hypothesis; `([] ++ l).Nodup ↔ l.Nodup` is `simpa`.
2. `check (H.prevOutcomeRoot == outcomeRoot out.outcomes)` vs `check (H.prevOutcomeRoot == outcomeRootD1 outD.outcomes)`.
3. `check (H.txRoot == zeroHash32)` + `let body := u32 0 ++ encodeReceipts out.outgoing` vs `check (H.txRoot == merklizeBorsh (w.newTxs.map Tx.raw))` + `let body := u32 w.newTxs.length ++ concatAll (w.newTxs.map Tx.raw) ++ encodeReceipts out.outgoing`.
4. D1's `some (emr, len)` arm ends with `return d1Outputs root out.outcomes out.gasUsed out.tokensBurnt L out.outgoing (merklizeBorsh (w.newTxs.map Tx.raw)) emr len ownCongestion`; D0's arm has nothing (`check`s only). The D1 side returns a VALUE (`Observable`) but `SIM` only asks the D1 run to *succeed*, so this arm is closed by `sim_of_eq rfl`/`sim_pure_right` after the two `check`s.
Everything else (`root`, the implicit-transition `for` loop, `allowed`, `ownCongestion`, and the checks in 2/3 and the RS block) is identical or handled below.

KEY: `hw : WRel w wD` gives `wD.newTxs = []` (`.2.2.2.2.2.2.2.2`) and `wD.main = w.main`; `ho : ORel out outD` gives `outD.localIds = []`, `outD.outcomes = out.outcomes.map (fun o => {o := o, status := OStatus.value})`, `outD.gasUsed = out.gasUsed`, `outD.tokensBurnt = out.tokensBurnt`, `outD.trie = out.trie`, `outD.outgoing = out.outgoing`.

ROUTE:
* Statement 1 (D1-only): `sim_extra` with the truth `([] ++ receipts.map Receipt.receiptId).Nodup` derived from `hN` by `simpa [ho.2.2.2.2.2]`. Concretely: `refine NearSpecV3.D0SubD1.Work.Root.sim_extra _ _ _ ?_ ?_` — but since the D1 statement is `check … >>= fun _ => <rest>` and the D0 side has no statement, use `sim_extra` with the boolean `decide (… .Nodup)`; you must prove that boolean is `true` (`decide_eq_true_eq`/`simpa` from `hN` and `ho`).
* Statement 2: the two outcome roots coincide because `outD.outcomes = out.outcomes.map ⟨·, .value⟩` (`ho`), so `outcomeRootD1 outD.outcomes = outcomeRoot D0` by the child `Work.Root.Outcome` (statement: `Outcome (os : List NearSpec.Outcome) : NearSpecV3.outcomeRootD1 (os.map (fun o => { o := o, status := NearSpecV3.OStatus.value })) = NearSpec.outcomeRoot os`). Rewrite and the two `check`s are `sim_check`/`sim_of_eq rfl`.
* Statement 3: D0's `check (H.txRoot == zeroHash32)` gives `H.txRoot = zeroHash32`; D1's is `check (H.txRoot == merklizeBorsh (wD.newTxs.map Tx.raw))` with `merklizeBorsh ([] : List Tx).map Tx.raw = zeroHash32` (`Rel.merklizeBorsh_nil_tx`), so by `beq_bytes`/`beq_bytes_symm` this is `rfl`-true — use `sim_bind_check2`. For the `body`s: `u32 wD.newTxs.length ++ concatAll (wD.newTxs.map Tx.raw) = u32 0` after `wD.newTxs = []` (`Rel.u32_nil_length`, `Rel.concatAll_nil`, `Rel.method`; `rfl` after rewriting), so the following `match encodedMerkleRoot …` is the SAME term on both sides (`sim_match_pure_throw` / `sim_of_eq rfl`, then `sim_bind_same`), and D0's two `check`s pair with D1's two `check`s.
* Statement 4: label the `some` arm: D0 `check (H.encodedMerkleRoot == emr) m >>= fun _ => check (H.encodedLength == len) m'` and D1 the same followed by `return d1Outputs …`. After the two `check`s are peeled with `sim_bind_same`, the D0 remainder is `pure ()` and the D1 remainder is `pure (d1Outputs …)` — close with `NearSpecV3.D0SubD1.Work.Root.sim_pure_right` (it says `SIM x (pure v)` for any `v`) or `sim_of_eq rfl`.

Also note D0's `root`/`for` loop over `implicitBlks.zip w.implicit` uses `w.implicit`, and `hw` gives `wD.implicit = w.implicit`, so that loop is the same term on both sides (the same `forIn` treatment as in `Phases/PhaseC`).

USEFUL: `NearSpecV3.D0SubD1.Work.Root.Rel`: `sim_bind_same`, `sim_bind`, `sim_congr`, `sim_check`, `sim_check_both`, `sim_bind_check2`, `sim_extra`, `sim_bind_skip'`, `sim_match_pure_throw`, `sim_pure_right`, `sim_of_eq`, `ORel`, `WRel`, `merklizeBorsh_nil_tx`, `concatAll_nil`, `u32_nil_length`, `beq_bytes`, `beq_bytes_symm`, `eq_of_beq_bytes`. `NearSpecV3.D0SubD1.Work.Root.Basic`: `bind_ok_exists`, `check_eq_true`, `check_of_true`. `split`/`trace_state` are available; never `dsimp` after `unfold`.
-/

namespace Work.Phases.PhaseE

open NearSpec NearSpecV3

/-- **The tail of a D1 `check` chain that returns a value.**  A statement `check b m >>= f` whose
D0 counterpart is the bare `check b m` (no value) is simulated by the D1 side only *succeeding*
whatever it returns; here the D1 continuation `f` is `fun _ => pure v`. -/
theorem sim_check_pure_right {α ρ : Type} (x : Except String α) (v : ρ) :
    NearSpecV3.D0SubD1.Work.Root.SIM x (x >>= fun _ => pure v) := by
  intro a ha
  exact ⟨v, by rw [ha]; rfl⟩

end Work.Phases.PhaseE

namespace Work.Phases

open NearSpec NearSpecV3
open NearSpecV3.D0SubD1.Work.Root

/-- **Phase E of the D0 ⊆ D1 lockstep — the tail.**

`d0PE`/`d1PE` (`NearSpecV3.D0SubD1.Work.Root.Phases`) are the fifth slice of the two checkers: the
implicit-transition loop, the final header comparison, and (D1 only) the observable the D1 checker
returns.  The two slices differ in exactly four places, all listed in the guidance above; the proof
is the verbatim-slice argument of the other phases:

* the D1-only leading `check (decide (outD.localIds ++ …).Nodup)` holds because `ORel` gives
  `outD.localIds = []` and `hN` says `(receipts.map receiptId).Nodup = true` — `sim_extra`;
* the remaining shared statements (`root`, the `for` loop over `implicitBlks.zip w.implicit`,
  `allowed`/`ownCongestion`, the header checks) are the *same term* on both sides after rewriting
  `wD.implicit → w.implicit`, `wD.main → w.main` and `outD.trie → out.trie`, so they are peeled by
  `sim_bind_same` (this covers the `for` loop directly: both sides have the same loop term and the
  same answer type for the loop's state, so no induction is needed — only the D0 side's `check`s
  inside the loop are ever entered at the two runs' common success);
* the outcome-root comparison uses the child `Work.Root.Outcome` to turn the `OStatus.value`
  decoration of the outcomes (`ORel`) into `outcomeRootD1 outD.outcomes = outcomeRoot out.outcomes`;
* the transaction roots and the RS body coincide because `wD.newTxs = []` (`WRel`), so the D0
  `check (H.txRoot == zeroHash32)`/`body := u32 0 ++ encodeReceipts …` and the D1
  `check (H.txRoot == merklizeBorsh [])`/`body := u32 0 ++ [] ++ encodeReceipts …` are the same
  test, and the D1 `some (emr, len)` arm ends with `pure (d1Outputs …)`, closed by
  `PhaseE.sim_check_pure_right`. -/
theorem PhaseE (c : NearSpecV3.Claim) (w : NearSpecV3.StateWitness) (wD : NearSpecV3.StateWitnessD1) (H : NearSpecV3.ChunkInner) (L : NearSpecV3.Layout)
    (idx : Nat) (B2 : NearSpecV3.Blk) (slotB2 : NearSpecV3.ChunkInner) (implicitBlks : List NearSpecV3.Blk)
    (receipts : List NearSpec.Receipt) (out : NearSpecV3.MainOut) (outD : NearSpecV3.MainOutD1) (own : NearSpecV3.Congestion)
    (hw : NearSpecV3.D0SubD1.Work.Root.WRel w wD) (ho : NearSpecV3.D0SubD1.Work.Root.ORel out outD)
    (hN : decide (receipts.map NearSpec.Receipt.receiptId).Nodup = true) :
    NearSpecV3.D0SubD1.Work.Root.SIM
      (NearSpecV3.D0SubD1.Work.Root.d0PE c w H L idx B2 slotB2 implicitBlks receipts out own)
      (NearSpecV3.D0SubD1.Work.Root.d1PE c wD H L idx B2 slotB2 implicitBlks receipts outD own) := by
  -- the two relations, unpacked
  obtain ⟨hE, hIB, hIn, hMain, hEnt, hARH, hImpl, hTxs, hNew⟩ := hw
  obtain ⟨hTrie, hOut, hOutgoing, hGas, hTok, hLoc⟩ := ho
  -- make the two slices syntactically the same term, statement by statement
  unfold NearSpecV3.D0SubD1.Work.Root.d0PE NearSpecV3.D0SubD1.Work.Root.d1PE
  simp only [hImpl, hMain, hTrie]
  rw [hOut, hGas, hTok, hOutgoing, hNew]
  simp only [NearSpecV3.D0SubD1.Work.Root.concatAll_nil, List.map_nil, List.length_nil]
  rw [Work.Root.Outcome out.outcomes, NearSpecV3.D0SubD1.Work.Root.merklizeBorsh_nil]
  rw [List.append_nil, hLoc, List.nil_append]
  -- statement 1: the D1-only `e.distinct_ids` check holds
  refine sim_extra _ _ _ hN ?_
  -- the shared statements: the first `check`, the implicit-transition `for` loop, then the
  -- remaining header comparison (`check`s all the way to the RS body)
  apply sim_bind_same; intro u
  apply sim_bind_same; intro s
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  apply sim_bind_same; intro u
  -- the RS block: `match encodedMerkleRoot … with none => throw … | some (emr, len) => …`,
  -- the same scrutinee on both sides
  generalize hX : encodedMerkleRoot c.rsDataParts c.rsTotalParts
    (u32 0 ++ encodeReceipts out.outgoing) = X
  cases X with
  | none => exact sim_throw _ _
  | some p =>
    obtain ⟨emr, len⟩ := p
    apply sim_bind_same; intro u
    exact Work.Phases.PhaseE.sim_check_pure_right _ _

end Work.Phases
