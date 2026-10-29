import NearSpecV3.ChunkValidationD1
import NearSpecV3.D0SubD1.Work.Root.Basic
import NearSpecV3.D0SubD1.Work.Root.Rel
import NearSpecV3.D0SubD1.Work.Root.Phases
import NearSpecV3.D0SubD1.Work.Decode.Agree

/-! Proof notes (the statement and route this lemma was proved against):

Phase B of the D0 ⊆ D1 lockstep. `Work.Root.d0PB c swBytes k` and `d1PB c swBytes k2` (`NearSpecV3.D0SubD1.Work.Root.Phases`) are the SECOND SLICE of the two checkers, verbatim: witness decode, the two witness/claim header checks, chunk-inner decode, layout decode, the trust-domain checks. **This slice contains the witness decoder, so it is where the two runs diverge in the data, not only in the answer type.**

WHAT DIFFERS (exhaustive; verified by diffing the slices):
1. D0's first statement is `decodeStateWitness swBytes`, D1's is `decodeStateWitnessD1 swBytes`.
2. D0 has an extra `check (c.txValid.isEmpty) "out of domain (c.no_tx_flags)"` (nothing on the D1 side).
3. D1 has an extra `check (w.newTxs.all Tx.sizeOk) "invalid: new transaction exceeds max_transaction_size"`.
Everything else is byte-identical.

ROUTE (this is why this statement has the shape it has):
* Step 1 establishes `WRel w wD`, i.e. `wD.epochId = w.epochId ∧ wD.innerBytes = w.innerBytes ∧ wD.inner = w.inner ∧ wD.main = w.main ∧ wD.entries = w.entries ∧ wD.appliedReceiptsHash = w.appliedReceiptsHash ∧ wD.implicit = w.implicit ∧ wD.txs = [] ∧ wD.newTxs = []`. Use the GREEN child `Work.Decode.Agree` (`NearSpecV3.D0SubD1.Work.Decode.Agree`): `(bs) (w0) (h : decodeStateWitness bs = .ok w0) : ∃ w1, decodeStateWitnessD1 bs = .ok w1 ∧ w1.epochId = w0.epochId ∧ … ∧ w1.txs = [] ∧ w1.newTxs = []`. Peel the D0 bind `w ← decodeStateWitness swBytes` with `sim_bind` (`NearSpecV3.D0SubD1.Work.Root.Rel`) at `hx := sim_of_eq rfl`? No: the two scrutinees are the two different decoders, so peel the D0 side with `sim_bind_same`'s sibling `bind_ok_exists`, or better: `apply sim_bind` with the D1 scrutinee `decodeStateWitnessD1 swBytes` and `hx` proved from `Agree`. THEN you get `wD` with `WRel w wD` for free and the remaining statements line up 1:1.
* Step 2: the statements after that are *identical terms* once `WRel w wD` is used to rewrite `wD`'s fields — note `wD.txs = []` and `wD.newTxs = []` make D1's extra `check (w.newTxs.all Tx.sizeOk)` hold: use `NearSpecV3.D0SubD1.Work.Root.sim_extra` (or `sim_bind_check2`) with `rfl` for `([] : List Tx).all Tx.sizeOk = true` (`Rel.all_sizeOk_nil`).
* Step 3: D0's extra `check (c.txValid.isEmpty)` is peeled with `NearSpecV3.D0SubD1.Work.Root.sim_bind_skip'`: it gives its bool, and `NearSpecV3.D0SubD1.Work.Root.Basic.eq_nil_of_isEmpty` turns it into `c.txValid = []`, which **must be handed to `hk`** (that is the third argument of `hk`). This is essential: D1 later checks `c.txValid.length == w.txs.length`, which is unprovable without it.
* Step 4 (`hk` call): `customs` — the answer values of the two slices flow into `hk`, so give it `WRel w wD` (step 1) and `c.txValid = []` (step 3).

USEFUL: `NearSpecV3.D0SubD1.Work.Root.Rel` has `sim_bind_same`, `sim_bind`, `sim_congr`, `sim_check`, `sim_check_both`, `sim_bind_check2`, `sim_bind_skip'`, `sim_extra`, `sim_of_eq`, `sim_sim`-free kit, `WRel` and its projections; `NearSpecV3.D0SubD1.Work.Root.Basic` has `bind_ok_exists`, `check_ok_iff`, `check_eq_true`, `check_of_true`, `eq_nil_of_isEmpty`. `split`/`trace_state` are available; never `dsimp` after `unfold`.

PROOF (done, no children needed).  `unfold` both slices; the two do-blocks are chains of
`Except.bind`s with the same scrutinee term at every step except at the four places the guidance
lists.
1. The first `bind` is the *different* one (`decodeStateWitness` vs `decodeStateWitnessD1`): peeled
   with `sim_bind`, whose `hx` is `Work.Decode.Agree` (D0 success ⟹ D1 success on the same
   stream).  Success of `decodeStateWitnessD1 swBytes` pins its value (`Except.ok.inj`), so the
   witnesses `Work.Decode.Agree` speaks about are exactly the continuation's `w0`/`wD`, and
   `WRel w0 wD` is immediate.
2. `rw` the three shared fields that occur in the remaining statements
   (`wD.epochId`, `wD.innerBytes`, `wD.newTxs`) into the D0 ones; `wD.newTxs = []` turns the
   D1-only `check` into `check (([].all Tx.sizeOk)) …`, which is `true` by `rfl`.
3. Every other statement has the same scrutinee on both sides (the cuts are at statement
   boundaries), so each is peeled with `sim_bind_same` — including the `check`s, whose value is
   discarded.
4. The D0-only `check (c.txValid.isEmpty) …` is peeled with `sim_bind_skip'`, which hands its
   truth to the continuation: `eq_nil_of_isEmpty` turns it into `c.txValid = []`, the second
   hypothesis of `hk` (nothing on the D1 side consumes it — the D1-only `check` is the
   `all_sizeOk_nil` step).
5. The remainder is `k c w0 H L` vs `check (([].all Tx.sizeOk)) … >>= k2 c wD H L`: the extra D1
   `check` is substituted away with `all_sizeOk_nil`, and `hk w0 wD H L hWR htx` closes it.
-/

namespace Work.Phases

theorem PhaseB (c : NearSpecV3.Claim) (swBytes : NearSpec.Bytes)
    (k : NearSpecV3.Claim → NearSpecV3.StateWitness → NearSpecV3.ChunkInner → NearSpecV3.Layout → Except String Unit)
    (k2 : NearSpecV3.Claim → NearSpecV3.StateWitnessD1 → NearSpecV3.ChunkInner → NearSpecV3.Layout → Except String NearSpecV3.Observable)
    (hk : ∀ (w : NearSpecV3.StateWitness) (wD : NearSpecV3.StateWitnessD1) (H : NearSpecV3.ChunkInner) (L : NearSpecV3.Layout),
      NearSpecV3.D0SubD1.Work.Root.WRel w wD → c.txValid = [] → NearSpecV3.D0SubD1.Work.Root.SIM (k c w H L) (k2 c wD H L)) :
    NearSpecV3.D0SubD1.Work.Root.SIM
      (NearSpecV3.D0SubD1.Work.Root.d0PB c swBytes k)
      (NearSpecV3.D0SubD1.Work.Root.d1PB c swBytes k2) := by
  unfold NearSpecV3.D0SubD1.Work.Root.d0PB NearSpecV3.D0SubD1.Work.Root.d1PB
  -- the first statement is the D0 witness decoder vs the D1 witness decoder
  apply NearSpecV3.D0SubD1.Work.Root.sim_bind
  · intro w0 h0
    obtain ⟨w1, h1, -⟩ := Work.Decode.Agree swBytes w0 h0
    exact ⟨w1, h1⟩
  · intro w0 wD h0 hD
    -- `Work.Decode.Agree` identifies `wD` with the witness it produces on this very stream
    obtain ⟨w1, h1, hrel⟩ := Work.Decode.Agree swBytes w0 h0
    have hok : (Except.ok w1 : Except String NearSpecV3.StateWitnessD1) = Except.ok wD := by
      rw [← h1]; exact hD
    have hw : wD = w1 := (Except.ok.inj hok).symm
    subst hw
    have hW : NearSpecV3.D0SubD1.Work.Root.WRel w0 wD := hrel
    -- the fields of `wD` that the remaining statements mention are the D0 witness's fields,
    -- and `wD.newTxs = []` makes the D1-only `all Tx.sizeOk` gate trivial
    have hE : wD.epochId = w0.epochId := hW.1
    have hI : wD.innerBytes = w0.innerBytes := hW.2.1
    have hN : wD.newTxs = [] := hW.2.2.2.2.2.2.2.2
    rw [hE, hI, hN]
    -- the statements shared verbatim (same scrutinee term on both sides)
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro H hH
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro L hL
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    -- the D0-only statement `check (c.txValid.isEmpty) …`: hand its truth to `hk`
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_skip'
    intro htx
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
    intro u hu
    -- the D1-only statement `check (w.newTxs.all Tx.sizeOk) …`, already `[]`
    intro hu'
    have hk' := hk w0 wD H L hW (NearSpecV3.D0SubD1.Work.Root.eq_nil_of_isEmpty htx)
    obtain ⟨b, hb⟩ := hk' hu hu'
    exact ⟨b, by
      rw [NearSpecV3.D0SubD1.Work.Root.check_of_true _ NearSpecV3.D0SubD1.Work.Root.all_sizeOk_nil]
      exact hb⟩

end Work.Phases
