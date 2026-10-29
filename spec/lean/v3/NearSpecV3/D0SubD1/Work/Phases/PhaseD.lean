import NearSpecV3.ChunkValidationD1
import NearSpecV3.D0SubD1.Work.Root.Basic
import NearSpecV3.D0SubD1.Work.Root.Rel
import NearSpecV3.D0SubD1.Work.Root.Phases
import NearSpecV3.D0SubD1.Work.Runtime.EmptyTxs

/-! Proof notes (the statement and route this lemma was proved against):

Phase D of the D0 ⊆ D1 lockstep: the main transition. `Work.Root.d0PD c w H L idx B2 prevB2 slotB2 implicitBlks receipts k` / `d1PD c wD H L idx B2 prevB2 slotB2 implicitBlks receipts k2` (`NearSpecV3.D0SubD1.Work.Root.Phases`) are the FOURTH SLICE. `hT : c.txValid = []` is a hypothesis **on purpose**: D0 establishes it in phase B (`check (c.txValid.isEmpty) "out of domain (c.no_tx_flags)"`) and D1 needs it HERE (`check (c.txValid.length == w.txs.length) "invalid: tx_valid length"`), so the assembly passes it down through the continuation. `hw : WRel w wD` gives `wD.txs = []` (`.2.2.2.2.2.2.2.1`) and `wD.main = w.main` (`.2.2.2.1`).

WHAT DIFFERS (exhaustive; verified by diffing the slices):
1. D0: `check (slotB2.txRoot == zeroHash32) "invalid: transaction root of the last chunk"`, then D0's `check (decide (receipts.map Receipt.receiptId).Nodup) "out of domain (e.distinct_ids)"`.
   D1: `check (merklizeBorsh (w.txs.map Tx.raw) == slotB2.txRoot) "invalid: transaction root of the last chunk"`, then `check (c.txValid.length == w.txs.length) "invalid: tx_valid length"`.
   (D1's `Nodup` check on `out.localIds ++ receipts.map receiptId` lives in phase E instead.)
2. `tMain`: D0 `partialTrie w.main.values slotB2.prevStateRoot (mainKeys receipts bshards)`; D1 `… (mainKeys receipts bshards ++ txKeys w.txs)`.
3. `let out ← applyNewChunk prims ctxB2 tMain receipts` vs `let out ← applyNewChunkD1 prims ctxB2 tMain receipts (w.txs.zip (c.txValid.map (· != 0)))`.
Everything else is identical.

ROUTE:
* Statement 1: `check (slotB2.txRoot == zeroHash32)` vs `check (merklizeBorsh (wD.txs.map Tx.raw) == slotB2.txRoot)`: the D1 boolean is implied by the D0 one — the D0 boolean gives `slotB2.txRoot = zeroHash32` (`eq_of_beq_bytes`), and `merklizeBorsh (([] : List Tx).map Tx.raw) = zeroHash32` is `rfl` after `hw`'s `wD.txs = []` (`Rel.merklizeBorsh_nil_tx`). Use `NearSpecV3.D0SubD1.Work.Root.sim_bind_check2` (`hb : b1 = true → b2 = true`, `hk : b1 = true → SIM (f ()) (g ())`).
* Statement 2: `check (decide (receipts.map Receipt.receiptId).Nodup)` (D0-only) paired with `check (c.txValid.length == wD.txs.length)` (D1-only): the D0 boolean gives `decide … = true`, which must be handed to `hk`'s second argument; the D1 boolean is `rfl`-true after `hT` and `hw`'s `wD.txs = []` (both sides `[].length`). Again `sim_bind_check2` (or `sim_bind_skip'` + `sim_extra`).
* Statements 3–5 (`baseBytes`, `own`, `ctxB2`) are identical terms.
* Statement 6 (`t0`, `bshards`): identical; rewrite `wD.main = w.main`.
* Statement 7 (`tMain`): the D1 key list is `mainKeys receipts bshards ++ txKeys wD.txs = mainKeys receipts bshards ++ [] = mainKeys receipts bshards` by `Rel.txKeys_nil` and `Rel.mainKeys_append_nil` (both published). So the two `tMain`s are the *same term*, and the `check (tMain.hashOf == slotB2.prevStateRoot)` after it is `sim_of_eq rfl`/`sim_check`.
* Statement 8 (`out`): the scrutinees are `applyNewChunk …` and `applyNewChunkD1 prims ctxB2 tMain receipts []` (after `wD.txs = []`, `c.txValid = []` and `Rel.txValid_map_nil`). Peel with `NearSpecV3.D0SubD1.Work.Root.sim_bind`, taking `hx` from the GREEN child `Work.Runtime.EmptyTxs` (`NearSpecV3.D0SubD1.Work.Runtime.EmptyTxs`): `(prims ctx t receipts out) (h : applyNewChunk prims ctx t receipts = .ok out) : ∃ out', applyNewChunkD1 prims ctx t receipts [] = .ok out' ∧ out'.trie = out.trie ∧ out'.outcomes = out.outcomes.map (fun o => { o := o, status := OStatus.value }) ∧ out'.outgoing = out.outgoing ∧ out'.gasUsed = out.gasUsed ∧ out'.tokensBurnt = out.tokensBurnt ∧ out'.localIds = []` — exactly `ORel out out'`. Then call `hk out out' own (that conjunction) (hN)`.

USEFUL: `NearSpecV3.D0SubD1.Work.Root.Rel`: `sim_bind`, `sim_bind_same`, `sim_bind_check2`, `sim_bind_skip'`, `sim_extra`, `sim_check_both`, `sim_check`, `sim_of_eq`, `sim_congr`, `ORel`, `WRel` (projections are nested `.2`), `merklizeBorsh_nil_tx`, `txKeys_nil`, `mainKeys_append_nil`, `txValid_map_nil`, `zip_nil_tx`, `beq_bytes`, `eq_of_beq_bytes`, `beq_nat`, `eq_of_beq_nat`, `sim_pure_right`. `NearSpecV3.D0SubD1.Work.Root.Basic`: `bind_ok_exists`, `check_eq_true`, `check_of_true`. This is where the *runtime* layers meet, so it is the second-most expensive after C. Keep the statement exactly as pinned.

## How this was proved (notes for the next reader)

`d0PD`/`d1PD` unfold to *eight* `bind`s, and the two sides differ in exactly three of them
(transactions root, the `distinct_ids`/`tx_valid length` pair, the runtime call); every other
statement is literally the same term, so it is peeled with `NearSpecV3.D0SubD1.Work.Root.sim_bind_same`.
Two further wrinkles:

* `d1PD`'s `let bshards ← match t0.find keyBufferedIdx with …` is desugared by Lean into an
  `Option`-`match` whose arms feed a shared jump function applied to `bshards` — so the peel is
  `cases hb : t0.find keyBufferedIdx` (the variable of the `cases` is `hb`, the arms introduce
  `bshards` and the fallback is definitionally the same term as the `some` arm).  This needs the
  two `if`s of the D1 fallback to be *definitionally* transparent, which they are (`if_false`
  in the `match` desugaring).
* Statement 8 is peeled with `Work.Phases.PhaseD.sim_bind_exists` (a `bind` whose two scrutinees
  are different terms), the D1 value coming from the GREEN `Work.Runtime.EmptyTxs`.
-/

namespace Work.Phases.PhaseD

open NearSpec NearSpecV3 NearSpecV3.D0SubD1.Work.Root

/-- Peel a `bind` whose two scrutinees are *different* terms: the matching value of the D1 side is
produced together with the continuation hypothesis (here it is the `Work.Runtime.EmptyTxs`
output).  This is the sibling of `NearSpecV3.D0SubD1.Work.Root.sim_bind` made for the D0-runtime
vs D1-runtime step. -/
theorem sim_bind_exists {α β γ δ : Type} {x : Except String α} {y : Except String β}
    {f : α → Except String γ} {g : β → Except String δ}
    (h : ∀ a, x = .ok a → ∃ b, y = .ok b ∧ SIM (f a) (g b)) : SIM (x >>= f) (y >>= g) := by
  intro c hc
  obtain ⟨a, ha, hc'⟩ := bind_ok_exists hc
  obtain ⟨b, hb, hf⟩ := h a ha
  obtain ⟨d, hd⟩ := hf c hc'
  exact ⟨d, by rw [hb]; exact hd⟩

end Work.Phases.PhaseD

namespace Work.Phases

open NearSpec NearSpecV3 NearSpecV3.D0SubD1.Work.Root

set_option maxHeartbeats 0

theorem PhaseD (c : NearSpecV3.Claim) (hT : c.txValid = []) (w : NearSpecV3.StateWitness) (wD : NearSpecV3.StateWitnessD1)
    (H : NearSpecV3.ChunkInner) (L : NearSpecV3.Layout)
    (idx : Nat) (B2 : NearSpecV3.Blk) (prevB2 : NearSpecV3.Blk) (slotB2 : NearSpecV3.ChunkInner)
    (implicitBlks : List NearSpecV3.Blk) (receipts : List NearSpec.Receipt) (hw : NearSpecV3.D0SubD1.Work.Root.WRel w wD)
    (k : NearSpecV3.Claim → NearSpecV3.StateWitness → NearSpecV3.ChunkInner → NearSpecV3.Layout → Nat → NearSpecV3.Blk → NearSpecV3.ChunkInner → List NearSpecV3.Blk → List NearSpec.Receipt → NearSpecV3.MainOut → NearSpecV3.Congestion → Except String Unit)
    (k2 : NearSpecV3.Claim → NearSpecV3.StateWitnessD1 → NearSpecV3.ChunkInner → NearSpecV3.Layout → Nat → NearSpecV3.Blk → NearSpecV3.ChunkInner → List NearSpecV3.Blk → List NearSpec.Receipt → NearSpecV3.MainOutD1 → NearSpecV3.Congestion → Except String NearSpecV3.Observable)
    (hk : ∀ (out : NearSpecV3.MainOut) (outD : NearSpecV3.MainOutD1) (own : NearSpecV3.Congestion), NearSpecV3.D0SubD1.Work.Root.ORel out outD →
      decide (receipts.map NearSpec.Receipt.receiptId).Nodup = true →
      NearSpecV3.D0SubD1.Work.Root.SIM (k c w H L idx B2 slotB2 implicitBlks receipts out own)
        (k2 c wD H L idx B2 slotB2 implicitBlks receipts outD own)) :
    NearSpecV3.D0SubD1.Work.Root.SIM
      (NearSpecV3.D0SubD1.Work.Root.d0PD c w H L idx B2 prevB2 slotB2 implicitBlks receipts k)
      (NearSpecV3.D0SubD1.Work.Root.d1PD c wD H L idx B2 prevB2 slotB2 implicitBlks receipts k2) := by
  have hwM : wD.main = w.main := hw.2.2.2.1
  have hwT : wD.txs = [] := hw.2.2.2.2.2.2.2.1
  unfold NearSpecV3.D0SubD1.Work.Root.d0PD NearSpecV3.D0SubD1.Work.Root.d1PD
  -- statement 1: D0's `slotB2.txRoot == zeroHash32` implies D1's
  -- `merklizeBorsh (wD.txs.map Tx.raw) == slotB2.txRoot` (`wD.txs = []`)
  apply NearSpecV3.D0SubD1.Work.Root.sim_bind_check2
  · intro h1
    rw [NearSpecV3.D0SubD1.Work.Root.eq_of_beq_bytes h1, hwT]
    exact NearSpecV3.D0SubD1.Work.Root.beq_bytes NearSpecV3.D0SubD1.Work.Root.merklizeBorsh_nil_tx
  · intro hN
    -- statement 2: D0's `distinct_ids` check is kept (it is `PhaseE`'s hypothesis) and paired
    -- with D1's `tx_valid length` check (`c.txValid = []`, `wD.txs = []`)
    apply NearSpecV3.D0SubD1.Work.Root.sim_bind_check2
    · intro h1
      rw [hT, hwT]
      exact NearSpecV3.D0SubD1.Work.Root.beq_nat rfl
    · intro hN'
      -- statements 3–5: `baseBytes`, `own`, `ctxB2` — the same term on both sides
      rw [hwM]
      simp only []
      apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
      intro _
      apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
      intro _
      -- statement 6: `t0.find keyBufferedIdx`, then `bshards` (the same term on both sides)
      cases hb : (partialTrie w.main.values slotB2.prevStateRoot [keyBufferedIdx]).find
          keyBufferedIdx with
      | none =>
        apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
        intro bshards
        -- statement 7: D1's key list `mainKeys receipts bshards ++ txKeys wD.txs` collapses to
        -- D0's `mainKeys receipts bshards`, so `tMain` is the same term on both sides
        simp only [hT, hwT, List.map_nil, List.zip_nil_left, NearSpecV3.D0SubD1.Work.Root.txKeys_nil,
          NearSpecV3.D0SubD1.Work.Root.mainKeys_append_nil]
        apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
        intro _
        -- statement 8: `applyNewChunk prims ctxB2 tMain receipts` vs
        -- `applyNewChunkD1 prims ctxB2 tMain receipts []`
        apply Work.Phases.PhaseD.sim_bind_exists
        intro out hout
        obtain ⟨out', hout', ht, ho, hog, hg, htk, hl⟩ :=
          Work.Runtime.EmptyTxs prims _ _ receipts out hout
        exact ⟨out', hout', hk out out' slotB2.congestion ⟨ht, ho, hog, hg, htk, hl⟩ hN'⟩
      | some v =>
        apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
        intro bshards
        simp only [hT, hwT, List.map_nil, List.zip_nil_left, NearSpecV3.D0SubD1.Work.Root.txKeys_nil,
          NearSpecV3.D0SubD1.Work.Root.mainKeys_append_nil]
        apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
        intro _
        apply Work.Phases.PhaseD.sim_bind_exists
        intro out hout
        obtain ⟨out', hout', ht, ho, hog, hg, htk, hl⟩ :=
          Work.Runtime.EmptyTxs prims _ _ receipts out hout
        exact ⟨out', hout', hk out out' slotB2.congestion ⟨ht, ho, hog, hg, htk, hl⟩ hN'⟩

end Work.Phases
