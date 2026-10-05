import ZkFormal.Bcs.StarkMain
import ZkFormal.Bcs.Compose
import ZkFormal.Bcs.Game2
import ZkFormal.Bcs.Budget
import ZkFormal.Bcs.Mmcs

/-!
# ZkFormal.Bcs.Final — ROM soundness of lane L4's deployed STARK verifier

`stark_romSound`: the judge's `RomSound` for `Stark.Bcs.compile V` (as a
`TreeVerifier`), from
* lane L3's round-by-round facts in byte-transcript form (`hinit`, `hmsg`,
  `hround`, `hquery`, over `Bcs.PT mmcs`),
* the shape conditions `SchedOk V`,
* query budgets of the honest prover and the verifier,
* and `InvPotStmt` (the inversion potential, still being proved).

Every other L2 sublemma is discharged: `game2`, `qbAdd`, `stepMix`,
`mmcs_binding_rooted`, `compile_accepts`.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

/-- L4's compiled verifier as a tree verifier. -/
def starkTree {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (V : Stark.IopSpec F K) : TreeVerifier :=
  ⟨fun pub cb pb => Stark.Bcs.compile (F := F) V pub cb pb⟩

theorem stark_romSound (hInv : InvPotStmt)
    {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (V : Stark.IopSpec F K) (hV : Adapter.SchedOk V)
    (hK : 2 ≤ V.numChunks) (hK' : V.numChunks ≤ 2 ^ 32)
    (Doomed : PT mmcs → Prop)
    {S : ChallengeSpec} (L : Bytes → Prop) (P : TreeProver S) (pub : Bytes)
    (hinit : ∀ cb, ¬ L cb → Doomed ⟨cb, []⟩)
    (hmsg : ∀ τ roots raw os, Doomed τ → Doomed (τ.push (.msg roots raw os)))
    (B : Nat) (hround : ∀ τ : PT mmcs, Doomed τ →
      count (List.range roRange) (fun v => ¬ Doomed (τ.push (.chal (LazyRO.answer v)))) ≤ B)
    (g : Nat → Nat) (hquery : ∀ (τ : PT mmcs) (j : Nat), Doomed τ →
      count (List.range roRange) (fun v =>
        ∀ pt ∈ (Adapter.adapt (F := F) V).points τ.view j (LazyRO.answer v),
          Pass (Adapter.adapt (F := F) V) τ pt) ≤ g j)
    (qH qP NPu NVu NPq NVq : Nat) (hN : qH + qP * NPu + NVu ≤ 2 ^ 100)
    (hPu : ∀ c wit, OracleComp.QueryBound unitWeight (P.tree pub c wit) NPu)
    (hVu : ∀ cb pb, OracleComp.QueryBound unitWeight ((starkTree (F := F) V).tree pub cb pb) NVu)
    (hPq : ∀ c wit, OracleComp.QueryBound (qWeight chunkDec) (P.tree pub c wit) NPq)
    (hVq : ∀ cb pb, OracleComp.QueryBound (qWeight chunkDec) ((starkTree (F := F) V).tree pub cb pb) NVq) :
    RomSound S L (starkTree (F := F) V).toVerifier P.toProver pub qH qP (qH + qP * NPu + NVu)
      (bcsNum V.numChunks B ((List.range V.numChunks).map g).prod qH qP NPu NVu NPq NVq)
      (roRange ^ V.numChunks) :=
  bcs_romSound game2 qbAdd stepMix hInv mmcs_binding_rooted.1 mmcs_binding_rooted.2
    (Adapter.adapt (F := F) V) hK hK' Doomed (Adapter.ctxOf pub) L P (starkTree (F := F) V) pub
    (fun tbl cb pb wf hev => Adapter.compile_accepts F K V hV tbl pub cb pb wf hev)
    hinit hmsg B hround g hquery qH qP NPu NVu NPq NVq hN hPu hVu hPq hVq

end ZkFormal.Bcs
