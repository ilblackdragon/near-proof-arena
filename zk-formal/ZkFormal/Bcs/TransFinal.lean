import ZkFormal.Bcs.TransCompose
import ZkFormal.Bcs.DecPush

/-!
# ZkFormal.Bcs.TransFinal — ROM soundness of L4's verifier from L3's `RbrWith`

`stark_romSound_rbr`: the judge's `RomSound` for `Stark.Bcs.compile V`, with
the bound `bcsNum K (bad·Dm) (G^K) … / 2^(256K)`, from lane L3's round-by-round
facts `Udr.RbrWith V InLang Kall bad agree D` (any doomed predicate `D`), the
challenge-decoder fiber bound `Dm` (lane L1), L4's shape conditions, and
query budgets.
-/

namespace ZkFormal.Bcs.Transport

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

theorem prod_const (K G : Nat) : ((List.range K).map fun _ => G).prod = G ^ K := by
  rw [List.map_const', List.length_range, prod_replicate']

theorem stark_romSound_rbr_of (hQuery : DecQueryStmt) (hPos : PosCountStmt)
    {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (V : Stark.IopSpec F K) (hS : Adapter.SchedOk V)
    (hK : 2 ≤ V.numChunks) (hK' : V.numChunks ≤ 2 ^ 32)
    (InLang : Bytes → Prop) (Kall : List K) (bad : Nat) (agree : Nat → Nat)
    (D : Stark.PT K (Stark.Oracle F) → Prop) (hR : Udr.RbrWith V InLang Kall bad agree D)
    (Dm : Nat) (hdec : ∀ ood (P : K → Prop) b, count Kall P ≤ b →
      count (List.range roRange) (fun v => P (decChal (F := F) ood (LazyRO.answer v))) ≤ b * Dm)
    (hp : 0 < V.posPerChunk) (hpb : V.posPerChunk * V.posBits ≤ 256)
    (hql : ∀ hdr, V.headerOk hdr = true → V.queryLog hdr ≤ V.posBits)
    (G : Nat) (hG : ∀ hdr, V.headerOk hdr = true →
      agree (2 ^ V.queryLog hdr) ^ V.posPerChunk * 2 ^ (256 - V.posPerChunk * V.queryLog hdr) ≤ G)
    {S : ChallengeSpec} (P : TreeProver S) (pub : Bytes)
    (qH qP NPu NVu NPq NVq : Nat) (hN : qH + qP * NPu + NVu ≤ 2 ^ 100)
    (hPu : ∀ c wit, OracleComp.QueryBound unitWeight (P.tree pub c wit) NPu)
    (hVu : ∀ cb pb, OracleComp.QueryBound unitWeight ((starkTree (F := F) V).tree pub cb pb) NVu)
    (hPq : ∀ c wit, OracleComp.QueryBound (qWeight chunkDec) (P.tree pub c wit) NPq)
    (hVq : ∀ cb pb, OracleComp.QueryBound (qWeight chunkDec) ((starkTree (F := F) V).tree pub cb pb) NVq) :
    RomSound S InLang (starkTree (F := F) V).toVerifier P.toProver pub qH qP (qH + qP * NPu + NVu)
      (bcsNum V.numChunks (bad * Dm) (G ^ V.numChunks) qH qP NPu NVu NPq NVq)
      (roRange ^ V.numChunks) := by
  obtain ⟨hi, hm, hr, hq⟩ := transport decNone decMsg decChal_ok hQuery hPos V hS InLang Kall bad agree D hR
    Dm hdec hp hpb hql G hG
  have := stark_romSound' V hS hK hK' (DoomedB V D) InLang P pub hi hm (bad * Dm) hr (fun _ => G)
    (fun τ j hd => hq τ j hd) qH qP NPu NVu NPq NVq hN hPu hVu hPq hVq
  rwa [prod_const] at this

end ZkFormal.Bcs.Transport
