import ZkFormal.Sha.Frame.Stmt
import ZkFormal.Sha.Compose

/-!
# ZkFormal.Sha.Frame.All — soundness modulo the block-level statements

`ChainStmt`, `FrameStmt` and `DigestIoStmt` are proved here from `KindStmt`
and `BlockStmt`; the lane's soundness theorems then depend only on
`KindStmt`, `BlockStmt` and `IVStmt` (lane/zk-L5-block).
-/

namespace ZkFormal.Sha

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.View ZkFormal.Sha.Frame

theorem chainStmt (hK : KindStmt) : ChainStmt := chainStmt_of hK
theorem frameStmt (hK : KindStmt) (hB : BlockStmt) : FrameStmt := frameStmt_of hK hB
theorem digestIoStmt (hK : KindStmt) : DigestIoStmt := digestIoStmt_of hK

theorem sha_bus_sound_of (hK : KindStmt) (hB : BlockStmt) (hIV : IVStmt)
    {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : ShaLocal tr t pub) :
    ∀ p ∈ digests tr t, p.2 = ArenaCore.sha256 p.1 :=
  sha_bus_sound hB hIV (chainStmt hK) (frameStmt hK hB) hL

theorem sha_digest_contract_of (hK : KindStmt) (hB : BlockStmt) (hIV : IVStmt)
    {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : ShaLocal tr t pub)
    (busBytes busDigest : Nat) {d : Nat} (hd : d < tr.height t) (hm : tr.cell t d colDmult = 1) :
    ∃ m dg, (m, dg) ∈ digests tr t ∧ dg = ArenaCore.sha256 m ∧
      (Table.interactions busBytes busDigest)[16]!.msgVal tr t d pub =
        [tr.cell t d colId, Fp.ofNat m.length] ++ dg.map (fun x => Fp.ofNat x.toNat) ∧
      ∀ i, i < m.length → ∃ r, r < tr.height t ∧ ∃ q, q < 16 ∧ tr.cell t r (colF q) = 1 ∧
        (Table.interactions busBytes busDigest)[q]!.msgVal tr t r pub =
          [tr.cell t d colId, Fp.ofNat i, Fp.ofNat (m[i]!).toNat] :=
  sha_digest_contract hB hIV (chainStmt hK) (frameStmt hK hB) (digestIoStmt hK) hL busBytes busDigest hd hm

end ZkFormal.Sha
