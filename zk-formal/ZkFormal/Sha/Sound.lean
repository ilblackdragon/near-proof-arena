import ZkFormal.Sha.Frame.All
import ZkFormal.Sha.Sound.Block

/-!
# ZkFormal.Sha.Sound — lane L5 soundness, closed (no hypotheses)

* `sha_bus_sound_closed`: every `(m, d)` claimed by a legal SHA table has
  `d = ArenaCore.sha256 m`;
* `sha_digest_contract_closed`: the digest-bus contract consumed by lane L6;
* `sha_bus_sound_holds`: the DESIGN.md form, from `Air.Holds`.
-/

namespace ZkFormal.Sha

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.View

theorem sha_bus_sound_closed {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : ShaLocal tr t pub) :
    ∀ p ∈ digests tr t, p.2 = ArenaCore.sha256 p.1 :=
  sha_bus_sound_of Sound.kindStmt Sound.blockStmt Sound.ivStmt hL

theorem sha_bus_sound_holds {A : Air} {pub : List Fp} {tr : Trace Fp} (h : Holds A pub tr)
    {t busBytes busDigest : Nat} (ht : t < A.tables.length)
    (hT : A.tables[t] = Table.table busBytes busDigest) :
    ∀ p ∈ digests tr t, p.2 = ArenaCore.sha256 p.1 :=
  sha_bus_sound_closed (shaLocal_of_holds h ht hT)

theorem sha_digest_contract_closed {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : ShaLocal tr t pub)
    (busBytes busDigest : Nat) {d : Nat} (hd : d < tr.height t) (hm : tr.cell t d colDmult = 1) :
    ∃ m dg, (m, dg) ∈ digests tr t ∧ dg = ArenaCore.sha256 m ∧
      (Table.interactions busBytes busDigest)[16]!.msgVal tr t d pub =
        [tr.cell t d colId, Fp.ofNat m.length] ++ dg.map (fun x => Fp.ofNat x.toNat) ∧
      ∀ i, i < m.length → ∃ r, r < tr.height t ∧ ∃ q, q < 16 ∧ tr.cell t r (colF q) = 1 ∧
        (Table.interactions busBytes busDigest)[q]!.msgVal tr t r pub =
          [tr.cell t d colId, Fp.ofNat i, Fp.ofNat (m[i]!).toNat] :=
  sha_digest_contract_of Sound.kindStmt Sound.blockStmt Sound.ivStmt hL busBytes busDigest hd hm

end ZkFormal.Sha
