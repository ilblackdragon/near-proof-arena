import ZkFormal.NearV3.Render.Ups.CodecRelaySanity
import ZkFormal.NearV3.Render.Ups.CodecRelayLengthGlobal
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched

theorem codecRelay_table_inventory {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr t pub Ps fwd)
    (hn : Ps.length<2013265921) (m : List Fp) :
    tableBusCount codecTable.interactions tr t pub B_BYTES true m =
      cnt ((relayTaus tr t).flatMap fun tau=>relayValueMsgs tau (relaySchedValue tr t tau)) m +
        cnt (codecSanityMsgs tr t pub) m := by
  rw [codecRelay_tableBytes,←codecSanityMsgs_count]
  have he:=(codecRelay_inventory hl hh hs hn).count_eq m
  exact congrArg (·+cnt (codecSanityMsgs tr t pub) m) he

/-- Converts an explicit decomposition of actual physical SHA byte sends into
the compact UPS extraction interface. The residual family remains explicitly
owned by the caller; this does not assert whole-AIR isolation by itself. -/
theorem codecRelay_global_bytes {tr : Trace Fp} {tc tu : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr tc pub) (hh : tr.height tc≤2^22)
    {Ps : List InstPub} {fwd : List (Nat×Nat)} (hs : CodecSparSupply tr tc pub Ps fwd)
    (hn : Ps.length≤32) {v : List UpsSeg} {upsIs : List Interaction}
    (hup : TableTraffic upsIs tr tu pub (upsTraffic v))
    {shaR : Nat→List Fp→Nat} {others : List Msg}
    (htotal : ∀m,shaR B_BYTES m =
      tableBusCount codecTable.interactions tr tc pub B_BYTES true m +
      tableBusCount upsIs tr tu pub B_BYTES true m + cnt others m)
    (hothers : ∀m∈others,∀a,m.head?=some a → a<P ∧ a%16≠K_VUPS) :
    (∀m,shaR B_BYTES m = cnt
      ((relayTaus tr tc).flatMap (fun tau=>relayValueMsgs tau (relaySchedValue tr tc tau)) ++
        (upsTraffic v).sends B_BYTES ++ (codecSanityMsgs tr tc pub ++ others)) m) ∧
    (∀m∈codecSanityMsgs tr tc pub ++ others,∀a,m.head?=some a → a<P ∧ a%16≠K_VUPS) := by
  constructor
  · intro m
    rw [htotal,codecRelay_table_inventory hl hh hs (by omega), (hup B_BYTES m).1]
    simp only [cnt,List.map_append,List.count_append]
    omega
  · intro m hm a ha
    rcases List.mem_append.mp hm with hm|hm
    · exact codecSanityMsgs_other hl hh hs hn m hm a ha
    · exact hothers m hm a ha
end ZkFormal.NearV3.Render.UpsRelay
