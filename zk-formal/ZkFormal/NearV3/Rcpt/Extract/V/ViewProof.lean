import ZkFormal.NearV3.Rcpt.Extract.V.TableTraffic
import ZkFormal.NearV3.Rcpt.Extract.V.PreparedRanges

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3

/-- Complete receipt view extraction for an admissible packed public statement.
The public range premise prevents the documented field-cast aliases of u32 totals;
no premise is added to the native transition domain. -/
theorem extract_view {tr : Trace Fp} {pub : List Fp} {tt : Nat}
    (hL : TableLocal RcptV3.table tr tt pub) (hp : ReceiptPublicRanges pub) :
    ∃ ls,RcptV3Wf pub ls ∧ TableTraffic RcptV3.interactions tr tt pub (rcptTraffic3 pub ls) := by
  obtain ⟨bs,e,h⟩ := extract_lists hL
  exact ⟨bs.map (ListBlock.view tr tt),h.view_wf hL hp,h.view_traffic hL⟩

/-- Successful native preparation and the actual protocol public packing discharge
the receipt extraction's public-range obligation. Every traffic channel and local
semantic receipt/list fact holds for one and the same extracted view. -/
theorem extract_prepared_view {cb : NearSpec.Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (overhead : Nat)
    (hsize : (Public.preparedBytes p overhead).length<Algebra.P)
    (tr : Trace Fp) (tt : Nat)
    (hL : TableLocal RcptV3.table tr tt (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))) :
    ∃ ls,RcptV3Wf (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) ls ∧
      TableTraffic RcptV3.interactions tr tt (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead))
        (rcptTraffic3 (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) ls) :=
  extract_view hL (prepared_receipt_ranges hp overhead (Assembly.prepD0_roots hp) hsize)

end ZkFormal.NearV3.RcptV3Proof
