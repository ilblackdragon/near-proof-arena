import ZkFormal.NearV3.Assembly.RoutingQCandidate
import ZkFormal.NearV3.Rcpt.Extract.V.RouteRows

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptV3Proof

theorem extracted_q_lt {tr : Trace Fp} {t : Nat} {pub : List Fp} {y : RS}
    (h : TableLocal candidateTable tr t pub)
    (lay : Layout tr t y.s y.h y.Lp y.Lv y.Ls y.kt) : (rcptOf tr t y).q<128 := by
  have hb := local_base h
  have F := route_receiver hb lay
  have hz : 0<y.Lv := by have hh := lay.pos;omega
  have hs : tr.cell t (lkRow y 0) sV=1 := by simpa using F.fld.st 0 hz
  have hf : tr.cell t (lkRow y 0) fs=1 := by simpa using F.fld.fs 0 hz
  have hq := first_receiver_q_lt h (route_height hb lay 0 (by omega)) hs hf
  have he := F.consts 0 hz RcptV3.q (by simp [rconsts])
  simp only [Nat.add_zero] at he
  change cv tr t y.s RcptV3.q<128
  simpa only [cv,he] using hq

end ZkFormal.NearV3.Assembly.RoutingQCandidate
