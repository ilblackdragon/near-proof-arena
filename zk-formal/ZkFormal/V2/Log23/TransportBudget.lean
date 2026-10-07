import ZkFormal.V2.Log23.Verifier
import ZkFormal.Assembly.Params

/-! Numeric obligations of the actual BCS transport bound. The round-by-round
candidate RBR proof and actual prover/verifier query budgets remain open. -/
namespace ZkFormal.V2.Log23

open ZkFormal.Assembly ZkFormal.Stark

theorem dominates_through_27 :
    ∀ q, q < 28 → 8 ≤ q → chunkGood (Udr.agreeUdr 4) q ≤ g2_8 := by decide +kernel

theorem header_chunk_good {AP : AirP} {g : Nat} {hdr : List Nat}
    (h : verifierHeader AP g hdr = true) :
    chunkGood (Udr.agreeUdr 4) (queryLog AP.toAir (params g) hdr) ≤ g2_8 := by
  have hb := verifierHeader_bounds h
  exact dominates_through_27 _ (by omega) hb.2.2.2.2.1

theorem query_budget : QueryOk 24 g2_8 := udr2_K24_min8_ok

theorem full_transport_budget (NPu NVu : Nat)
    (hPu : NPu ≤ 2 ^ 32) (hVu : NVu ≤ 2 ^ 30) :
    Bcs.bcsNum 24 badAnswers (g2_8 ^ 24) (2 ^ 64) (2 ^ 40) NPu NVu 24 24 * 2 ^ 128 ≤
      ArenaCore.Security.roRange ^ 24 :=
  full_K24_min8 NPu NVu hPu hVu

end ZkFormal.V2.Log23
