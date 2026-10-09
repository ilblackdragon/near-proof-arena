import ZkFormal.NearV3.Assembly.RcptCandidateKeyTraffic
-- Source TableTraffic.lean SHA256: 42bc6ad76470d41df5ea2c04755c69abce3e9520b78240460a2ebecbbe1df5b6.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyTraffic

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Every receipt interaction, on every bus and in both directions, equals the
traffic of the same concrete extracted list view. -/
theorem ListChain.view_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    TableTraffic RcptV3.interactions tr tt pub (rcptTraffic3 pub (bs.map (ListBlock.view tr tt))) := by
  unfold TableTraffic rcptTraffic3
  intro bus m
  by_cases h0 : bus=B_BYTES
  · subst bus
    exact ListChain.bytes_view_traffic hL h m
  by_cases h1 : bus=B_RCL
  · subst bus
    exact ListChain.rcl_view_traffic hL h m
  by_cases h2 : bus=B_KEYNIB
  · subst bus
    exact ListChain.key_view_traffic hL h m
  by_cases h3 : bus=B_MEM
  · subst bus
    constructor
    · rw [tableBusCount_eq,ListChain.memory_writes_view hL h]
    · rw [tableBusCount_eq,ListChain.memory_reads_view hL h]
  by_cases h4 : bus=B_RIDS
  · subst bus
    constructor
    · rw [tableBusCount_eq,ListChain.rids_view_traffic hL h true]; rfl
    · rw [tableBusCount_eq,ListChain.rids_view_traffic hL h false]; rfl
  by_cases h5 : bus=B_MPOS
  · subst bus
    constructor
    · rw [tableBusCount_eq,ListChain.mpos_view_traffic hL h true]; rfl
    · rw [tableBusCount_eq,ListChain.mpos_view_traffic hL h false]; rfl
  by_cases h6 : bus=B_SREC
  · subst bus
    constructor
    · rw [tableBusCount_eq,ListChain.signer_traffic hL h true]; rfl
    · rw [tableBusCount_eq,ListChain.signer_traffic hL h false]; rfl
  by_cases h7 : bus=B_AKC
  · subst bus
    constructor
    · rw [tableBusCount_eq,ListChain.access_counter_traffic hL h true]; rfl
    · rw [tableBusCount_eq,ListChain.access_counter_traffic hL h false]; rfl
  by_cases h8 : bus=B_BND
  · subst bus
    constructor
    · rw [tableBusCount_eq,ListChain.boundary_traffic hL h true]; rfl
    · rw [tableBusCount_eq,ListChain.boundary_traffic hL h false]; rfl
  by_cases h9 : bus=B_FINAL
  · subst bus
    constructor
    · rw [tableBusCount_eq,ListChain.final_view_traffic hL h true]; rfl
    · rw [tableBusCount_eq,ListChain.final_view_traffic hL h false]; rfl
  by_cases h10 : bus=B_DIGEST
  · subst bus
    constructor
    · rw [tableBusCount_eq,ListChain.digest_view_traffic hL h true]; rfl
    · rw [tableBusCount_eq,ListChain.digest_view_traffic hL h false]; rfl
  have hrow (q : Nat) (sd : Bool) : rowTraffic RcptV3.interactions tr tt q pub bus sd=[] := by
    rw [rowT]
    simp [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
  have hsend : rcptSends3 pub (bs.map (ListBlock.view tr tt)) bus=[] := by
    simp [rcptSends3,rSends,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,flatMap_nil_fun]
  have hrecv : rcptRecvs3 (bs.map (ListBlock.view tr tt)) bus=[] := by
    simp [rcptRecvs3,rRecvs,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,flatMap_nil_fun]
  constructor <;> simp [tableBusCount_eq,hrow,hsend,hrecv,flatMap_nil_fun]

/-- Full traffic extraction requires no public-range premise. -/
theorem extract_traffic : ∃ ls,TableTraffic RcptV3.interactions tr tt pub (rcptTraffic3 pub ls) := by
  obtain ⟨bs,e,h⟩ := extract_lists hL
  exact ⟨bs.map (ListBlock.view tr tt),ListChain.view_traffic hL h⟩

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
