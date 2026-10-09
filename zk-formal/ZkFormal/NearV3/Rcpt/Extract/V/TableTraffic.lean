import ZkFormal.NearV3.Rcpt.Extract.V.KeyTraffic

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Every receipt interaction, on every bus and in both directions, equals the
traffic of the same concrete extracted list view. -/
theorem ListChain.view_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    TableTraffic RcptV3.interactions tr tt pub (rcptTraffic3 pub (bs.map (ListBlock.view tr tt))) := by
  unfold TableTraffic rcptTraffic3
  intro bus m
  by_cases h0 : bus=B_BYTES
  · subst bus
    exact h.bytes_view_traffic hL m
  by_cases h1 : bus=B_RCL
  · subst bus
    exact h.rcl_view_traffic hL m
  by_cases h2 : bus=B_KEYNIB
  · subst bus
    exact h.key_view_traffic hL m
  by_cases h3 : bus=B_MEM
  · subst bus
    constructor
    · rw [tableBusCount_eq,h.memory_writes_view hL]
    · rw [tableBusCount_eq,h.memory_reads_view hL]
  by_cases h4 : bus=B_RIDS
  · subst bus
    constructor
    · rw [tableBusCount_eq,h.rids_view_traffic hL true]; rfl
    · rw [tableBusCount_eq,h.rids_view_traffic hL false]; rfl
  by_cases h5 : bus=B_MPOS
  · subst bus
    constructor
    · rw [tableBusCount_eq,h.mpos_view_traffic hL true]; rfl
    · rw [tableBusCount_eq,h.mpos_view_traffic hL false]; rfl
  by_cases h6 : bus=B_SREC
  · subst bus
    constructor
    · rw [tableBusCount_eq,h.signer_traffic hL true]; rfl
    · rw [tableBusCount_eq,h.signer_traffic hL false]; rfl
  by_cases h7 : bus=B_AKC
  · subst bus
    constructor
    · rw [tableBusCount_eq,h.access_counter_traffic hL true]; rfl
    · rw [tableBusCount_eq,h.access_counter_traffic hL false]; rfl
  by_cases h8 : bus=B_BND
  · subst bus
    constructor
    · rw [tableBusCount_eq,h.boundary_traffic hL true]; rfl
    · rw [tableBusCount_eq,h.boundary_traffic hL false]; rfl
  by_cases h9 : bus=B_FINAL
  · subst bus
    constructor
    · rw [tableBusCount_eq,h.final_view_traffic hL true]; rfl
    · rw [tableBusCount_eq,h.final_view_traffic hL false]; rfl
  by_cases h10 : bus=B_DIGEST
  · subst bus
    constructor
    · rw [tableBusCount_eq,h.digest_view_traffic hL true]; rfl
    · rw [tableBusCount_eq,h.digest_view_traffic hL false]; rfl
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
  exact ⟨bs.map (ListBlock.view tr tt),h.view_traffic hL⟩

end ZkFormal.NearV3.RcptV3Proof
