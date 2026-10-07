import ZkFormal.NearV3.Public.SchedulerWidth
import ZkFormal.NearV3.Public.Bounds

/-! Concrete prepared-statement segment widths and fit, with no independent
count or offset premise. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpecV3

theorem prepared_width (p : Prep) (hr : RootsSized p)
    (hs : ∀ s ∈ p.lists, s.root.length = 32) {i : Nat} (hi : i < 9) :
    ∀ row ∈ (preparedBlocks p).getD i [], row.length = (plans.getD i sourcePlan).width := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sourcePayload_width p.lists hs
  · exact boundaryPayload_width p.bnds
  · exact bodyPayload_width p.body
  · exact natPayload_width _ 7 (render_pubb_width _ _)
  · exact natPayload_width _ 11 (render_par_width _ _)
  · exact natPayload_width _ 5 (dl_width _ _)
  · exact natPayload_width _ 5 (dl_width _ _)
  · intro row hrow
    change row ∈ [[UInt8.ofNat 0] ++ p.hdr.prevStateRoot] at hrow
    obtain rfl := List.mem_singleton.mp hrow
    simp only [List.length_append,List.length_cons,List.length_nil,hr.1]
    rfl
  · intro row hrow
    change row ∈ [[UInt8.ofNat (p.hdr.K+1)] ++ p.hdr.postStateRoot] at hrow
    obtain rfl := List.mem_singleton.mp hrow
    simp only [List.length_append,List.length_cons,List.length_nil,hr.2.1]
    rfl

theorem plan_width_positive {i : Nat} (hi : i < 9) : 0 < (plans.getD i sourcePlan).width := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem prepared_segment_fits (p : Prep) (witnessOverhead maxPub : Nat)
    (hr : RootsSized p) (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (preparedBytes p witnessOverhead).length ≤ maxPub) (hmax : maxPub < 256^4)
    (seg : PubSeg) (hseg : seg ∈ preparedSegments) :
    seg.fits maxPub (ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)) = true := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hseg
  have hi : i < 9 := List.mem_range.mp hi
  rw [← headerBytes_length p witnessOverhead hr]
  exact descriptor_fits_of_bound _ _ _ (by rw [preparedBlocks_length]; exact hi)
    (plan_width_positive hi) (prepared_width p hr hs hi) hlen hmax

end ZkFormal.NearV3.Public
