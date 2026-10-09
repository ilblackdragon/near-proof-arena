import ZkFormal.NearV3.Assembly.RoutingBoundedPrep
import ZkFormal.NearV3.Public.PreparedFit

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3

private theorem length_filterMap_if {α β : Type} (xs : List α) (test : α→Bool) (f : α→β) :
    (xs.filterMap (fun x=>if test x then some (f x) else none)).length=(xs.filter test).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : test x <;> simp [h,ih]

theorem ownIntervals_length (l : Layout) (own : Nat) :
    (ownIntervals l own).length=
      ((List.range (l.boundaries.length+1)).filter (fun k=>l.shardIds.getD k 0==own)).length := by
  exact length_filterMap_if _ _ _

theorem interval_count_nonincreasing (l : Layout) (own : Nat) :
    (boundedIntervals l own).length≤(ownIntervals l own).length := by
  rw [boundedIntervals,ownIntervals_length,ownIntervals_length]
  have hs : List.Sublist (List.range ((boundedLayout l).boundaries.length+1))
      (List.range (l.boundaries.length+1)) :=
    List.range_sublist.mpr (by simp [boundedLayout];omega)
  exact (hs.filter (fun k=>l.shardIds.getD k 0==own)).length_le

theorem boundary_payload_bytes (bs : List (Option Bytes×Option Bytes)) :
    (Public.payloadBytes (Public.boundaryPayload bs)).length=195*bs.length := by
  rw [Public.payload_length _ 3 (Public.boundaryPayload_width bs),Public.boundaryPayload_length]
  unfold BND_STRIDE
  omega

/-- Packed metadata has fixed byte width. Replacing the expanded boundaries by
the bounded representation cannot increase the actual public statement bytes. -/
theorem prepared_length_nonincreasing (p : Prep) (l : Layout) (own overhead : Nat)
    (hb : p.bnds=ownIntervals l own) :
    (Public.preparedBytes (boundedPrep p l own) overhead).length≤
      (Public.preparedBytes p overhead).length := by
  have hc := interval_count_nonincreasing l own
  simp only [Public.preparedBytes,Public.encode_length,Public.dataStart,
    Public.preparedBlocks,Public.dataBytes,List.flatMap_cons,List.flatMap_nil,
    List.length_append,List.length_cons,List.length_nil,boundedPrep]
  simp only [Public.headerBytes,Public.schedulerRecords]
  rw [boundary_payload_bytes,boundary_payload_bytes,hb]
  omega

/-- Existing global public-size/no-wrap bounds transfer unchanged to the
candidate's updated counts and offsets. No old offsets are reused. -/
theorem prepared_fit_transfer (p : Prep) (l : Layout) (own overhead maxPub : Nat)
    (hb : p.bnds=ownIntervals l own) (hr : Public.RootsSized p)
    (hs : ∀s∈p.lists,s.root.length=32)
    (hlen : (Public.preparedBytes p overhead).length≤maxPub) (hmax : maxPub<256^4)
    (seg : ZkFormal.V2.PubSeg) (hseg : seg∈Public.preparedSegments) :
    seg.fits maxPub (ZkFormal.Udr.pubOf ZkFormal.Algebra.Fp
      (Public.preparedBytes (boundedPrep p l own) overhead))=true := by
  apply Public.prepared_segment_fits (boundedPrep p l own) overhead maxPub hr hs
  · exact Nat.le_trans (prepared_length_nonincreasing p l own overhead hb) hlen
  · exact hmax
  · exact hseg

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
