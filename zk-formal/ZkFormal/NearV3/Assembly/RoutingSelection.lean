import ZkFormal.NearV3.Assembly.RoutingBoundedPrep

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3

/-- Executable first matching normalized interval, in the exact public order. -/
def selectInterval (l : Layout) (own : Nat) (acct : Bytes) : Option Nat :=
  (boundedIntervals l own).findIdx? (inInterval acct)

theorem selectInterval_complete (l : Layout) (own : Nat) (acct : Bytes)
    (hr : l.shardOf acct=own) : ∃q,selectInterval l own acct=some q := by
  have ha : (boundedIntervals l own).any (inInterval acct)=true :=
    (boundedIntervals_iff l own acct).mpr hr
  have hs : (selectInterval l own acct).isSome=true := by
    simpa [selectInterval,List.findIdx?_isSome] using ha
  exact Option.isSome_iff_exists.mp hs

theorem selectInterval_valid (l : Layout) (own : Nat) (acct : Bytes) {q : Nat}
    (h : selectInterval l own acct=some q) :
    q<(boundedIntervals l own).length ∧
      inInterval acct ((boundedIntervals l own).getD q (none,none))=true := by
  obtain ⟨hq,hp,_⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨hq,?_⟩
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hq,Option.getD_some] using hp

def routeKey (bounds : List (Option Bytes×Option Bytes)) (q pos : Nat) : List Nat :=
  let iv := bounds.getD q (none,none)
  [65*q+pos,((iv.1.getD []).getD pos 0).toNat,
    ((iv.2.getD []).getD pos 0).toNat,if iv.2.isNone then 1 else 0]

theorem routeKey_public_row (bounds : List (Option Bytes×Option Bytes)) (q pos : Nat)
    (hp : pos<65) :
    routeKey bounds q pos=[65*q+pos]++(Public.boundaryRow bounds (65*q+pos)).map UInt8.toNat := by
  have hd : (65*q+pos)/65=q := by omega
  have hm : (65*q+pos)%65=pos := by omega
  simp only [routeKey,Public.boundaryRow,BND_STRIDE,hd,hm,List.map_cons,List.map_nil,List.singleton_append]
  split <;> rfl

theorem routeKey_mem (p : Prep) {q pos : Nat} (hq : q<p.bnds.length) (hp : pos<65) :
    routeKey p.bnds q pos∈Public.boundaryRecords p := by
  rw [routeKey_public_row _ q pos hp]
  apply List.mem_map.mpr
  refine ⟨65*q+pos,List.mem_range.mpr ?_,rfl⟩
  change 65*q+pos<65*p.bnds.length
  omega

/-- All byte and end-marker lookup keys of the selected native interval are
actual normalized prepared public records, not merely equal after a field cast. -/
theorem selected_requests_covered {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (acct : Bytes)
    (hr : k.L.shardOf acct=k.H.shardId) (hlen : acct.length≤64) :
    ∃q,selectInterval k.L k.H.shardId acct=some q ∧ q<128 ∧
      inInterval acct ((boundedPrep p k.L k.H.shardId).bnds.getD q (none,none))=true ∧
      ∀pos,pos≤acct.length → routeKey (boundedPrep p k.L k.H.shardId).bnds q pos∈
        Public.boundaryRecords (boundedPrep p k.L k.H.shardId) := by
  obtain ⟨q,hq⟩ := selectInterval_complete _ _ _ hr
  have hv := selectInterval_valid _ _ _ hq
  refine ⟨q,hq,native_index_bound hp hk hv.1,hv.2,?_⟩
  intro pos hpos
  exact routeKey_mem _ hv.1 (by omega)

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
