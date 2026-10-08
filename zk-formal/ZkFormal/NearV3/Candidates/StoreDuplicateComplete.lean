import ZkFormal.NearV3.Candidates.TrieCountComplete
import ZkFormal.NearV3.Candidates.NativeValueWf
namespace ZkFormal.NearV3.Candidates.StoreDuplicateComplete
open ZkFormal.Near ZkFormal.Algebra ZkFormal.Air Render
open StoreDuplicateMetadata CombinedStoreOccurrences

theorem assigned_getD (rs : List Occurrence) (vs : List NodeS3) (i : Nat) (hi : i<vs.length) :
    (assign rs 0 vs).getD i default=patch rs i (vs.getD i default) := by
  have hh:=assign_get rs vs 0 i
  have ha : i<(assign rs 0 vs).length := by simpa [assign_length] using hi
  simpa [List.getD, List.getElem?_eq_getElem hi,List.getElem?_eq_getElem ha] using hh

theorem assigned_cid (rs : List Occurrence) (vs : List NodeS3) (i p : Nat) (hi : i<vs.length) :
    NodeGen3.cidAt (assign rs 0 vs) i p=NodeGen3.cidAt vs i p := by
  simp only [NodeGen3.cidAt,NodeGen3.layN,NodeGen3.rec,assigned_getD rs vs i hi,patch]

/-- Selecting duplicate representatives preserves every honest node renderer
premise, including byte-window child IDs and the final SUM row capacity. -/
theorem node_ok (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hn : NodeOk vs) (hv : ValWf es) :
    NodeOk (assign (allOccurrences vs tau es) 0 vs) := by
  let rs:=allOccurrences vs tau es
  refine ⟨(StoreOccurrenceIds.assigned_wf vs tau es hn.wf hv).1,?_,?_,?_,?_,?_⟩
  · simpa [assign_length] using hn.pos
  · intro s hs
    obtain ⟨i,o,ho,rfl⟩:=assign_member rs vs 0 s hs
    exact hn.depth o ho
  · intro s hs
    obtain ⟨i,o,ho,rfl⟩:=assign_member rs vs 0 s hs
    exact hn.lenB o ho
  · simpa [assign_bytes] using hn.rows
  · intro n hni p hp
    have hi : n<vs.length := by simpa [assign_length] using hni
    rw [assigned_getD rs vs n hi] at hp ⊢
    rw [assigned_cid rs vs n p hi]
    exact hn.ucid n hi p hp

/-- Same concrete node/value duplicate assignment has full local validity and
all semantic traffic on the count-extended physical log22 tables. Global bus
balance is a separate obligation. -/
theorem complete (vs : List NodeS3) (tau : ValE→Nat) (es : List ValE)
    (hn : NodeOk vs) (hv : ValWf es) (t : Nat) (pub : List Fp) :
    let ns:=assign (allOccurrences vs tau es) 0 vs
    let vals:=ValueDuplicateMetadata.assign (allOccurrences vs tau es) tau es
    TableLocal Rcpt.Candidates.SizeCount.nodeTable (TrieCountHeight.node ns pub) t pub ∧
    TableTraffic Rcpt.Candidates.SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) t pub
      (TrieCountComplete.withSize (nodeTraffic3 ns) (TrieCountComplete.nodeSize ns)) ∧
    TableLocal Rcpt.Candidates.SizeCount.valTable (TrieCountHeight.value vals pub) t pub ∧
    TableTraffic Rcpt.Candidates.SizeCount.valTable.interactions (TrieCountHeight.value vals pub) t pub
      (TrieCountComplete.withSize (valTraffic vals) (TrieCountComplete.valueSize vals)) := by
  have hnv:=TrieCountComplete.node_complete _ (node_ok vs tau es hn hv) t pub
  have hvv:=TrieCountComplete.value_complete _
    ⟨(StoreOccurrenceIds.assigned_wf vs tau es hn.wf hv).2⟩ t pub
  exact ⟨hnv.1,hnv.2.1,hvv.1,hvv.2.1⟩
end ZkFormal.NearV3.Candidates.StoreDuplicateComplete
