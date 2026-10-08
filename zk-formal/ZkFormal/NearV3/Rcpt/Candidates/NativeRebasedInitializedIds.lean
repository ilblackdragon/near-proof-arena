import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedChildIds
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestMetadata

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

private theorem initialized_ids (ns : List NodeS3) (n : Nat) :
    (initializeList n ns).map NodeS3.ucid=ns.map (fun s=>windowIds s.v) := by
  induction ns generalizing n with
  | nil => rfl
  | cons s ns ih => simp only [initializeList,List.map_cons,initializeMetadata,ih]

/-- Initialized child IDs in the original updated forest agree with the actual
rebased native node's window IDs, without reinitializing post-write counters. -/
theorem replay_initialized_ids (rs : List ReplayTree) (h : ∀r∈rs,r.Valid) (u : Inputs) :
    (records u (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))).map NodeS3.ucid=
      (forestNodes 0 0 0 (rs.map ReplayTree.post)).map (fun s=>windowIds s.v) := by
  simp only [records,List.map_map,Function.comp_def,record]
  rw [initialized_ids,replay_forest_window_lists rs 0 0 0 0 h]

/-- Exact per-byte initialized metadata transfer at a shared global index. -/
theorem replay_initialized_cid_at (rs : List ReplayTree) (h : ∀r∈rs,r.Valid)
    (u : Inputs) {i : Nat} {a b : NodeS3}
    (ha : (records u (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))))[i]?=some a)
    (hb : (forestNodes 0 0 0 (rs.map ReplayTree.post))[i]?=some b)
    (hw : b.v.wf) (p : Nat) :
    a.ucid.getD p 0=NodeGen3.cidAt (forestNodes 0 0 0 (rs.map ReplayTree.post)) i p := by
  have he:=congrArg (fun xs=>xs[i]?) (replay_initialized_ids rs h u)
  have hi : a.ucid=windowIds b.v := by
    simpa only [List.getElem?_map,ha,hb,Option.map_some,Option.some.injEq] using he
  rw [hi]
  rw [Candidates.NativeNodeChildIds.window_at b.v hw p]
  simp only [NodeGen3.cidAt,NodeGen3.layN,NodeGen3.rec,List.getD_eq_getElem?_getD,hb,Option.getD_some]
  rfl

/-- Initialization and digest updates retain a provider at every actual rebased
source index; no coverage premise is required from the caller. -/
theorem replay_initialized_provider (rs : List ReplayTree) (h : ∀r∈rs,r.Valid)
    (u : Inputs) {i : Nat} {b : NodeS3}
    (hb : (forestNodes 0 0 0 (rs.map ReplayTree.post))[i]?=some b) (hw : b.v.wf) :
    ∃a,(records u (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))))[i]?=some a ∧
      ∀p,a.ucid.getD p 0=NodeGen3.cidAt (forestNodes 0 0 0 (rs.map ReplayTree.post)) i p := by
  let ns:=records u (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))
  have hl:=congrArg List.length (replay_initialized_ids rs h u)
  simp only [List.length_map] at hl
  have hi : i<ns.length := by
    change i<(records u (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))).length
    rw [hl]
    exact (List.getElem?_eq_some_iff.mp hb).1
  have ha : ns[i]?=some ns[i] := List.getElem?_eq_getElem hi
  exact ⟨ns[i],ha,fun p=>replay_initialized_cid_at rs h u ha hb hw p⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
