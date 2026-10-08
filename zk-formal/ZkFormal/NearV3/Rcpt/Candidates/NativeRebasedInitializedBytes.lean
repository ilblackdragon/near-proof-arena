import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedInitializedIds
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedWindowBytes

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

private theorem init_map (u : Inputs) (ss : List NodeS3) (n : Nat) :
    (records u (initializeList n ss)).map (fun s=>(s.v.ser true,s.depth))=
      (records u ss).map (fun s=>(s.v.ser true,s.depth)) := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp only [records,initializeList,List.map_cons,record,initializeMetadata] at *;rw [ih]

/-- One initialized original provider retains all authenticated rebased bytes,
depth and byte-level child IDs at the same global source index. -/
theorem replay_initialized_fields (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) {i : Nat} {b : NodeS3}
    (hb : (forestNodes 0 0 0 (rs.map ReplayTree.post))[i]?=some b) (hbw : b.v.wf) :
    ∃a,(records (forestOldInputs rs) (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))))[i]?=some a ∧
      a.v.ser true=b.v.ser false ∧ a.depth=b.depth ∧
      ∀p,a.ucid.getD p 0=NodeGen3.cidAt (forestNodes 0 0 0 (rs.map ReplayTree.post)) i p := by
  obtain ⟨a,ha,hcid⟩:=replay_initialized_provider rs hv (forestOldInputs rs) hb hbw
  have hi:=congrArg (fun xs=>xs[i]?) (init_map (forestOldInputs rs) (forestNodes 0 0 0 (rs.map ReplayTree.pre)) 0)
  rw [List.getElem?_map,ha,Option.map_some,List.getElem?_map] at hi
  cases ho : (records (forestOldInputs rs) (forestNodes 0 0 0 (rs.map ReplayTree.pre)))[i]? with
  | none => simp [ho] at hi
  | some o =>
    simp only [ho,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hi
    have hp:=replay_window_at rs hv hw ho hb
    exact ⟨a,ha,hi.1.trans hp.1,hi.2.trans hp.2,hcid⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
