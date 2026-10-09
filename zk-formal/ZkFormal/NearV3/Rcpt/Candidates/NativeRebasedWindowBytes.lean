import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedDepths
import ZkFormal.NearV3.Rcpt.Candidates.NativeSetWf
import ZkFormal.NearV3.Assembly.ForestNodeBytes

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

/-- The updated original records and the rebased reader forest serialize to
identical post bytes in the same global occurrence order. -/
theorem replay_window_bytes (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (post : Bool) :
    (records (forestOldInputs rs) (forestNodes 0 0 0 (rs.map ReplayTree.pre))).map (fun s=>s.v.ser true)=
      (forestNodes 0 0 0 (rs.map ReplayTree.post)).map (fun s=>s.v.ser post) := by
  rw [forestOldInputs_all_bytes rs hv hw]
  symm
  apply forestNodes_bytes
  intro t ht
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp ht
  exact SizedAccountRun.wf (hv r hr) (hw r hr)

/-- Exact indexed byte and depth transport into the original updated provider.
The indices are shared, not chosen by a byte-equality search. -/
theorem replay_window_at (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) {i : Nat} {a b : NodeS3}
    (ha : (records (forestOldInputs rs) (forestNodes 0 0 0 (rs.map ReplayTree.pre)))[i]?=some a)
    (hb : (forestNodes 0 0 0 (rs.map ReplayTree.post))[i]?=some b) :
    a.v.ser true=b.v.ser false ∧ a.depth=b.depth := by
  constructor
  · have he:=congrArg (fun xs=>xs[i]?) (replay_window_bytes rs hv hw false)
    simpa only [List.getElem?_map,ha,hb,Option.map_some,Option.some.injEq] using he
  · exact replay_updated_depth_at rs hv (forestOldInputs rs) ha hb

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
