import ZkFormal.NearV3.Rcpt.Candidates.NativeRootRecords
import ZkFormal.NearV3.Assembly.UpsertAncestorCost

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

theorem allocated_post_widths (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hv : ∀u∈us,u.Valid) (hcount : insts.length=us.length)
    (hi : ∀tau u I,us[tau]?=some u→insts[tau]?=some I→AllocatedNativeInstance us tau u I) :
    ∀I∈insts,I.post.length=32 := by
  intro I hI
  obtain ⟨i,hib,rfl⟩:=List.getElem_of_mem hI
  have hub : i<us.length:=by omega
  have ha:=hi i us[i] insts[i] (by simp [hub]) (by simp [hib])
  rw [ha.2.2.1,List.length_map]
  exact traceUpsert_output_hash_length (hv _ (List.getElem_mem hub)).1

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
