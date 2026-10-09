import ZkFormal.NearV3.Assembly.CompactSplitChildTargets
import ZkFormal.NearV3.Assembly.SchedulerDigestPlanJobs

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

def digestJobIds (xs : List Msg) : List Nat := xs.map (fun m=>m.getD 0 0)
def fieldJob (I : Render.UpsInst) (j : Nat) : Nat := (Fp.ofNat (upsertJobId I.tau j)).toNat

private theorem split_case_bound (I : Render.UpsInst) (k : Nat) (hi : InstOk I)
    (hp : PartOk I k (part I k)) (hk : (part I k).kind=10) : 4≤I.ci := by
  by_cases hkt:k<nTof I.ci I.ti
  · have he:=hp.kindT hkt
    have hb:k<4:=Nat.lt_of_lt_of_le hkt (nTof_le I.ci hi.ci I.ti hi.ti)
    apply Nat.le_of_not_gt
    intro hn
    rcases (show I.ci=0∨I.ci=1∨I.ci=2∨I.ci=3 by omega) with hc|hc|hc|hc <;>
      rcases (show k=0∨k=1∨k=2∨k=3 by omega) with h|h|h|h <;>
      simp [hc,h,hk,UCase.all,UCase.split,termPlan,UKind.ix] at he hk <;> omega
  · have hu:=hp.kindU (by omega)
    omega

/-- Exact per-part physical job-ID permutation. Ordinary nonempty target-child
shape is explicit for RDB/RBI; payload/hash equality is proved separately. -/
theorem physical_part_job_ids (I : Render.UpsInst) (k : Nat) (hi : InstOk I)
    (hf : FieldsOk (part I k)) (hp : PartOk I k (part I k)) (hw : WindowOk I (part I k))
    (hn : (part I k).kind=0∨(part I k).kind=5→0<nWin (part I k).shape) :
    (digestJobIds ((List.range (part I k).q.length).flatMap (nodeDigestMsgs I k))).Perm
      ((partDigestUses (UCase.all.getD I.ci .LP) k (UKind.all.getD (part I k).kind .RDB)).map (fieldJob I)) := by
  have hb:=hp.kind
  rcases (show (part I k).kind=0∨(part I k).kind=1∨(part I k).kind=2∨(part I k).kind=3∨
      (part I k).kind=4∨(part I k).kind=5∨(part I k).kind=6∨(part I k).kind=7∨
      (part I k).kind=8∨(part I k).kind=9∨(part I k).kind=10∨(part I k).kind=11 by omega)
    with hk|hk|hk|hk|hk|hk|hk|hk|hk|hk|hk|hk
  · rw [selected_branch_inventory I k hf hp (by omega) (hn (by omega))]
    simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,hk]
  · rw [extension_child_target I k hf hp (by omega)]
    simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,hk]
  · rw [fresh_leaf_target I k hf hp (by omega)]
    simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,hk]
  · rw [branch_value_target I k hf hp (by omega)]
    simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,hk]
  · rw [branch_value_target I k hf hp (by omega)]
    simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,hk]
  · rw [selected_branch_inventory I k hf hp (by omega) (hn (by omega))]
    simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,hk]
  · rw [moved_leaf_no_digest I k hf hp hk]
    simp [digestJobIds,partDigestUses,UKind.all,hk]
  · rw [moved_extension_no_digest I k hf hp hk]
    simp [digestJobIds,partDigestUses,UKind.all,hk]
  · rw [fresh_leaf_target I k hf hp (by omega)]
    simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,hk]
  · rw [extension_child_target I k hf hp (by omega)]
    simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,hk]
  · have hc:=split_case_bound I k hi hp hk
    have hci:=hi.ci
    rcases (show I.ci=4∨I.ci=5∨I.ci=6∨I.ci=7∨I.ci=8∨I.ci=9∨I.ci=10 by omega)
      with hc|hc|hc|hc|hc|hc|hc
    · rw [split_lsa_targets I k hf hp hw hk hc]
      simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,UCase.all,hk,hc]
    · rw [split_value_moved_targets I k hf hp hw hk (by omega)]
      simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,UCase.all,hk,hc]
    · rw [split_two_child_targets I k hf hp hw hk (by omega)]
      split <;> simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,UCase.all,hk,hc]
      exact List.Perm.swap _ _ []
    · rw [split_value_moved_targets I k hf hp hw hk (by omega)]
      simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,UCase.all,hk,hc]
    · rw [split_value_copied_targets I k hf hp hw hk hc]
      simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,UCase.all,hk,hc]
    · rw [split_two_child_targets I k hf hp hw hk (by omega)]
      split <;> simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,UCase.all,hk,hc]
      exact List.Perm.swap _ _ []
    · rw [split_copied_child_target I k hf hp hw hk hc]
      simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,UCase.all,hk,hc]
  · rw [extension_child_target I k hf hp (by omega)]
    simp [digestJobIds,digestWindow,digMsg,fieldJob,partDigestUses,UKind.all,hk]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
