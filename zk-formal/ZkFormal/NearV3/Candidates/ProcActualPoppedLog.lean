import ZkFormal.NearV3.Candidates.ProcActualReplayTotal
import ZkFormal.NearV3.Candidates.ProcPushConservation
namespace ZkFormal.NearV3.Candidates.ProcActualPoppedLog
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcActualReplayRound ProcActualBucketGuards

def buckets (s : Acc) : Array (Nat×Nat×Nat×Nat) := s.2.2.2.2.2.2.2.2.1

theorem collect_exact (R K z : Nat) (bs : List Push) (acc : Array (Nat×Nat×Nat×Nat))
    (ht : ∀b∈bs,b.key=K ∧ b.z=z) :
    ∃out,forIn bs acc (collectStep R K z)=.ok out ∧
      out.toList=acc.toList++bs.map (ProcPushConservation.stamp R) := by
  induction bs generalizing acc with
  | nil => exact ⟨acc,rfl,by simp⟩
  | cons b bs ih =>
    have hb := ht b (by simp)
    let next := acc.push (ProcPushConservation.stamp R b)
    have hstep : collectStep R K z b acc=.ok (.yield next) := by
      simp [collectStep,hb.1,hb.2,check,next,ProcPushConservation.stamp,
        bind,Except.bind,pure,Except.pure]
    obtain ⟨out,ho,he⟩ := ih next (fun b hb => ht b (by simp [hb]))
    refine ⟨out,by simpa only [List.forIn_cons,hstep,bind,Except.bind] using ho,?_⟩
    simpa [next,List.append_assoc] using he

set_option maxHeartbeats 800000 in
theorem round_buckets (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (s out : Acc) (ht : Tagged rd) (h : step I cv key rd s=.ok (.yield out)) :
    (buckets out).toList=(buckets s).toList++rd.bucket.map (ProcPushConservation.stamp cv.size) := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  obtain ⟨col,hcol,he⟩ := collect_exact cv.size rd.key rd.z rd.bucket bs ht
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    have hc := Except.ok.inj (hcol.symm.trans (by assumption))
    simpa only [buckets,hc] using he
theorem loop_buckets (I : Input) (cv : Array CReq) (key : List Nat) (rs : List Round)
    (s out : Acc) (ht : ∀rd∈rs,Tagged rd)
    (h : forIn rs s (step I cv key)=.ok out) :
    (buckets out).toList=(buckets s).toList++
      (ProcPushConservation.popped rs).map (ProcPushConservation.stamp cv.size) := by
  induction rs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; simp [ProcPushConservation.popped]
  | cons rd rs ih =>
    rw [List.forIn_cons] at h
    cases he : step I cv key rd s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨next,rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s next he
      simp only [he,bind,Except.bind] at h
      have hn := round_buckets I cv key rd s next (ht rd (by simp)) he
      have hh := ih next (fun rd hr=>ht rd (by simp [hr])) h
      rw [hn] at hh
      simpa [ProcPushConservation.popped,List.map_append,List.append_assoc] using hh

theorem replay_buckets (I : Input) (cv : Array CReq) (rs : List Round) (out : Acc)
    (ht : ∀rd∈rs,Tagged rd) (h : ProcActualReplayFactor.replay I cv rs=.ok out) :
    (buckets out).toList=(ProcPushConservation.popped rs).map (ProcPushConservation.stamp cv.size) := by
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩ := ProcActualReplayTotal.reads_array lp.a2 lp.g2 cv
    (Array.replicate (I.ids.length*I.ids.length) #[])
  change (forIn cv _ (ProcActualReplayFactor.readStep lp.a2 lp.g2) >>= fun ops =>
    forIn rs (ProcActualReplayInitial.initial I cv ops) (step I cv (NearSpecV3.leWords I.seed)))=.ok out at h
  rw [hop] at h
  have hh := loop_buckets I cv (NearSpecV3.leWords I.seed) rs _ out ht h
  simpa [buckets,ProcActualReplayInitial.initial] using hh

/-- Actual popped records conserve the complete model push multiset. Binding
actual generated-push records to that multiset is still a separate obligation. -/
theorem process_conservation (I : Input) (cv : Array CReq) (st : PState) (rs : List Round)
    (hp : ProcActualInput.process I=.ok (st,rs)) (out : Acc)
    (hr : ProcActualReplayFactor.replay I cv rs=.ok out) :
    (((ProcModelStep.initial (convRaw I.p I.ids.length I.raw) (ProcActualInput.initial I)).1++
      ProcPushConservation.generated rs).map (ProcPushConservation.stamp cv.size)).Perm
      (buckets out).toList := by
  have ht := process_tags I.ids.length I.allowed _ _ st _ rs hp
  rw [replay_buckets I cv rs out ht hr]
  exact (ProcPushConservation.process_perm I.ids.length I.allowed _ _ st _ rs hp).map _

end ZkFormal.NearV3.Candidates.ProcActualPoppedLog
