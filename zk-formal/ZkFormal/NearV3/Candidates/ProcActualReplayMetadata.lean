import ZkFormal.NearV3.Candidates.ProcActualReplayClock
import ZkFormal.NearV3.Candidates.ProcActualRoundOrder
namespace ZkFormal.NearV3.Candidates.ProcActualReplayMetadata
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcActualReplayRound

def rounds (s : Acc) : Array Gen.RoundD := s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

def keys (s : Acc) := (rounds s).toList.map (fun rd=>(rd.K,rd.z))

set_option maxHeartbeats 800000 in
theorem step_metadata (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (s out : Acc) (hs : ProcActualReplayChain.Inv s)
    (h : step I cv key rd s=.ok (.yield out)) :
    ProcActualReplayChain.Inv out ∧ keys out=keys s++[(rd.key,rd.z)] := by
  rcases s with ⟨sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi⟩
  unfold step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    constructor
    · simp only [ProcActualReplayChain.Inv,Array.toList_push]
      exact ProcActualReplayChain.Stamped.snoc hs _ _ _ _ _
    · simp [keys,rounds]

theorem loop_metadata (I : Input) (cv : Array CReq) (key : List Nat) (rs : List Round)
    (s out : Acc) (hs : ProcActualReplayChain.Inv s)
    (h : forIn rs s (step I cv key)=.ok out) :
    ProcActualReplayChain.Inv out ∧ keys out=keys s++rs.map (fun rd=>(rd.key,rd.z)) := by
  induction rs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; exact ⟨hs,by simp⟩
  | cons rd rs ih =>
    rw [List.forIn_cons] at h
    cases he : step I cv key rd s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok next =>
      obtain ⟨mid,rfl⟩ := ProcActualRoundTransition.step_yields I cv key rd s next he
      simp only [he,bind,Except.bind] at h
      obtain ⟨hm,hk⟩ := step_metadata I cv key rd s mid hs he
      obtain ⟨ho,hl⟩ := ih mid hm h
      exact ⟨ho,by simpa [hk,List.append_assoc] using hl⟩

theorem replay_metadata (I : Input) (cv : Array CReq) (rs : List Round) (out : Acc)
    (h : ProcActualReplayFactor.replay I cv rs=.ok out) :
    ProcActualReplayChain.Inv out ∧ keys out=rs.map (fun rd=>(rd.key,rd.z)) := by
  let lp := linkPass I.ids.length I.p I.allowed (ProcActualInput.allowances I.ids I.prev)
  obtain ⟨ops,hop⟩ := ProcActualReplayTotal.reads_array lp.a2 lp.g2 cv
    (Array.replicate (I.ids.length*I.ids.length) #[])
  change (forIn cv _ (ProcActualReplayFactor.readStep lp.a2 lp.g2) >>= fun ops =>
    forIn rs (ProcActualReplayInitial.initial I cv ops) (step I cv (NearSpecV3.leWords I.seed)))=.ok out at h
  rw [hop] at h
  have hs : ProcActualReplayChain.Inv (ProcActualReplayInitial.initial I cv ops) :=
    ProcActualReplayChain.Stamped.nil
  obtain ⟨hi,hk⟩ := loop_metadata I cv _ rs _ out hs h
  exact ⟨hi,by simpa [keys,rounds,ProcActualReplayInitial.initial] using hk⟩

theorem replay_trace (I : Input) (cv : Array CReq) (st : PState) (rs : List Round) (out : Acc)
    (hp : ProcActualInput.process I=.ok (st,rs))
    (hr : ProcActualReplayFactor.replay I cv rs=.ok out) :
    ∃last,ProcActualZeroTrace.Trace last (keys out) := by
  rw [(replay_metadata I cv rs out hr).2]
  exact ProcActualZeroTrace.process_trace _ _ _ _ _ _ _ hp

theorem replay_zero_rules (I : Input) (cv : Array CReq) (st : PState) (rs : List Round) (out : Acc)
    (hp : ProcActualInput.process I=.ok (st,rs))
    (hr : ProcActualReplayFactor.replay I cv rs=.ok out) :
    ∀rd∈(rounds out).toList,ProcActualRoundOrder.ZeroRule rd := by
  obtain ⟨last,ht⟩ := replay_trace I cv st rs out hp hr
  exact (ProcActualRoundOrder.stamped_rules (replay_metadata I cv rs out hr).1 ht).2
open ProcActualReplayChain ProcActualRoundOrder ProcActualZeroTrace ProcActualZeroTransition in
theorem stamped_decreasing {T kp Kq zq : Nat} {rs : List Gen.RoundD}
    (hs : Stamped T kp Kq zq rs) {last : Option (Nat×Nat)}
    (ht : Trace last (rs.map (fun rd=>(rd.K,rd.z))))
    (hb : ∀rd∈rs,rd.K<Proc.KSENT) :
    ∀rd∈rs,rd.K≠0 → rd.K<rd.Kq := by
  induction hs generalizing last with
  | nil => simp
  | @snoc T kp Kq zq rs hs K z L kend es ih =>
    simp only [List.map_append,List.map_cons,List.map_nil] at ht
    obtain ⟨prev,hp,hl,hv,ho,hz⟩ := trace_snoc (rs.map (fun rd=>(rd.K,rd.z))) K z ht
    have hc := (stamped_rules hs hp).1
    have hi := ih hp (fun rd hr=>hb rd (by simp [hr]))
    intro rd hr hn
    simp only [List.mem_append,List.mem_singleton] at hr
    rcases hr with hr|rfl
    · exact hi rd hr hn
    · cases prev with
      | none =>
        have hq : Kq=Proc.KSENT := hc.1
        have hbound := hb ⟨K,z,T,L,kp,kend,Kq,zq,es⟩ (by simp)
        simpa [hq] using hbound
      | some p =>
        rcases p with ⟨K',z'⟩
        have hq : K'=Kq := hc.1
        change K<Kq
        change K≠0 at hn
        unfold Ordered at ho
        omega

theorem replay_decreasing (I : Input) (cv : Array CReq) (st : PState) (rs : List Round) (out : Acc)
    (hp : ProcActualInput.process I=.ok (st,rs))
    (hr : ProcActualReplayFactor.replay I cv rs=.ok out)
    (hb : ∀rd∈(rounds out).toList,rd.K<Proc.KSENT) :
    ∀rd∈(rounds out).toList,rd.K≠0 → rd.K<rd.Kq := by
  obtain ⟨last,ht⟩ := replay_trace I cv st rs out hp hr
  exact stamped_decreasing (replay_metadata I cv rs out hr).1 ht hb
end ZkFormal.NearV3.Candidates.ProcActualReplayMetadata
