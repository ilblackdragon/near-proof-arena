import ZkFormal.NearV3.Assembly.PrepContext
import ZkFormal.NearV3.Sched.Pub.Prep
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

def schedulerContexts (k : WalkD0) (m : MainExecutionV3) : List ApplyCtx :=
  m.ctx k :: k.implicitBlks.map (fun b=>blockCtx k.L k.H.shardId k.slotB2.gasLimit b b.hdr.nextGasPrice)

def preparedScheduler (ctx : ApplyCtx) : Except String Scheduler.SchedPub :=
  match schedPub ctx with
  | some sp=>pure sp
  | none=>throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)"

private theorem mapError_ok_iff {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f=.ok a ↔ x=.ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
theorem prepClaim_contexts {cb : Bytes} {pc : PrepC} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepClaim cb=.ok pc) (hw : walkD0 cb=.ok k) (hm : m.NativeValid k w) :
    (schedulerContexts k m).mapM preparedScheduler=.ok pc.sched := by
  have hmb := hm.block
  have hmp := hm.previous
  unfold prepClaim at hp
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok hp; clear hp; have hp := hn; clear hn)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    simp_all only [mapError_ok_iff, pure, Except.pure, Except.ok.injEq]
    unfold walkD0 at hw
    simp only [*, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hw
    repeat' (first
      | (have hh := hw; clear hw; obtain ⟨_, _, hw⟩ := bind_ok hh; clear hh)
      | (split at hw)
      | (dsimp only at hw))
    all_goals try (cases hw; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at hw
      subst hw
      expose_names
      have hb2 : w_23 = i_3 := by grind only
      have hslot : p_1.2 = w_31 := by
        rw [←hb2,heq_2] at heq_8
        simp only [Option.bind_some,heq_5,Option.some.injEq] at heq_8
        grind only
      unfold schedulerContexts MainExecutionV3.ctx preparedScheduler
      simp only [pure,Except.pure]
      grind only

theorem prepD0_contexts {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k) (hm : m.NativeValid k w) :
    (schedulerContexts k m).mapM preparedScheduler=.ok p.sched := by
  obtain ⟨pc,hpc,hbody⟩ := bind_ok hp
  rw [prepBody_sched hbody]
  exact prepClaim_contexts hpc hw hm

theorem preparedScheduler_spec {ctx : ApplyCtx} {sp : Scheduler.SchedPub}
    (h : preparedScheduler ctx=.ok sp) : schedPub ctx=some sp := by
  unfold preparedScheduler at h
  split at h
  · simp only [pure,Except.pure,Except.ok.injEq] at h
    subst sp
    assumption
  · cases h

theorem contexts_index {ctxs : List ApplyCtx} {ps : List Scheduler.SchedPub}
    (h : ctxs.mapM preparedScheduler=.ok ps) (i : Nat) (ctx : ApplyCtx)
    (hi : ctxs[i]?=some ctx) :
    ∃sp,ps[i]?=some sp ∧ schedPub ctx=some sp := by
  induction ctxs generalizing ps i with
  | nil => simp at hi
  | cons c cs ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨sp,hsp,h⟩ := bind_ok h
    obtain ⟨rest,hrest,h⟩ := bind_ok h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst ps
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hi
      subst ctx
      exact ⟨sp,rfl,preparedScheduler_spec hsp⟩
    | succ i => exact ih hrest i hi

theorem prepD0_context_index {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k) (hm : m.NativeValid k w)
    (i : Nat) (ctx : ApplyCtx) (hi : (schedulerContexts k m)[i]?=some ctx) :
    ∃sp,p.sched[i]?=some sp ∧ schedPub ctx=some sp :=
  contexts_index (prepD0_contexts hp hw hm) i ctx hi
end ZkFormal.NearV3.Assembly
