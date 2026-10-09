import ZkFormal.NearV3.Candidates.ProcPriorCodecWrapperTotal
import ZkFormal.NearV3.Candidates.ProcActualPreparedGenerator
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecNativeTotal
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

theorem initial_allowances (ids : List Nat) (k : Nat) :
    (ProcActualInput.allowances ids NearSpec.Bandwidth.State.initial)[k]! = 0 := by
  simp only [ProcActualInput.allowances,NearSpec.Bandwidth.State.initial,List.foldl_nil]
  by_cases hk : k<ids.length*ids.length
  · rw [getElem!_pos _ k (by simpa using hk)]
    simp
  · rw [getElem!_neg _ k (by simpa using hk)]
    rfl

theorem decoded_absent (old : Option NearSpec.Bytes) (prev : NearSpec.Bandwidth.State)
    (hd : ProcActualCore.decodePrevious old=some prev) (ids : List Nat)
    (hn : old.isSome=false) : ∀k : Nat,(ProcActualInput.allowances ids prev)[k]! = 0 := by
  cases old with
  | some bytes => cases hn
  | none =>
    simp only [ProcActualCore.decodePrevious,Option.some.injEq] at hd
    subst prev
    exact initial_allowances ids

theorem decoded_codec_success (sp : SchedPub) (hs : SchedPubOk sp)
    (old : Option NearSpec.Bytes) (prev : NearSpec.Bandwidth.State)
    (hd : ProcActualCore.decodePrevious old=some prev) (tau : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R)
    (vid : Nat) (gb : Array Nat) (fwd : List (Nat×Nat))
    (hf : ∀k,k<R.n*R.n → R.tau=0 → ProcPriorCodecRecordTotal.Forward R gb fwd k) :
    ∃o,ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R old.isSome vid gb fwd=.ok o :=
  ProcPriorCodecWrapperTotal.run_codec_success _ tau R old.isSome vid gb fwd hs.params hr
    (decoded_absent old prev hd sp.ids) hf

open NearSpec NearSpecV3 in
/-- Non-main scheduler calls construct both corrected generators without a
forwarding premise: the executable codec only checks forwarding at tau zero. -/
theorem native_nonmain {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (sp : SchedPub) (hsp : sp∈p.sched)
    (ctx : ApplyCtx) (hpub : schedPub ctx=some sp)
    (old : Option Bytes) (nativeOut : Output) (hcore : runCore sp old=some nativeOut)
    (tau : Nat) (ht : tau≠0) (vid : Nat) (gb : Array Nat) (fwd : List (Nat×Nat)) :
    ∃prev R o,ProcActualCore.decodePrevious old=some prev ∧
      ActualRun.run (ProcPreparedSequence.input sp prev) tau=.ok R ∧
      ProcPriorCodecGen.codecRows (ProcPreparedSequence.input sp prev) R old.isSome vid gb fwd=.ok o := by
  obtain ⟨prev,R,hd,hr⟩ := ProcActualPreparedGenerator.native_success hp sp hsp ctx hpub old nativeOut hcore tau
  have hτ := (ProcActualRunProjection.run_fields _ tau R hr).1
  obtain ⟨o,ho⟩ := decoded_codec_success sp (prepD0_sched hp sp hsp) old prev hd tau R hr vid gb fwd
    (by intro k hk hz; exact (ht (hτ.symm.trans hz)).elim)
  exact ⟨prev,R,o,hd,hr,ho⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecNativeTotal
