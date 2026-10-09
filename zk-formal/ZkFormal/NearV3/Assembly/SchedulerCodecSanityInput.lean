import ZkFormal.NearV3.Assembly.SchedulerSanityJobs
import ZkFormal.NearV3.Candidates.ProcPreparedSequence

namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates

/-- Exactly the native corrected Codec SHA input, including absent prior state. -/
def codecSanityInput (I : Sched.Gen.Input) (present : Bool) : Bytes :=
  ((if present then I.prev.sanityHash.map UInt8.toNat else List.replicate 32 0)++
    I.ash.map UInt8.toNat).map UInt8.ofNat

/-- Read/decode/public preparation pins the generator's SHA input to the
same scheduler witness, rather than assuming equality of digest outputs. -/
theorem prepared_sanity_input {u : SchedulerUpsertWitness} {sp : Scheduler.SchedPub}
    {prev : Option Bytes} {old : Bandwidth.State}
    (hr : readKey u.pre keyBwState "bandwidth scheduler state"=.ok prev)
    (hp : schedPub u.ctx=some sp)
    (hd : (match prev with | none=>some Bandwidth.State.initial | some b=>Bandwidth.State.decode b)=some old) :
    schedulerWitnessSanity u=some (codecSanityInput (ProcPreparedSequence.input sp old) prev.isSome) := by
  cases prev with
  | none=>
    cases hd
    simp only [schedulerWitnessSanity,hr,hp,Option.bind_some,schedulerSanityInput,
      codecSanityInput,ProcPreparedSequence.input,Option.isSome_none]
    simp only [ite_false,List.map_append,nativeBytes_roundtrip]
    simp [Bandwidth.State.initial,zeroHash,zeros]
  | some b=>
    simp only [schedulerWitnessSanity,hr,hp,Option.bind_some,schedulerSanityInput,hd,
      codecSanityInput,ProcPreparedSequence.input,Option.isSome_some]
    simp only [ite_true,List.map_append,nativeBytes_roundtrip,bind,Option.bind]

/-- Every actual accepted scheduler run supplies those exact native input
components. No separate prior-state or action-hash identity is required. -/
theorem witness_sanity_input {u : SchedulerUpsertWitness} (hv : u.Valid) :
    ∃sp prev old,readKey u.pre keyBwState "bandwidth scheduler state"=.ok prev ∧
      schedPub u.ctx=some sp ∧
      (match prev with | none=>some Bandwidth.State.initial | some b=>Bandwidth.State.decode b)=some old ∧
      schedulerWitnessSanity u=some (codecSanityInput (ProcPreparedSequence.input sp old) prev.isSome) := by
  obtain ⟨so,hs,_⟩:=hv.2
  obtain ⟨prev,sp,o,hr,hp,hcore,_⟩:=schedStep_complete hs
  cases prev with
  | none=>exact ⟨sp,none,Bandwidth.State.initial,hr,hp,rfl,prepared_sanity_input hr hp rfl⟩
  | some b=>
    unfold Scheduler.runCore at hcore
    dsimp only at hcore
    obtain ⟨old,hd,hrest⟩:=Option.bind_eq_some_iff.mp hcore
    exact ⟨sp,some b,old,hr,hp,hd,prepared_sanity_input hr hp hd⟩

end ZkFormal.NearV3.Assembly.CodecDigest
