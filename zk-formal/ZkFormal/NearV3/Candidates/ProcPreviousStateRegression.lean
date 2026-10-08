import ZkFormal.NearV3.Candidates.ProcNativeInitial
namespace ZkFormal.NearV3.Candidates.ProcPreviousStateRegression
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

def previous : NearSpec.Bandwidth.State :=
  ⟨[⟨99,0,7⟩,⟨0,1,0⟩,⟨1,0,0⟩,⟨1,1,0⟩],List.replicate 32 0⟩
def params : Params := ⟨100000,4500000,4194304,4194304,4500000⟩
def pub : SchedPub :=
  ⟨[0,1],params,#[false,false,false,false],[],requestValues params,List.replicate 32 0,NearSpec.sha256 (NearSpec.u32 2++NearSpec.concatAll ([0,1].map NearSpec.u64))⟩
def input : Input := ProcPreparedSequence.input pub previous

def nativeAllowances : Array Nat :=
  previous.links.foldl (fun a la=>
    match indexOf pub.ids la.sender,indexOf pub.ids la.receiver with
    | some s,some r=>a.set! (s*pub.ids.length+r) la.allowance
    | _,_=>a) (Array.replicate (pub.ids.length*pub.ids.length) 0)

theorem actual_pub : pubOf Config.pv86 NearSpecV3.CongestionConfig.pv86 [0,1] [] []
    (List.replicate 32 0)=some pub := by rfl

theorem params_valid : Params.calculate Config.pv86 pub.ids.length=some pub.params := by decide +kernel
theorem previous_decodes : NearSpec.Bandwidth.State.decode previous.encode=some previous := by decide +kernel
theorem native_accepts : (runCore pub (some previous.encode)).isSome=true := by decide +kernel
theorem native_initial_zero : nativeAllowances[0]! =0 := by decide +kernel
theorem model_initial_seven : (a0Src pub.ids previous)[0]! =7 := by decide +kernel
theorem native_after_increase :
    (nativeAllowances.map (fun a=>min (min (a+params.maxShardBandwidth/pub.ids.length) u64Max) params.maxAllowance))[0]! =2250000 := by decide +kernel
theorem model_after_link_pass : (ProcCoreReplay.initial input).al[0]! =2250007 := by decide +kernel

theorem native_run_accepts :
    (NearSpecV3.Scheduler.run Config.pv86 NearSpecV3.CongestionConfig.pv86 [0,1]
      (some previous.encode) [] [] (List.replicate 32 0)).isSome=true := by
  rw [run_eq_core,actual_pub]
  exact native_accepts

theorem native_state_prefix :
    (runCore pub (some previous.encode)).map (fun o=>o.state.take 29)=
      some ([0]++NearSpec.u32 4++NearSpec.u64 0++NearSpec.u64 0++NearSpec.u64 2250000) := by decide +kernel

theorem model_state_prefix :
    (match coreEv input.ids input.p input.allowed input.raw input.seed input.ash input.prev with
      | .error _=>none | .ok o=>some (o.state.take 29))=
      some ([0]++NearSpec.u32 4++NearSpec.u64 0++NearSpec.u64 0++NearSpec.u64 2250007) := by decide +kernel

/-- Native decoding/core execution accepts this prior-state fixture, while the
positional canonical model reads a different initial allowance. This is not a
whole checkD0a accepted-witness fixture. -/
theorem allowance_mismatch : nativeAllowances≠a0Src pub.ids previous := by
  intro h
  have hh := congrArg (fun a : Array Nat=>a[0]!) h
  rw [native_initial_zero,model_initial_seven] at hh
  contradiction
end ZkFormal.NearV3.Candidates.ProcPreviousStateRegression
