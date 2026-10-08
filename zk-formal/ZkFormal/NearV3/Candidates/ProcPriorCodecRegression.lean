import ZkFormal.NearV3.Candidates.ProcPriorCodecGen
import ZkFormal.NearV3.Candidates.ProcPreviousStateRegression
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRegression
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcPreviousStateRegression

def nativeInitial : PState:=ProcActualInput.initial input
/-- The fixture has no requests and no allowed links. Its final allowances are
therefore the exact native link-pass values. No general Run-validity is asserted. -/
def fixtureRun : Run:=
  {tau:=0,n:=2,base:=params.base,D:=0,seed:=input.seed,key:=[],a2:=nativeInitial.al,
   conv:=[],used:=#[],rounds:=[],
   segs:=(List.range 4).map (fun l=>⟨addrOf 0 0 l,true,false,0,nativeInitial.al[l]!,0,[]⟩),
   cmps:=[],kfin:=0,fin:=nativeInitial}

def output : Except String CodecOut:=
  ProcPriorCodecGen.codecRows input fixtureRun true 0 #[0,0,0,0] []

def outputSome : Option CodecOut:=match output with | .ok o=>some o | .error _=>none

theorem old_generator_rejects :
    (match Gen.codecRows input fixtureRun true 0 #[0,0,0,0] [] with
     | .error s=>s=="codec a2 differs from the link pass" | .ok _=>false)=true := by
  decide +kernel

theorem repaired_generator_succeeds : (outputSome.map fun o=>o.rows.size)=some 165 := by
  decide +kernel

theorem original_prior_bytes : (outputSome.map (·.pre))=some (previous.encode.map (fun x : UInt8=>x.toNat)) := by
  decide +kernel

theorem actual_prior_query : (outputSome.map fun o=>(o.rows[23]!)[Codec.apR]!)=some 0 := by
  decide +kernel

theorem native_post_prefix : (outputSome.map fun o=>o.post.take 29)=
    some (([0]++NearSpec.u32 4++NearSpec.u64 0++NearSpec.u64 0++NearSpec.u64 2250000).map (fun x : UInt8=>x.toNat)) := by
  decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorCodecRegression
