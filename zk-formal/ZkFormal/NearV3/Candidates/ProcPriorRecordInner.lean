import ZkFormal.NearV3.Candidates.ProcPriorRecordCells
import ZkFormal.NearV3.Candidates.ProcPriorRawBoolean
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordInner
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open NearSpec NearSpec.Bandwidth NearSpecV3.Scheduler
open ProcPriorCells ProcPriorRecordRows ProcPriorRecordTable ProcPriorRecordCells

theorem inner_constraints (ids : List Nat) (tau j w g : Nat) (r : LinkAllowance)
    (hw:w<3) (hg:g<2) (hv:value ⟨j,w,g,r⟩<18446744073709551616)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cell ids tau ⟨j,w,g,r⟩) (cell ids tau ⟨j,w,g+1,r⟩) 0 0 1)=0 := by
  let v:=value ⟨j,w,g,r⟩
  let high:=ProcPriorIdLimbs.mid v+ProcPriorIdLimbs.hi v
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  have hzero:Fp.ofNat 0=(0:Fp):=rfl
  have hsf:=ProcPriorCells.bit_bool (indexOf ids r.sender).isSome
  have hrf:=ProcPriorCells.bit_bool (indexOf ids r.receiver).isSome
  have hbig:=ProcPriorCells.bit_bool (decide (high≠0))
  have missing (x : Option Nat) : (1-bit x.isSome)*Fp.ofNat (x.getD 0)=0 := by
    cases x <;> simp [bit,hzero] <;> grind
  have hsm:=missing (indexOf ids r.sender)
  have hrm:=missing (indexOf ids r.receiver)
  have hl:=congrArg Fp.ofNat (ProcPriorRecordLimbs.lo_bytes v)
  have hm:=congrArg Fp.ofNat (ProcPriorRecordLimbs.mid_bytes v)
  have hbound:high<P:=by
    have hh:=ProcPriorRecordLimbs.high_sum_bound v hv
    have hp:P>16842752:=by decide +kernel
    omega
  have hinv:=ProcPriorRawBoolean.inv_delta high 0 hbound (by decide +kernel)
  have hhigh:bit (decide (high≠0))=1-bit (decide (high=0)) := by
    by_cases hh:high=0 <;> simp [hh,bit] <;> grind
  have hnon:Fp.ofNat high*(1-bit (decide (high≠0)))=0 := by
    by_cases hh:high=0 <;> simp [hh,bit,hzero] <;> grind
  simp only [hzero] at hinv
  have hf:constraints.map (·.evalWith
      (env (cell ids tau ⟨j,w,g,r⟩) (cell ids tau ⟨j,w,g+1,r⟩) 0 0 1))=
      List.replicate constraints.length (0:Fp) := by
    have hw':w=0 ∨ w=1 ∨ w=2:=by omega
    have hg':g=0 ∨ g=1:=by omega
    rcases hw' with rfl|rfl|rfl <;> rcases hg' with rfl|rfl
    all_goals simp [constraints,ZkFormal.Chacha.Table.boolC,ProcPriorRecordTable.header,words,limbs,packed,
      adjacent,sameRecord,sameWord,notE,sub,k,c,n,Expr.evalWith,env,ProcPriorRecordCells.cell,value,
      act,ProcPriorRecordTable.tau,record,shards,sender,receiver,amount,firstLimb,midLimb,topLimb,
      byte0,byte1,byte2,lo,mid,hi,senderFound,senderIndex,receiverFound,receiverIndex,
      big,bigInv,writeGate,bit,hone,hzero,List.replicate]
    all_goals simp only [v,value,high,bit] at hsf hrf hbig hsm hrm hl hm hinv hhigh hnon
    all_goals grind
  have hmemb:e.evalWith (env (cell ids tau ⟨j,w,g,r⟩) (cell ids tau ⟨j,w,g+1,r⟩) 0 0 1)
      ∈constraints.map (·.evalWith (env (cell ids tau ⟨j,w,g,r⟩) (cell ids tau ⟨j,w,g+1,r⟩) 0 0 1)):=
    List.mem_map.mpr ⟨e,he,rfl⟩
  rw [hf] at hmemb
  exact (List.mem_replicate.mp hmemb).2

end ZkFormal.NearV3.Candidates.ProcPriorRecordInner
