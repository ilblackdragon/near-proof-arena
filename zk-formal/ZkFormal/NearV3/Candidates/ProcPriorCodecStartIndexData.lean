import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroRows
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedInstance
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecStartIndexData
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecStepRows ProcPriorCodecExtra

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (s out : State) (hf:f<3) (hg:g<8)
    (h:step I R present gb fwd (instanceCells I R present vidV) k f g s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[srcC]! =k/R.n ∧ a[useC]! =k%R.n ∧
      a[hasC]! =(if k%R.n+1=R.n then 1 else 0) ∧ a[rs]! =(if f=0 ∧ g=0 then 1 else 0) ∧
      a[nn]! =R.n ∧ a[kidx]! =k ∧ a[ehp]! =0 := by
  obtain ⟨tail,ht,ha⟩:=successful_row I R present gb fwd (instanceCells I R present vidV) k f g s out hf hg h
  let a:=record I R present (instanceCells I R present vidV)
    (baseExtra R.n k f g (b2n I.allowed[k]!) gb[k]!++tail) k f g
  have hc : a[srcC]! =k/R.n ∧ a[useC]! =k%R.n ∧
      a[hasC]! =(if k%R.n+1=R.n then 1 else 0) ∧ a[rs]! =(if f=0 ∧ g=0 then 1 else 0) ∧
      a[al]! =b2n I.allowed[k]! ∧ a[Codec.gb]! =gb[k]! :=
    ProcPriorCodecRecordBase.counters I present R.n k f g _ _ _ _ _ (instanceCells I R present vidV) tail ht
  have hi : ProcPriorCodecSideCarry.Instance I R present vidV a :=
    ProcCodecGeneratedInstance.record I R present vidV k f g _ _ _ _ _ tail ht
  have hnn : a[nn]! =R.n := by
    rw [hi nn (by simp [ProcPriorCodecSideCarry.instanceColumns])]
    simp [ProcPriorCodecSideCarry.instanceValue,instanceCells,SchedSetAll.lookup,
      act,tau,pres,vid,nn,NN,base,fair,itz,zt]
  obtain ⟨b,hb,_,_,_,_,_,_,_,_,_,hkidx,_,_,_,hehp,_⟩:=
    ProcPriorCodecRecordZeroRows.actual I R present gb fwd vidV k f g s out hf hg h
  have heq : b=a := Array.push_inj_right.mp (hb.symm.trans ha)
  subst b
  exact ⟨a,ha,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hnn,hkidx,hehp⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecStartIndexData
