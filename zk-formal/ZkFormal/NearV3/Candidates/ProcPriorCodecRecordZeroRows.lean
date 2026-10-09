import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroRows
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash ProcPriorCodecStepRows
open ProcPriorCodecRecordZeroCells

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ a[act]! =1 ∧
      a[kR]! =1 ∧
      a[kH]! =0 ∧
      a[kZ]! =0 ∧
      a[kA]! =0 ∧
      a[fA]! =(if f=2 then 1 else 0) ∧
      a[Codec.g]! =gg ∧
      a[ig7]! =finv (fsub gg 7) ∧
      a[e7]! =(if gg=7 then 1 else 0) ∧
      a[kidx]! =k ∧
      a[NN]! =R.n*R.n ∧
      a[ikl]! =finv (fsub k (R.n*R.n-1)) ∧
      a[ekl]! =(if k+1=R.n*R.n then 1 else 0) ∧
      a[ehp]! =0 ∧
      a[esj]! =0 ∧
      a[tau]! =R.tau ∧
      a[itz]! =finv R.tau ∧
      a[zt]! =(if R.tau=0 then 1 else 0) := by
  obtain ⟨tail,ht,hr⟩ := successful_row I R present gb fwd (instanceCells I R present vidV) k f gg s out hf hg h
  let a := record I R present (instanceCells I R present vidV)
    (baseExtra R.n k f gg (b2n I.allowed[k]!) gb[k]!++tail) k f gg
  refine ⟨a,hr,?_⟩
  have hh := lookup_values 1 R.tau (b2n present) vidV R.n (R.n*R.n) I.p.base
    (I.p.maxShardBandwidth/R.n) (finv R.tau) (if R.tau=0 then 1 else 0)
    1 (5+24*k+8*f+gg)
    (if f<2 then idByte I.ids k (8*f+gg) else if gg<3 then (R.segs.getD k default).vfin/256^gg%256 else 0)
    (if ¬present then 0 else if f<2 then (if f<2 then idByte I.ids k (8*f+gg) else if gg<3 then (R.segs.getD k default).vfin/256^gg%256 else 0) else (Array.replicate (R.n*R.n) 0)[k]!/256^gg%256)
    (b2n present) k (k%256) (k/256) (if f=0 then 1 else 0) (if f=1 then 1 else 0)
    (if f=2 then 1 else 0) gg (finv (fsub gg 7)) (if gg=7 then 1 else 0)
    (finv (fsub k (R.n*R.n-1))) (if k+1=R.n*R.n then 1 else 0)
  dsimp only [a,record]
  simp only [
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht act (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht kR (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht kH (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht kZ (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht kA (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht fA (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht Codec.g (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht ig7 (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht e7 (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht kidx (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht NN (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht ikl (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht ekl (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht ehp (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht esj (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht tau (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht itz (by decide +kernel),
    projection I R present vidV _ _ _ _ _ _ _ _ tail ht zt (by decide +kernel)]
  exact hh
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordZeroRows
