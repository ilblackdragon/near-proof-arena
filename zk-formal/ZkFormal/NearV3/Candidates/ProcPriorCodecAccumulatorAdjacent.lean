import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorLoop
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorAdjacent
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep
open ProcPriorCodecAccumulator ProcPriorCodecAccumulatorRows ProcPriorCodecAccumulatorLoop

/-- Adjacent executable allowance rows share the actual updated accumulator. -/
theorem adjacent (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k g : Nat) (s mid out : State)
    (hk : k<R.n*R.n) (hg : g<7)
    (ha : step I R present gb fwd inst k 2 g s=.ok (.yield mid))
    (hb : step I R present gb fwd inst k 2 (g+1) mid=.ok (.yield out)) :
    ∃a b,mid.1=s.1.push a ∧ out.1=mid.1.push b ∧
      b[Codec.ap]! = a[Codec.ap]! ∧
      b[Codec.apost]! = a[Codec.apost]! +256^g*postByte R k g ∧
      b[Codec.big]! = a[Codec.big]! := by
  obtain ⟨a,har,hap,hapost,hbig⟩ := cells I R present gb fwd inst k g s mid (by omega) ha
  obtain ⟨b,hbr,hbp,hbpost,hbbig⟩ := cells I R present gb fwd inst k (g+1) mid out (by omega) hb
  obtain ⟨he1,he2,he3⟩ := byte_native_accumulators I R present gb fwd inst k g s mid (by omega) hk ha
  exact ⟨a,b,har,hbr,by omega,by omega,by omega⟩

/-- The terminal row reads the completed low24 accumulator before the final step. -/
theorem terminal (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k : Nat) (rows : Array (Array Nat))
    (cmps : List (Nat×Nat×Nat)) (mid out : State) (hk : k<R.n*R.n)
    (hp : forIn (List.range 7) (rows,cmps,0,0,0,0)
      (fun g st=>step I R present gb fwd inst k 2 g st)=.ok mid)
    (hs : step I R present gb fwd inst k 2 7 mid=.ok (.yield out)) :
    ∃row,out.1=mid.1.push row ∧ row[Codec.ap]! =0 ∧
      row[Codec.apost]! =(R.segs.getD k default).vfin%16777216 ∧ row[Codec.big]! =0 := by
  obtain ⟨ha,hp',hb⟩ := bytes I R present gb fwd inst k (List.range 7)
    (rows,cmps,0,0,0,0) mid hk (by intro g hg; simp at hg; omega) hp
  have he : ((List.range 7).map (fun g=>256^g*postByte R k g)).sum=
      (R.segs.getD k default).vfin%16777216 := by
    simpa [List.range_succ,postByte,Nat.add_assoc] using low24_digits (R.segs.getD k default).vfin
  obtain ⟨row,hr,hr1,hr2,hr3⟩ := cells I R present gb fwd inst k 7 mid out (by decide) hs
  exact ⟨row,hr,by simpa [ha] using hr1,by simpa [hp',he] using hr2,by simpa [hb] using hr3⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorAdjacent
