import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeGates
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordMultiplicity
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordKind
import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows
import ZkFormal.NearV3.Assembly.SchedulerCodecNonhash
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecNativeMultiplicity
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash
open ProcPriorCodecStepRows ProcPriorCodecSideMultiplicity

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State)
    (hk : k<R.n*R.n) (hf : f<3) (hg : gg<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀inter∈ProcPriorCodecActual.interactions,∀e∈inter.mult,
      Bit (e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)) := by
  obtain ⟨tail,ht,hr⟩ := successful_row I R present gb fwd (instanceCells I R present vidV) k f gg s out hf hg h
  let r := record I R present (instanceCells I R present vidV)
    (baseExtra R.n k f gg (b2n I.allowed[k]!) gb[k]!++tail) k f gg
  have hr' : out.1=s.1.push r := hr
  obtain ⟨a,har,hbits⟩ := ProcPriorCodecNativeGates.actual I R present gb fwd vidV k f gg s out hk hf hg h
  have he : a=r := Array.push_inj_right.mp (har.symm.trans hr')
  subst a
  have hflags : r[act]! =1 ∧ r[kR]! =1 ∧ r[kH]! =0 ∧ r[kZ]! =0 ∧ r[kA]! =0 ∧
      r[kF]! =0 ∧ r[ehp]! =0 ∧ r[fS]! =(if f=0 then 1 else 0) ∧
      r[fR]! =(if f=1 then 1 else 0) ∧ r[fA]! =(if f=2 then 1 else 0) := by
    dsimp only [r,record]
    exact ProcPriorCodecRecordKind.flags I R present vidV k f gg _ _ _ _ _ tail ht
  obtain ⟨_,hR,hH,hZ,hA,hF,_,hS,hRc,hFA⟩ := hflags
  have hD : r[dgg]! =0 := by
    dsimp only [r,record]
    apply ZkFormal.NearV3.Assembly.CodecDigest.record_digest_gate
    exact ProcPriorCodecExtraColumns.extra_avoids_dgg _ _ _ _ _ _ tail ht
  refine ⟨r,hr',ProcPriorCodecRecordMultiplicity.record_mult _ nxt first last trans ?_ ?_ ?_ ?_⟩
  · intro c hc
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals simp only [hH,hZ,hA,hF,hD]; rfl
  · simpa only [hR] using (show Fp.ofNat 1=(1:Fp) from rfl)
  · rw [hS,hRc]
    have hh : f=0 ∨ f=1 ∨ f=2 := by omega
    rcases hh with rfl|rfl|rfl <;> unfold Bit <;> decide +kernel
  · intro c hc
    have hb : r[c]! ≤1 := hbits c hc
    have hh : r[c]! =0 ∨ r[c]! =1 := by omega
    rcases hh with h0|h1
    · exact Or.inl (by rw [h0]; rfl)
    · exact Or.inr (by rw [h1]; rfl)
end ZkFormal.NearV3.Candidates.ProcPriorCodecNativeMultiplicity
