import ZkFormal.NearV3.Candidates.ProcPriorRecordSummarySound
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordTopSummary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem fields (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) :
    r+2<tr.height t ∧ cv tr t (r+2) (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv tr t (r+2) topLimb=1 ∧
      (∀x∈[sender,receiver,amount,lo,mid,hi],cv tr t (r+2) x=cv tr t r x) := by
  obtain ⟨hr1,hs1,_,hm1,hf1⟩:=ProcPriorRecordWordTraversal.limb_next hL hr hs firstLimb midLimb (by simp) hf
  obtain ⟨hr2,hs2,_,ht2,hf2⟩:=ProcPriorRecordWordTraversal.limb_next hL hr1 hs1 midLimb topLimb (by simp) hm1
  simp only [Nat.add_assoc,Nat.reduceAdd] at hr2 hs2 ht2 hf2
  exact ⟨hr2,hs2,ht2,fun x hx=>(hf2 x hx).trans (hf1 x hx)⟩

/-- The low/big allowance summary at the actual final limb belongs to the
same reconstructed word as its first limb. -/
theorem summary (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1)
    (hl:cv tr t r lo<16777216) (hm:cv tr t r mid<16777216) (hh:cv tr t r hi<65536) :
    ProcPriorSummary.low (ProcPriorRecordSummarySound.word tr t r)=cv tr t (r+2) lo ∧
      ProcPriorSummary.big (ProcPriorRecordSummarySound.word tr t r)=decide (cv tr t (r+2) big=1) ∧
      ∀fair:Nat,(if cv tr t (r+2) big=1 then 4500000 else min (cv tr t (r+2) lo+fair) 4500000)=
        min (min (ProcPriorRecordSummarySound.word tr t r+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  obtain ⟨hr2,hs2,ht2,hfields⟩:=fields hL hr hs hf
  have hlo:=hfields lo (by simp)
  have hmid:=hfields mid (by simp)
  have hhi:=hfields hi (by simp)
  have hword:cv tr t (r+2) sender+cv tr t (r+2) receiver+cv tr t (r+2) amount=1:=by
    have he:=ProcPriorRecordGeometry.limbs_eq hL hr2 hs2
    have hb:=ProcPriorRecordGeometry.words_bound hL hr2 hs2
    have ha:=ProcPriorRecordSound.flag hL hr2 hs2 act (by simp)
    omega
  have heq:ProcPriorRecordSummarySound.word tr t (r+2)=ProcPriorRecordSummarySound.word tr t r:=by
    unfold ProcPriorRecordSummarySound.word
    rw [hlo,hmid,hhi]
  have hb:=ProcPriorRecordSummarySound.big_exact hL hr2 hs2 hword (by omega) (by omega) (by omega)
  have hi:=ProcPriorRecordSummarySound.increase_exact hL hr2 hs2 hword (by omega) (by omega) (by omega)
  rw [heq] at hb hi
  exact ⟨(ProcPriorRecordSummarySound.low_exact hl).trans hlo.symm,hb,hi⟩
end ZkFormal.NearV3.Candidates.ProcPriorRecordTopSummary
