import ZkFormal.NearV3.Candidates.ProcPriorRecordTopSummary
import ZkFormal.NearV3.Candidates.ProcPriorRecordLimbs
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordNativeWord
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

/-- Eight authenticated bytes determine all three natural limbs of the same
word; the top row has only two bytes and its third cell is constrained zero. -/
theorem limbs (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) (v:Nat) (hv:v<18446744073709551616)
    (hbytes:∀j,j<8→cv tr t (r+j/3) (byte0+j%3)=ProcPriorRecordLimbs.digit v j) :
    cv tr t r lo=ProcPriorIdLimbs.lo v ∧ cv tr t r mid=ProcPriorIdLimbs.mid v ∧
      cv tr t r hi=ProcPriorIdLimbs.hi v := by
  have h0:=hbytes 0 (by decide)
  have h1:=hbytes 1 (by decide)
  have h2:=hbytes 2 (by decide)
  have h3:=hbytes 3 (by decide)
  have h4:=hbytes 4 (by decide)
  have h5:=hbytes 5 (by decide)
  have h6:=hbytes 6 (by decide)
  have h7:=hbytes 7 (by decide)
  simp only [Nat.reduceDiv,Nat.reduceMod,Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7
  change cv tr t r byte1=ProcPriorRecordLimbs.digit v 1 at h1
  change cv tr t r byte2=ProcPriorRecordLimbs.digit v 2 at h2
  change cv tr t (r+1) byte1=ProcPriorRecordLimbs.digit v 4 at h4
  change cv tr t (r+1) byte2=ProcPriorRecordLimbs.digit v 5 at h5
  change cv tr t (r+2) byte1=ProcPriorRecordLimbs.digit v 7 at h7
  obtain ⟨hr1,hs1,_,hm1,hf1⟩:=ProcPriorRecordWordTraversal.limb_next hL hr hs firstLimb midLimb (by simp) hf
  obtain ⟨hr2,hs2,_,ht2,hf2⟩:=ProcPriorRecordWordTraversal.limb_next hL hr1 hs1 midLimb topLimb (by simp) hm1
  simp only [Nat.add_assoc,Nat.reduceAdd] at hr2 hs2 ht2 hf2
  have hlo:=(ProcPriorRecordPacked.limb hL hr hs firstLimb lo (by simp) hf
    (by rw [h0];exact ProcPriorRecordLimbs.digit_bound v 0)
    (by rw [h1];exact ProcPriorRecordLimbs.digit_bound v 1)
    (by rw [h2];exact ProcPriorRecordLimbs.digit_bound v 2)).1
  have hmid:=(ProcPriorRecordPacked.limb hL hr1 hs1 midLimb mid (by simp) hm1
    (by rw [h3];exact ProcPriorRecordLimbs.digit_bound v 3)
    (by rw [h4];exact ProcPriorRecordLimbs.digit_bound v 4)
    (by rw [h5];exact ProcPriorRecordLimbs.digit_bound v 5)).1
  have hhi:=(ProcPriorRecordPacked.top hL hr2 hs2 ht2
    (by rw [h6];exact ProcPriorRecordLimbs.digit_bound v 6)
    (by rw [h7];exact ProcPriorRecordLimbs.digit_bound v 7)).1
  rw [h0,h1,h2,←ProcPriorRecordLimbs.lo_bytes] at hlo
  rw [h3,h4,h5,←ProcPriorRecordLimbs.mid_bytes] at hmid
  rw [h6,h7,←ProcPriorRecordLimbs.hi_bytes v hv] at hhi
  have hm0:=hf1 mid (by simp)
  have hh0:=(hf2 hi (by simp)).trans (hf1 hi (by simp))
  exact ⟨hlo,hm0.symm.trans hmid,hh0.symm.trans hhi⟩

theorem word (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) (v:Nat) (hv:v<18446744073709551616)
    (hbytes:∀j,j<8→cv tr t (r+j/3) (byte0+j%3)=ProcPriorRecordLimbs.digit v j) :
    ProcPriorRecordSummarySound.word tr t r=v := by
  obtain ⟨hl,hm,hh⟩:=limbs hL hr hs hf v hv hbytes
  unfold ProcPriorRecordSummarySound.word
  rw [hl,hm,hh]
  exact ProcPriorIdLimbs.reconstruct v
/-- Once the eight byte identities are established, the actual top-row
summary implements saturation of that exact native word. Byte provenance
is an explicit premise, to be discharged by the authenticated record route. -/
theorem top_summary (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv tr t r firstLimb=1) (v:Nat) (hv:v<18446744073709551616)
    (hbytes:∀j,j<8→cv tr t (r+j/3) (byte0+j%3)=ProcPriorRecordLimbs.digit v j) :
    ProcPriorSummary.low v=cv tr t (r+2) lo ∧
      ProcPriorSummary.big v=decide (cv tr t (r+2) big=1) ∧
      ∀fair:Nat,(if cv tr t (r+2) big=1 then 4500000 else min (cv tr t (r+2) lo+fair) 4500000)=
        min (min (v+fair) NearSpecV3.Scheduler.u64Max) 4500000 := by
  obtain ⟨hl,hm,hh⟩:=limbs hL hr hs hf v hv hbytes
  obtain ⟨hvl,hvm,hvh⟩:=ProcPriorIdLimbs.bounds v hv
  have hsum:=ProcPriorRecordTopSummary.summary hL hr hs hf
    (by omega) (by omega) (by omega)
  rw [word hL hr hs hf v hv hbytes] at hsum
  exact hsum

end ZkFormal.NearV3.Candidates.ProcPriorRecordNativeWord
