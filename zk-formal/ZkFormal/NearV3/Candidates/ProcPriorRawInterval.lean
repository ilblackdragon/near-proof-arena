import ZkFormal.NearV3.Candidates.ProcPriorRawOrigin
namespace ZkFormal.NearV3.Candidates.ProcPriorRawInterval
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound ProcPriorRawOrigin
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem interval (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hheight:tr.height t≤2013265921)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) :
    ∃f,f≤r ∧ f<tr.height t ∧ cv tr t f (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t f first=1 ∧ cv tr t f act=1 ∧ cv tr t f pos=0 ∧
      r=f+cv tr t r pos ∧
      (∀x∈[tau,vid,present,count],cv tr t r x=cv tr t f x) ∧
      (∀q,f≤q→q≤r→cv tr t q (ProcPriorVertical4Linear.stage 2)=1 ∧ cv tr t q act=1) ∧
      (∀q,f<q→q≤r→cv tr t q first=0) := by
  induction r with
  | zero=>
    have hb:=flag hL hr hs first (by simp)
    have hf:cv tr t 0 first=1:=by
      by_cases hz:cv tr t 0 first=0
      · have hh:=ProcPriorRawBackward.positive hL hr hs ha hz;omega
      · omega
    have hp:=first_pos hL hr hs hf
    exact ⟨0,by omega,hr,hs,hf,ha,hp,by omega,(fun _ _=>rfl),(by intro q hq hq0;have he:q=0:=(by omega);simpa [he] using And.intro hs ha),(by intro q hq hq0;omega)⟩
  | succ r ih=>
    try simp only [Nat.succ_eq_add_one] at *
    have hb:=flag hL hr hs first (by simp)
    by_cases hf:cv tr t (r+1) first=1
    · have hp:=first_pos hL hr hs hf
      exact ⟨r+1,by omega,hr,hs,hf,ha,hp,by omega,(fun _ _=>rfl),(by intro q hq hqr;have he:q=r+1:=(by omega);simpa [he] using And.intro hs ha),(by intro q hq hqr;omega)⟩
    · have hf0:cv tr t (r+1) first=0:=by omega
      obtain ⟨hsp,_,hap⟩:=ProcPriorRawBackward.previous hL hr hs ha hf0
      obtain ⟨f,hfr,hfh,hfs,hff,hfa,hfp,he,hfields,hactive,hnotfirst⟩:=ih (by omega) hsp hap
      obtain ⟨hincr,hcarry⟩:=step hL hr hsp hap (not_done hL hr hsp ha hf0)
      have hnext:cv tr t (r+1) pos=cv tr t r pos+1:=by
        rcases hincr with h|h
        · exact h
        · omega
      refine ⟨f,by omega,hfh,hfs,hff,hfa,hfp,by omega,?_,?_,?_⟩
      · intro x hx
        exact (hcarry x hx).trans (hfields x hx)
      · intro q hfq hqr
        by_cases he:q=r+1
        · simpa [he] using And.intro hs ha
        · exact hactive q hfq (by omega)
      · intro q hfq hqr
        by_cases he:q=r+1
        · simpa [he] using hf0
        · exact hnotfirst q hfq (by omega)
end ZkFormal.NearV3.Candidates.ProcPriorRawInterval
