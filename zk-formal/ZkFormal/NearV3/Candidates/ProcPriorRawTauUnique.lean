import ZkFormal.NearV3.Candidates.ProcPriorRawTauSteps
namespace ZkFormal.NearV3.Candidates.ProcPriorRawTauUnique
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound ProcPriorRawTauSteps
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem active_back (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    {a b:Nat} (hab:a≤b) (hb:b<tr.height t)
    (hsa:cv tr t a (ProcPriorVertical4Linear.stage 2)=1)
    (hsb:cv tr t b (ProcPriorVertical4Linear.stage 2)=1) (ha:cv tr t b act=1) :cv tr t a act=1 := by
  induction b with
  | zero=>have he:a=0:=(by omega);subst a;exact ha
  | succ b ih=>
    by_cases he:a=b+1
    · subst a;exact ha
    · have hsp:=ProcPriorStageOrder.raw_interval hL (show a≤b by omega) (show b≤b+1 by omega) hb hsa hsb
      have hap:=ProcPriorRawBackward.previous_active hL hb hsp (last_zero hL hb hsp hsb) ha
      exact ih (by omega) (by omega) hsp hap

theorem monotone (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hh:tr.height t≤2013265921) {a b:Nat} (hab:a≤b) (hb:b<tr.height t)
    (hsa:cv tr t a (ProcPriorVertical4Linear.stage 2)=1)
    (hsb:cv tr t b (ProcPriorVertical4Linear.stage 2)=1) (ha:cv tr t b act=1) :
    cv tr t a tau≤cv tr t b tau := by
  induction b with
  | zero=>have he:a=0:=(by omega);subst a;exact Nat.le_refl _
  | succ b ih=>
    by_cases he:a=b+1
    · subst a;exact Nat.le_refl _
    · have hsp:=ProcPriorStageOrder.raw_interval hL (show a≤b by omega) (show b≤b+1 by omega) hb hsa hsb
      have hap:=ProcPriorRawBackward.previous_active hL hb hsp (last_zero hL hb hsp hsb) ha
      have hp:=ih (by omega) (by omega) hsp hap
      have hbound:=bound hL (show b<tr.height t by omega) hsp hap
      have hn:=next_tau hL hb hsp hap ha
      omega

theorem first_increase (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hh:tr.height t≤2013265921) {r:Nat} (hr:r+1<tr.height t)
    (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hn:cv tr t (r+1) (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t (r+1) act=1) (hf:cv tr t (r+1) first=1) :
    cv tr t (r+1) tau=cv tr t r tau+1 := by
  have hap:=ProcPriorRawBackward.previous_active hL hr hs (last_zero hL hr hs hn) ha
  have hr0:r<tr.height t:=by omega
  have hpos:cv tr t r pos≤r:=by
    obtain ⟨f,_,_,_,_,_,_,he,_⟩:=ProcPriorRawOrigin.origin hL hh hr0 hs hap
    omega
  have hzero:=ProcPriorRawOrigin.first_pos hL hr hn hf
  have hhash:cv tr t r hash=1:=by
    have hb:=flag hL hr0 hs hash (by simp)
    by_cases hz:cv tr t r hash=0
    · have hp:=(ProcPriorRawOrigin.step hL hr hs hap (Or.inl hz)).1
      omega
    · omega
  have hend:cv tr t r phaseEnd=1:=by
    have hb:=flag hL hr0 hs phaseEnd (by simp)
    by_cases hz:cv tr t r phaseEnd=0
    · have hp:=(ProcPriorRawOrigin.step hL hr hs hap (Or.inr hz)).1
      omega
    · omega
  have hi:=increment hL hr hs ha hhash hend
  have hbound:=bound hL hr0 hs hap
  omega

theorem strict_first (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hh:tr.height t≤2013265921) {a b:Nat} (hab:a<b) (hb:b<tr.height t)
    (hsa:cv tr t a (ProcPriorVertical4Linear.stage 2)=1)
    (hsb:cv tr t b (ProcPriorVertical4Linear.stage 2)=1) (hf:cv tr t b first=1) :
    cv tr t a tau<cv tr t b tau := by
  obtain ⟨r,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega :b≠0)
  have hsp:=ProcPriorStageOrder.raw_interval hL (show a≤r by omega) (show r≤r+1 by omega) hb hsa hsb
  have ha:cv tr t (r+1) act=1:=(ProcPriorRawPhase.first_header hL hb hsb hf).2.1
  have hap:=ProcPriorRawBackward.previous_active hL hb hsp (last_zero hL hb hsp hsb) ha
  have hmono:=monotone hL hh (show a≤r by omega) (show r<tr.height t by omega) hsa hsp hap
  have hinc:=first_increase hL hh hb hsp hsb ha hf
  change cv tr t a tau<cv tr t (r+1) tau
  omega

/-- Raw frame identity is unique by native instance number, derived from the
actual vertical order and nonwrapping tau increments, not bus uniqueness. -/
theorem first_unique (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hh:tr.height t≤2013265921) {a b:Nat} (ha:a<tr.height t) (hb:b<tr.height t)
    (hsa:cv tr t a (ProcPriorVertical4Linear.stage 2)=1)
    (hsb:cv tr t b (ProcPriorVertical4Linear.stage 2)=1)
    (hfa:cv tr t a first=1) (hfb:cv tr t b first=1)
    (he:cv tr t a tau=cv tr t b tau) :a=b := by
  rcases Nat.lt_trichotomy a b with h|h|h
  · have hh:=strict_first hL hh h hb hsa hsb hfb;omega
  · exact h
  · have hh:=strict_first hL hh h ha hsb hsa hfa;omega
end ZkFormal.NearV3.Candidates.ProcPriorRawTauUnique
