import ZkFormal.NearV3.Candidates.ProcPriorStageOrder
import ZkFormal.NearV3.Candidates.ProcPriorRawOrigin
namespace ZkFormal.NearV3.Candidates.ProcPriorRawTauSteps
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem first_tau (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r ProcPriorVertical4Linear.first=1) :cv tr t r tau=0 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul .isFirst (c tau)) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c ProcPriorVertical4Linear.first) (c tau))=2013265921*q at hq
  zs hq [hf]
  have hb:=Codec.lt (tr:=tr) (t:=t) r tau
  omega

theorem first_at_zero (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:0<tr.height t) :cv tr t 0 ProcPriorVertical4Linear.first=1 := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
    (.mul .isFirst (sub (c ProcPriorVertical4Linear.first) (k 1))) (by simp [ProcPriorVertical4Linear.windows]))
  zs hq []
  change 1*((cv tr t 0 ProcPriorVertical4Linear.first:Int)-1)=2013265921*q at hq
  have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member (Table.boolC ProcPriorVertical4Linear.first)
    (by simp [ProcPriorVertical4Linear.windows]))
  omega

theorem increment (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t (r+1) act=1) (hh:cv tr t r hash=1) (he:cv tr t r phaseEnd=1) :
    cv tr t (r+1) tau=cv tr t r tau+1 ∨
      (cv tr t r tau=2013265920 ∧ cv tr t (r+1) tau=0) := by
  obtain ⟨q,hq⟩:=zdvd hL (by omega) hs (mul3 done (n act) (sub (n tau) (.add (c tau) (k 1))))
    (by simp [constraints])
  change zev (tenv tr t r pub) (mul3 done (n act) (sub (n tau) (.add (c tau) (k 1))))=2013265921*q at hq
  zs hq [mul3,done,Codec.nx hr,ha,hh,he]
  have h0:=Codec.lt (tr:=tr) (t:=t) r tau
  have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) tau
  omega

theorem next_tau (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (han:cv tr t (r+1) act=1) :
    cv tr t (r+1) tau=cv tr t r tau ∨ cv tr t (r+1) tau=cv tr t r tau+1 ∨
      (cv tr t r tau=2013265920 ∧ cv tr t (r+1) tau=0) := by
  by_cases hh:cv tr t r hash=1
  · by_cases he:cv tr t r phaseEnd=1
    · exact Or.inr (increment hL hr hs han hh he)
    · have hb:=flag hL (show r<tr.height t by omega) hs phaseEnd (by simp)
      exact Or.inl ((ProcPriorRawOrigin.step hL hr hs ha (Or.inr (by omega))).2 tau (by simp))
  · have hb:=flag hL (show r<tr.height t by omega) hs hash (by simp)
    exact Or.inl ((ProcPriorRawOrigin.step hL hr hs ha (Or.inl (by omega))).2 tau (by simp))

theorem bound (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) :cv tr t r tau≤r := by
  induction r with
  | zero=>have hz:=first_tau hL hr hs (first_at_zero hL hr);omega
  | succ r ih=>
    by_cases hf:cv tr t (r+1) ProcPriorVertical4Linear.first=1
    · have hz:=first_tau hL hr hs hf;omega
    · have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member (Table.boolC ProcPriorVertical4Linear.first)
        (by simp [ProcPriorVertical4Linear.windows]))
      have hf0:cv tr t (r+1) ProcPriorVertical4Linear.first=0:=by omega
      obtain ⟨hsp,hlp⟩:=ProcPriorRawBackward.previous_stage hL hr hs hf0
      have hap:=ProcPriorRawBackward.previous_active hL hr hsp hlp ha
      have hp:=ih (by omega) hsp hap
      have hn:=next_tau hL hr hsp hap ha
      omega

theorem last_zero (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hn:cv tr t (r+1) (ProcPriorVertical4Linear.stage 2)=1) :cv tr t r ProcPriorVertical4Linear.last=0 := by
  have hb:=hL.bool (show r<tr.height t by omega) (ProcPriorVerticalMemorySound.window_member
    (Table.boolC ProcPriorVertical4Linear.last) (by simp [ProcPriorVertical4Linear.windows]))
  by_cases hz:cv tr t r ProcPriorVertical4Linear.last=0
  · exact hz
  · have hl:cv tr t r ProcPriorVertical4Linear.last=1:=by omega
    have ha:=ProcPriorStageOrder.advance hL hr hl 2 (by decide)
    simp only [Nat.reduceAdd] at ha
    have hp:=ProcPriorStageOrder.partition hL hr
    omega
end ZkFormal.NearV3.Candidates.ProcPriorRawTauSteps
