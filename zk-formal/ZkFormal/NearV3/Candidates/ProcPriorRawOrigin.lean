import ZkFormal.NearV3.Candidates.ProcPriorRawBackward
namespace ZkFormal.NearV3.Candidates.ProcPriorRawOrigin
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem not_done (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t (r+1) act=1) (hf:cv tr t (r+1) first=0) :
    cv tr t r hash=0 ∨ cv tr t r phaseEnd=0 := by
  have hr0:r<tr.height t:=by omega
  have bh:=flag hL hr0 hs hash (by simp)
  have be:=flag hL hr0 hs phaseEnd (by simp)
  obtain ⟨q,hq⟩:=zdvd hL hr0 hs (mul3 done (n act) (notE (n first))) (by simp [constraints])
  change zev (tenv tr t r pub) (mul3 done (n act) (notE (n first)))=2013265921*q at hq
  zs hq [mul3,done,notE,Codec.nx hr,ha,hf]
  by_cases hh:cv tr t r hash=0
  · exact Or.inl hh
  · have hh1:cv tr t r hash=1:=by omega
    rw [hh1] at hq
    exact Or.inr (by omega)

theorem step (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (hnot:cv tr t r hash=0 ∨ cv tr t r phaseEnd=0) :
    (cv tr t (r+1) pos=cv tr t r pos+1 ∨
      (cv tr t r pos=2013265920 ∧ cv tr t (r+1) pos=0)) ∧
    ∀x∈[tau,vid,present,count],cv tr t (r+1) x=cv tr t r x := by
  obtain ⟨q,hq⟩:=zdvd hL (by omega) hs (.mul nextWithin (sub (n pos) (.add (c pos) (k 1))))
    (by simp [constraints])
  change zev (tenv tr t r pub) (.mul nextWithin (sub (n pos) (.add (c pos) (k 1))))=2013265921*q at hq
  have h0:=Codec.lt (tr:=tr) (t:=t) r pos
  have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) pos
  have hp:cv tr t (r+1) pos=cv tr t r pos+1 ∨
      (cv tr t r pos=2013265920 ∧ cv tr t (r+1) pos=0):=by
    rcases hnot with hh|he
    · zs hq [nextWithin,done,ha,Codec.nx hr,hh];omega
    · zs hq [nextWithin,done,ha,Codec.nx hr,he];omega
  refine ⟨hp,?_⟩
  intro x hx
  obtain ⟨q,hq⟩:=zdvd hL (by omega) hs (.mul nextWithin (sub (n x) (c x))) (by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨x,hx,rfl⟩)
  change zev (tenv tr t r pub) (.mul nextWithin (sub (n x) (c x)))=2013265921*q at hq
  have h0:=Codec.lt (tr:=tr) (t:=t) r x
  have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) x
  rcases hnot with hh|he
  · zs hq [nextWithin,done,ha,Codec.nx hr,hh];omega
  · zs hq [nextWithin,done,ha,Codec.nx hr,he];omega

theorem first_pos (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) :cv tr t r pos=0 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (c first) (c pos)) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c first) (c pos))=2013265921*q at hq
  zs hq [hf]
  have hb:=Codec.lt (tr:=tr) (t:=t) r pos
  omega

/-- Every active physical byte belongs to a real earlier first row. Fields and
serialized position are natural, with wrap excluded by the physical height. -/
theorem origin (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hheight:tr.height t≤2013265921)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) :
    ∃f,f≤r ∧ f<tr.height t ∧ cv tr t f (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t f first=1 ∧ cv tr t f act=1 ∧ cv tr t f pos=0 ∧
      r=f+cv tr t r pos ∧
      (∀x∈[tau,vid,present,count],cv tr t r x=cv tr t f x) := by
  induction r with
  | zero=>
    have hb:=flag hL hr hs first (by simp)
    have hf:cv tr t 0 first=1:=by
      by_cases hz:cv tr t 0 first=0
      · have hh:=ProcPriorRawBackward.positive hL hr hs ha hz;omega
      · omega
    have hp:=first_pos hL hr hs hf
    exact ⟨0,by omega,hr,hs,hf,ha,hp,by omega,fun _ _=>rfl⟩
  | succ r ih=>
    try simp only [Nat.succ_eq_add_one] at *
    have hb:=flag hL hr hs first (by simp)
    by_cases hf:cv tr t (r+1) first=1
    · have hp:=first_pos hL hr hs hf
      exact ⟨r+1,by omega,hr,hs,hf,ha,hp,by omega,fun _ _=>rfl⟩
    · have hf0:cv tr t (r+1) first=0:=by omega
      obtain ⟨hsp,_,hap⟩:=ProcPriorRawBackward.previous hL hr hs ha hf0
      obtain ⟨f,hfr,hfh,hfs,hff,hfa,hfp,he,hfields⟩:=ih (by omega) hsp hap
      obtain ⟨hincr,hcarry⟩:=step hL hr hsp hap (not_done hL hr hsp ha hf0)
      have hnext:cv tr t (r+1) pos=cv tr t r pos+1:=by
        rcases hincr with h|h
        · exact h
        · omega
      refine ⟨f,by omega,hfh,hfs,hff,hfa,hfp,by omega,?_⟩
      intro x hx
      exact (hcarry x hx).trans (hfields x hx)
end ZkFormal.NearV3.Candidates.ProcPriorRawOrigin
