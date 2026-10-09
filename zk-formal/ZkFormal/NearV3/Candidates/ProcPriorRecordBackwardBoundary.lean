import ZkFormal.NearV3.Candidates.ProcPriorRecordWordTraversal
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordBackwardBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem not_first (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1) :
    cv tr t r ProcPriorVertical4Linear.first=0 := by
  obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr hs (.mul .isFirst (sub (c act) (header false))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c ProcPriorVertical4Linear.first) (sub (c act) (header false)))=2013265921*q at hq
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int):=rfl
  zs hq [header,words,cur]
  have hwi:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=1:=by omega
  have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member (Table.boolC ProcPriorVertical4Linear.first)
    (by simp [ProcPriorVertical4Linear.windows]))
  have he:(cv tr t r act:Int)-((cv tr t r act:Int)-
    ((cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)))=1:=by omega
  rw [he] at hq
  omega

theorem positive (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1) :0<r := by
  have hf:=not_first hL hr hs hw
  by_cases hz:r=0
  · subst r
    obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
      (.mul .isFirst (sub (c ProcPriorVertical4Linear.first) (k 1))) (by simp [ProcPriorVertical4Linear.windows]))
    change zev (tenv tr t 0 pub) (.mul .isFirst (sub (c ProcPriorVertical4Linear.first) (k 1)))=2013265921*q at hq
    zs hq [hf]
    change 1*(0-1: Int)=2013265921*q at hq
    omega
  · omega

/-- Every live word row has a real previous row in the same active Record
stage; a stage boundary/header cannot be mistaken for a limb predecessor. -/
theorem previous (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1) :
    ∃p,r=p+1 ∧ p<tr.height t ∧ cv tr t p (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv tr t p ProcPriorVertical4Linear.last=0 ∧ cv tr t p act=1 := by
  have hp:=positive hL hr hs hw
  have hf:=not_first hL hr hs hw
  obtain ⟨p,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega :r≠0)
  simp only [Nat.succ_eq_add_one] at *
  obtain ⟨hsp,hlp⟩:=ProcPriorRecordOrdinal.previous_stage hL hr hs hf
  have ha:cv tr t (p+1) act=1:=by
    have hb:=ProcPriorRecordGeometry.words_bound hL hr hs
    have hc:=ProcPriorRecordSound.flag hL hr hs act (by simp)
    omega
  exact ⟨p,rfl,by omega,hsp,hlp,ProcPriorRecordOrdinal.previous_active hL hr hsp hlp ha⟩
theorem after_header (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv tr t r act=1)
    (hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=0)
    (hwn:cv tr t (r+1) sender+cv tr t (r+1) receiver+cv tr t (r+1) amount=1) :
    cv tr t (r+1) firstLimb=1 := by
  obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL (by omega) hs
    (.mul (.mul (header false) (words true)) (sub (n firstLimb) (k 1))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (.mul (header false) (words true)) (sub (n firstLimb) (k 1)))=2013265921*q at hq
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int):=rfl
  have nex (x:Nat):zev (tenv tr t r pub) (.col x true)=(cv tr t (r+1) x:Int):=by
    change zev (tenv tr t r pub) (n x)=_
    simp only [zev_n,Codec.nx hr]
  zs hq [header,words,cur,nex,ha,Codec.nx hr]
  have hwi:(cv tr t r sender:Int)+(cv tr t r receiver:Int)+(cv tr t r amount:Int)=0:=by omega
  have hwni:(cv tr t (r+1) sender:Int)+(cv tr t (r+1) receiver:Int)+(cv tr t (r+1) amount:Int)=1:=by omega
  rw [hwi,hwni] at hq
  have hb:=Codec.lt (tr:=tr) (t:=t) (r+1) firstLimb
  omega
theorem after_top (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ht:cv tr t r topLimb=1)
    (hwn:cv tr t (r+1) sender+cv tr t (r+1) receiver+cv tr t (r+1) amount=1) :
    cv tr t (r+1) firstLimb=1 := by
  have hr0:r<tr.height t:=by omega
  have hb:=ProcPriorRecordGeometry.words_bound hL hr0 hs
  have hl:=ProcPriorRecordGeometry.limbs_eq hL hr0 hs
  have ha:=ProcPriorRecordSound.flag hL hr0 hs act (by simp)
  have ham:=ProcPriorRecordSound.flag hL hr0 hs amount (by simp)
  have hw:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1:=by omega
  have cur (x:Nat):zev (tenv tr t r pub) (.col x false)=(cv tr t r x:Int):=rfl
  have nex (x:Nat):zev (tenv tr t r pub) (.col x true)=(cv tr t (r+1) x:Int):=by
    change zev (tenv tr t r pub) (n x)=_
    simp only [zev_n,Codec.nx hr]
  have hn:=Codec.lt (tr:=tr) (t:=t) (r+1) firstLimb
  by_cases ham1:cv tr t r amount=1
  · obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr0 hs
      (.mul (.mul (.mul (c amount) (c topLimb)) (words true)) (sub (n firstLimb) (k 1))) (by simp [constraints])
    change zev (tenv tr t r pub) (.mul (.mul (.mul (c amount) (c topLimb)) (words true)) (sub (n firstLimb) (k 1)))=2013265921*q at hq
    zs hq [words,cur,nex,ht,ham1,Codec.nx hr]
    have hwni:(cv tr t (r+1) sender:Int)+(cv tr t (r+1) receiver:Int)+(cv tr t (r+1) amount:Int)=1:=by omega
    rw [hwni] at hq
    omega
  · obtain ⟨q,hq⟩:=ProcPriorRecordOrdinal.zdvd hL hr0 hs
      (.mul (.mul (.add (c sender) (c receiver)) (c topLimb)) (sub (n firstLimb) (k 1))) (by simp [constraints])
    change zev (tenv tr t r pub) (.mul (.mul (.add (c sender) (c receiver)) (c topLimb)) (sub (n firstLimb) (k 1)))=2013265921*q at hq
    zs hq [ht,Codec.nx hr]
    have hwi:(cv tr t r sender:Int)+(cv tr t r receiver:Int)=1:=by omega
    rw [hwi] at hq
    omega
theorem predecessor_limb (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (g g':Nat) (hgg:(g=midLimb ∧ g'=firstLimb) ∨ (g=topLimb ∧ g'=midLimb))
    (hg:cv tr t r g=1) :
    ∃p,r=p+1 ∧ p<tr.height t ∧ cv tr t p (ProcPriorVertical4Linear.stage 3)=1 ∧ cv tr t p g'=1 := by
  have hl:=ProcPriorRecordGeometry.limbs_eq hL hr hs
  have hw:=ProcPriorRecordGeometry.words_bound hL hr hs
  have ha:=ProcPriorRecordSound.flag hL hr hs act (by simp)
  have hwn:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1:=by
    rcases hgg with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
  have hfn:cv tr t r firstLimb=0:=by
    rcases hgg with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
  obtain ⟨p,heq,hp,hsp,_,hap⟩:=previous hL hr hs hwn
  subst r
  have hwp:=ProcPriorRecordGeometry.words_bound hL hp hsp
  have hlp:=ProcPriorRecordGeometry.limbs_eq hL hp hsp
  have hwp1:cv tr t p sender+cv tr t p receiver+cv tr t p amount=1:=by
    by_cases hz:cv tr t p sender+cv tr t p receiver+cv tr t p amount=0
    · have hn:=after_header hL hr hsp hap hz hwn
      omega
    · omega
  have htp:cv tr t p topLimb=0:=by
    by_cases ht1:cv tr t p topLimb=1
    · have hn:=after_top hL hr hsp ht1 hwn
      omega
    · omega
  refine ⟨p,rfl,hp,hsp,?_⟩
  rcases hgg with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · by_cases hm1:cv tr t p midLimb=1
    · have hn:=(ProcPriorRecordWordTraversal.limb_next hL hp hsp midLimb topLimb (by simp) hm1).2.2.2.1
      omega
    · omega
  · by_cases hf1:cv tr t p firstLimb=1
    · have hn:=(ProcPriorRecordWordTraversal.limb_next hL hp hsp firstLimb midLimb (by simp) hf1).2.2.2.1
      omega
    · omega

theorem top_origin (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (ht:cv tr t r topLimb=1) :
    ∃p,r=p+2 ∧ p<tr.height t ∧ cv tr t p (ProcPriorVertical4Linear.stage 3)=1 ∧ cv tr t p firstLimb=1 := by
  obtain ⟨q,heq,hq,hsq,hmq⟩:=predecessor_limb hL hr hs topLimb midLimb (by simp) ht
  obtain ⟨p,hep,hp,hsp,hfp⟩:=predecessor_limb hL hq hsq midLimb firstLimb (by simp) hmq
  exact ⟨p,by omega,hp,hsp,hfp⟩
end ZkFormal.NearV3.Candidates.ProcPriorRecordBackwardBoundary
