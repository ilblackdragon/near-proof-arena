import ZkFormal.NearV3.Candidates.ProcPriorRawRecordPosition
import ZkFormal.NearV3.Candidates.ProcPriorRecordOrdinal
namespace ZkFormal.NearV3.Candidates.ProcPriorRawBackward
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem previous_stage (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t (r+1) (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t (r+1) ProcPriorVertical4Linear.first=0) :
    cv tr t r (ProcPriorVertical4Linear.stage 2)=1 ∧ cv tr t r ProcPriorVertical4Linear.last=0 := by
  have hr0:r<tr.height t := by omega
  have hb:=hL.bool hr0 (ProcPriorVerticalMemorySound.window_member
    (Table.boolC ProcPriorVertical4Linear.last) (by simp [ProcPriorVertical4Linear.windows]))
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr0 (ProcPriorVerticalMemorySound.window_member
    (.mul .isTransition (sub (n ProcPriorVertical4Linear.first) (c ProcPriorVertical4Linear.last)))
    (by simp [ProcPriorVertical4Linear.windows]))
  zs hq [Codec.nx hr,hf]
  simp only [zev,Mem.tenv_last_zero hr] at hq
  have hl:cv tr t r ProcPriorVertical4Linear.last=0 := by omega
  obtain ⟨q,he⟩:=Mem.zdvd hL hr0 (ProcPriorVerticalMemorySound.window_member
    (.mul (.mul .isTransition (sub (k 1) (c ProcPriorVertical4Linear.last)))
      (sub (n (ProcPriorVertical4Linear.stage 2)) (c (ProcPriorVertical4Linear.stage 2)))) (by
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨2,by simp,rfl⟩))
  zs he [Codec.nx hr,hl,hs]
  simp only [zev,Mem.tenv_last_zero hr] at he
  have hb3:=hL.bool hr0 (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 2)) (by simp [ProcPriorVertical4Linear.windows]))
  exact ⟨by omega,hl⟩

theorem previous_active (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hl:cv tr t r ProcPriorVertical4Linear.last=0) (ha:cv tr t (r+1) act=1) :
    cv tr t r act=1 := by
  obtain ⟨q,hq⟩:=zdvd hL (show r<tr.height t by omega) hs
    (.mul (.mul .isTransition (notE (c act))) (n act)) (by simp [constraints,mul3])
  change zev (tenv tr t r pub) (.mul (.mul (notE (c ProcPriorVertical4Linear.last)) (notE (c act))) (n act))=2013265921*q at hq
  zs hq [notE,hl,Codec.nx hr,ha]
  have hb:=ProcPriorRawSound.flag hL (show r<tr.height t by omega) hs act (by simp)
  omega


theorem virtual_first (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (hf:cv tr t r ProcPriorVertical4Linear.first=1) :
    cv tr t r first=1 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul .isFirst (sub (c act) (c first))) (by simp [constraints,mul3])
  change zev (tenv tr t r pub) (.mul (c ProcPriorVertical4Linear.first) (sub (c act) (c first)))=2013265921*q at hq
  zs hq [ha,hf]
  have hb:=flag hL hr hs first (by simp)
  omega

theorem positive (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (hf:cv tr t r first=0) :0<r := by
  by_cases hz:r=0
  · subst r
    obtain ⟨q,hq⟩:=Mem.zdvd hL hr (ProcPriorVerticalMemorySound.window_member
      (.mul .isFirst (sub (c ProcPriorVertical4Linear.first) (k 1))) (by simp [ProcPriorVertical4Linear.windows]))
    change zev (tenv tr t 0 pub) (.mul .isFirst (sub (c ProcPriorVertical4Linear.first) (k 1)))=2013265921*q at hq
    zs hq []
    change 1*((cv tr t 0 ProcPriorVertical4Linear.first:Int)-1)=2013265921*q at hq
    have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member (Table.boolC ProcPriorVertical4Linear.first)
      (by simp [ProcPriorVertical4Linear.windows]))
    have hfirst:cv tr t 0 ProcPriorVertical4Linear.first=1:=by omega
    have h:=virtual_first hL hr hs ha hfirst
    omega
  · omega

theorem previous (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r+1<tr.height t) (hs:cv tr t (r+1) (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t (r+1) act=1) (hf:cv tr t (r+1) first=0) :
    cv tr t r (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t r ProcPriorVertical4Linear.last=0 ∧ cv tr t r act=1 := by
  have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member (Table.boolC ProcPriorVertical4Linear.first)
    (by simp [ProcPriorVertical4Linear.windows]))
  have hfirst:cv tr t (r+1) ProcPriorVertical4Linear.first=0:=by
    by_cases he:cv tr t (r+1) ProcPriorVertical4Linear.first=1
    · have h:=virtual_first hL hr hs ha he;omega
    · omega
  obtain ⟨hsp,hlp⟩:=previous_stage hL hr hs hfirst
  exact ⟨hsp,hlp,previous_active hL hr hsp hlp ha⟩
end ZkFormal.NearV3.Candidates.ProcPriorRawBackward
