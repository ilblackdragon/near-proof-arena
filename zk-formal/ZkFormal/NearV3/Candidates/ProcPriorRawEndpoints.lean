import ZkFormal.NearV3.Candidates.ProcPriorRawSound
namespace ZkFormal.NearV3.Candidates.ProcPriorRawEndpoints
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

/-- Phase endpoint flags in an arbitrary installed RawFrame are exact,
not hints supplied by an honest trace generator. -/
theorem phase_end (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (he:cv tr t r phaseEnd=1) :
    cv tr t r offset=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (c act) (.mul (sub (c offset) endAt) (c phaseEnd)))
    (by simp [constraints,isZero])
  change zev (tenv tr t r pub) (.mul (c act) (.mul (sub (c offset) endAt) (c phaseEnd)))=2013265921*q at hq
  zs hq [endAt,ha,he]
  have hh:=flag hL hr hs hdr (by simp)
  have hc:=flag hL hr hs rec (by simp)
  have hh':=flag hL hr hs hash (by simp)
  have hk:=kinds hL hr hs
  have ho:=Codec.lt (tr:=tr) (t:=t) r offset
  omega

theorem empty_count (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (he:cv tr t r empty=1) :cv tr t r count=0 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (c act) (.mul (c count) (c empty)))
    (by simp [constraints,isZero])
  change zev (tenv tr t r pub) (.mul (c act) (.mul (c count) (c empty)))=2013265921*q at hq
  zs hq [ha,he]
  have hc:=Codec.lt (tr:=tr) (t:=t) r count
  omega

theorem first_offset (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hh:cv tr t r hdr=1) (hf:cv tr t r first=1) :cv tr t r offset=0 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (c hdr) (.mul (c offset) (c first)))
    (by simp [constraints,isZero])
  change zev (tenv tr t r pub) (.mul (c hdr) (.mul (c offset) (c first)))=2013265921*q at hq
  zs hq [hh,hf]
  have hc:=Codec.lt (tr:=tr) (t:=t) r offset
  omega

theorem count_empty (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (hc:cv tr t r count=0) :cv tr t r empty=1 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs
    (.mul (c act) (sub (.mul (c count) (c emptyInv)) (notE (c empty))))
    (by simp [constraints,isZero])
  change zev (tenv tr t r pub)
    (.mul (c act) (sub (.mul (c count) (c emptyInv)) (notE (c empty))))=2013265921*q at hq
  zs hq [notE,ha,hc]
  have he:=flag hL hr hs empty (by simp)
  omega

theorem offset_first (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hh:cv tr t r hdr=1) (ho:cv tr t r offset=0) :cv tr t r first=1 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs
    (.mul (c hdr) (sub (.mul (c offset) (c firstInv)) (notE (c first))))
    (by simp [constraints,isZero])
  change zev (tenv tr t r pub)
    (.mul (c hdr) (sub (.mul (c offset) (c firstInv)) (notE (c first))))=2013265921*q at hq
  zs hq [notE,hh,ho]
  have hf:=flag hL hr hs first (by simp)
  omega

theorem first_fields (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) :
    cv tr t r pos=0 ∧ cv tr t r byte=0 ∧ cv tr t r record=0 ∧
      cv tr t r acc=cv tr t r count := by
  have zero (x:Nat) (hx:x=pos∨x=byte∨x=record):cv tr t r x=0 := by
    obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (c first) (c x))
      (by rcases hx with rfl|rfl|rfl <;> simp [constraints])
    change zev (tenv tr t r pub) (.mul (c first) (c x))=2013265921*q at hq
    zs hq [hf]
    have hx:=Codec.lt (tr:=tr) (t:=t) r x
    omega
  refine ⟨zero pos (by simp),zero byte (by simp),zero record (by simp),?_⟩
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (c first) (sub (c acc) (c count)))
    (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c first) (sub (c acc) (c count)))=2013265921*q at hq
  zs hq [hf]
  have ha:=Codec.lt (tr:=tr) (t:=t) r acc
  have hc:=Codec.lt (tr:=tr) (t:=t) r count
  omega
end ZkFormal.NearV3.Candidates.ProcPriorRawEndpoints
