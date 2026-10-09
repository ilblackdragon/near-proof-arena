import ZkFormal.NearV3.Candidates.ProcPriorRawTransitions
namespace ZkFormal.NearV3.Candidates.ProcPriorRawPhase
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem endpoint (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1)
    (ho:cv tr t r offset=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash) :
    cv tr t r phaseEnd=1 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs
    (.mul (c act) (sub (.mul (sub (c offset) endAt) (c endInv)) (notE (c phaseEnd))))
    (by simp [constraints,isZero])
  change zev (tenv tr t r pub)
    (.mul (c act) (sub (.mul (sub (c offset) endAt) (c endInv)) (notE (c phaseEnd))))=2013265921*q at hq
  zs hq [endAt,notE,ha,ho]
  have he:=flag hL hr hs phaseEnd (by simp)
  omega

/-- A phase beginning at offset zero traverses every canonical byte position
without field wrap, preserving its identity and phase. -/
theorem traverse (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (ho:cv tr t r offset=0)
    (e:Nat) (he:e=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash)
    (j:Nat) (hj:j≤e) :
    r+j<tr.height t ∧ cv tr t (r+j) (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t (r+j) act=1 ∧ cv tr t (r+j) offset=j ∧
      (∀x∈[tau,vid,present,count,hdr,rec,hash],cv tr t (r+j) x=cv tr t r x) := by
  have hh:=flag hL hr hs hdr (by simp)
  have hc:=flag hL hr hs rec (by simp)
  have hh':=flag hL hr hs hash (by simp)
  have hk:=kinds hL hr hs
  have heb:e≤31:=by omega
  induction j with
  | zero=>exact ⟨hr,hs,ha,ho,fun _ _=>rfl⟩
  | succ j ih=>
    obtain ⟨hrj,hsj,haj,hoj,hfields⟩:=ih (by omega)
    have hhdr:=hfields hdr (by simp)
    have hrec:=hfields rec (by simp)
    have hhash:=hfields hash (by simp)
    have hjflag:=flag hL hrj hsj phaseEnd (by simp)
    have hzero:cv tr t (r+j) phaseEnd=0 := by
      by_cases hf:cv tr t (r+j) phaseEnd=1
      · have hend:=ProcPriorRawEndpoints.phase_end hL hrj hsj haj hf
        omega
      · omega
    obtain ⟨_,hn⟩:=ProcPriorRawTransitions.active_not_last hL hrj hsj haj
    have hsn:=ProcPriorRawTransitions.stage_next hL hrj hsj haj
    obtain ⟨han,hfn⟩:=ProcPriorRawTransitions.interior hL hrj hsj haj hzero
    have hincr:=ProcPriorRawTransitions.interior_increment hL hrj hsj haj hzero offset (Or.inr rfl)
    have hon:cv tr t (r+j+1) offset=j+1:=by omega
    have hfn':∀x∈[tau,vid,present,count,hdr,rec,hash],cv tr t (r+j+1) x=cv tr t r x :=
      fun x hx=>(hfn x hx).trans (hfields x hx)
    exact ⟨hn,hsn,han,hon,hfn'⟩

theorem boundary_flag (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (ho:cv tr t r offset=0)
    (e:Nat) (he:e=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash)
    (j:Nat) (hj:j≤e) :cv tr t (r+j) phaseEnd=if j=e then 1 else 0 := by
  obtain ⟨hrj,hsj,haj,hoj,hfields⟩:=traverse hL hr hs ha ho e he j hj
  have hhdr:=hfields hdr (by simp)
  have hrec:=hfields rec (by simp)
  have hhash:=hfields hash (by simp)
  by_cases hje:j=e
  · simp only [hje,ite_true]
    subst j
    exact endpoint hL hrj hsj haj (by omega)
  · simp only [hje,ite_false]
    have hb:=flag hL hrj hsj phaseEnd (by simp)
    by_cases hf:cv tr t (r+j) phaseEnd=1
    · have hend:=ProcPriorRawEndpoints.phase_end hL hrj hsj haj hf
      omega
    · omega

theorem reset_offset (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (he:cv tr t r phaseEnd=1) :cv tr t (r+1) offset=0 := by
  have hn:=(ProcPriorRawTransitions.active_not_last hL hr hs ha).2
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (c phaseEnd) (n offset)) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul (c phaseEnd) (n offset))=2013265921*q at hq
  zs hq [he,Codec.nx hn]
  have hb:=Codec.lt (tr:=tr) (t:=t) (r+1) offset
  omega

/-- The header boundary selects exactly the record or sanity phase according
to the constrained empty flag and resets the record ordinal. -/
theorem header_next (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hh:cv tr t r hdr=1) (he:cv tr t r phaseEnd=1) :
    cv tr t (r+1) act=1 ∧ cv tr t (r+1) rec+cv tr t r empty=1 ∧
      cv tr t (r+1) hash=cv tr t r empty ∧ cv tr t (r+1) record=0 := by
  have hk:=kinds hL hr hs
  have hb:=flag hL hr hs act (by simp)
  have ha:cv tr t r act=1:=by omega
  have hhash:cv tr t r hash=0:=by omega
  have hn:=(ProcPriorRawTransitions.active_not_last hL hr hs ha).2
  have hsn:=ProcPriorRawTransitions.stage_next hL hr hs ha
  have hbn:=flag hL hn hsn act (by simp)
  have hrec:=flag hL hn hsn rec (by simp)
  have hhn:=flag hL hn hsn hash (by simp)
  have hempty:=flag hL hr hs empty (by simp)
  have hrecord:=Codec.lt (tr:=tr) (t:=t) (r+1) record
  obtain ⟨q0,h0⟩:=zdvd hL hr hs (.mul nextWithin (notE (n act))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul nextWithin (notE (n act)))=2013265921*q0 at h0
  zs h0 [nextWithin,done,notE,ha,hhash,Codec.nx hn]
  obtain ⟨q1,h1⟩:=zdvd hL hr hs (mul3 (c hdr) (c phaseEnd) (sub (n rec) (notE (c empty)))) (by simp [constraints])
  change zev (tenv tr t r pub) (mul3 (c hdr) (c phaseEnd) (sub (n rec) (notE (c empty))))=2013265921*q1 at h1
  zs h1 [mul3,notE,hh,he,Codec.nx hn]
  obtain ⟨q2,h2⟩:=zdvd hL hr hs (mul3 (c hdr) (c phaseEnd) (sub (n hash) (c empty))) (by simp [constraints])
  change zev (tenv tr t r pub) (mul3 (c hdr) (c phaseEnd) (sub (n hash) (c empty)))=2013265921*q2 at h2
  zs h2 [mul3,hh,he,Codec.nx hn]
  obtain ⟨q3,h3⟩:=zdvd hL hr hs (mul3 (c hdr) (c phaseEnd) (n record)) (by simp [constraints])
  change zev (tenv tr t r pub) (mul3 (c hdr) (c phaseEnd) (n record))=2013265921*q3 at h3
  zs h3 [mul3,hh,he,Codec.nx hn]
  omega

theorem first_header (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) :
    cv tr t r hdr=1 ∧ cv tr t r act=1 ∧ cv tr t r offset=0 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul (notE (c hdr)) (c first)) (by simp [constraints,isZero])
  change zev (tenv tr t r pub) (.mul (notE (c hdr)) (c first))=2013265921*q at hq
  zs hq [notE,hf]
  have hb:=flag hL hr hs hdr (by simp)
  have hh:cv tr t r hdr=1:=by omega
  have hk:=kinds hL hr hs
  have ha:=flag hL hr hs act (by simp)
  exact ⟨hh,by omega,ProcPriorRawEndpoints.first_offset hL hr hs hh hf⟩
end ZkFormal.NearV3.Candidates.ProcPriorRawPhase
