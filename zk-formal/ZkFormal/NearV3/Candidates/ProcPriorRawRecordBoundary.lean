import ZkFormal.NearV3.Candidates.ProcPriorRawPhase
namespace ZkFormal.NearV3.Candidates.ProcPriorRawRecordBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem last_record (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hc:cv tr t r rec=1) (he:cv tr t r recordEnd=1) :
    cv tr t r record+1=cv tr t r count ∨
      (cv tr t r record=2013265920 ∧ cv tr t r count=0) := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs
    (.mul (c rec) (.mul (sub (.add (c record) (k 1)) (c count)) (c recordEnd)))
    (by simp [constraints,isZero])
  change zev (tenv tr t r pub)
    (.mul (c rec) (.mul (sub (.add (c record) (k 1)) (c count)) (c recordEnd)))=2013265921*q at hq
  zs hq [hc,he]
  have h0:=Codec.lt (tr:=tr) (t:=t) r record
  have h1:=Codec.lt (tr:=tr) (t:=t) r count
  omega

theorem record_end (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hc:cv tr t r rec=1) (he:cv tr t r record+1=cv tr t r count) :
    cv tr t r recordEnd=1 := by
  obtain ⟨q,hq⟩:=zdvd hL hr hs
    (.mul (c rec) (sub (.mul (sub (.add (c record) (k 1)) (c count)) (c recordInv)) (notE (c recordEnd))))
    (by simp [constraints,isZero])
  change zev (tenv tr t r pub)
    (.mul (c rec) (sub (.mul (sub (.add (c record) (k 1)) (c count)) (c recordInv)) (notE (c recordEnd))))=2013265921*q at hq
  have hev:=he.symm
  zs hq [notE,hc,hev]
  have hb:=flag hL hr hs recordEnd (by simp)
  omega

theorem next_record (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hc:cv tr t r rec=1) (he:cv tr t r phaseEnd=1) :
    cv tr t (r+1) act=1 ∧ cv tr t (r+1) rec+cv tr t r recordEnd=1 ∧
      cv tr t (r+1) hash=cv tr t r recordEnd ∧ cv tr t (r+1) offset=0 ∧
      (cv tr t (r+1) record=cv tr t r record+1 ∨
        (cv tr t r record=2013265920 ∧ cv tr t (r+1) record=0)) := by
  have hk:=kinds hL hr hs
  have hb:=flag hL hr hs act (by simp)
  have ha:cv tr t r act=1:=by omega
  have hhash:cv tr t r hash=0:=by omega
  have hn:=(ProcPriorRawTransitions.active_not_last hL hr hs ha).2
  have hsn:=ProcPriorRawTransitions.stage_next hL hr hs ha
  have hbn:=flag hL hn hsn act (by simp)
  have hrec:=flag hL hn hsn rec (by simp)
  have hhn:=flag hL hn hsn hash (by simp)
  have hend:=flag hL hr hs recordEnd (by simp)
  have h0r:=Codec.lt (tr:=tr) (t:=t) r record
  have h1r:=Codec.lt (tr:=tr) (t:=t) (r+1) record
  have ho:=ProcPriorRawPhase.reset_offset hL hr hs ha he
  obtain ⟨q0,h0⟩:=zdvd hL hr hs (.mul nextWithin (notE (n act))) (by simp [constraints])
  change zev (tenv tr t r pub) (.mul nextWithin (notE (n act)))=2013265921*q0 at h0
  zs h0 [nextWithin,done,notE,ha,hhash,Codec.nx hn]
  obtain ⟨q1,h1⟩:=zdvd hL hr hs (mul3 (c rec) (c phaseEnd) (sub (n rec) (notE (c recordEnd)))) (by simp [constraints])
  change zev (tenv tr t r pub) (mul3 (c rec) (c phaseEnd) (sub (n rec) (notE (c recordEnd))))=2013265921*q1 at h1
  zs h1 [mul3,notE,hc,he,Codec.nx hn]
  obtain ⟨q2,h2⟩:=zdvd hL hr hs (mul3 (c rec) (c phaseEnd) (sub (n hash) (c recordEnd))) (by simp [constraints])
  change zev (tenv tr t r pub) (mul3 (c rec) (c phaseEnd) (sub (n hash) (c recordEnd)))=2013265921*q2 at h2
  zs h2 [mul3,hc,he,Codec.nx hn]
  obtain ⟨q3,h3⟩:=zdvd hL hr hs (mul3 (c rec) (c phaseEnd) (sub (n record) (.add (c record) (k 1)))) (by simp [constraints])
  change zev (tenv tr t r pub) (mul3 (c rec) (c phaseEnd) (sub (n record) (.add (c record) (k 1))))=2013265921*q3 at h3
  zs h3 [mul3,hc,he,Codec.nx hn]
  omega

theorem interior_record (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (he:cv tr t r phaseEnd=0) :
    cv tr t (r+1) record=cv tr t r record := by
  have hn:=(ProcPriorRawTransitions.active_not_last hL hr hs ha).2
  obtain ⟨q,hq⟩:=zdvd hL hr hs
    (.mul (sub nextWithin (.mul (c rec) (c phaseEnd))) (sub (n record) (c record)))
    (by simp [constraints])
  change zev (tenv tr t r pub)
    (.mul (sub nextWithin (.mul (c rec) (c phaseEnd))) (sub (n record) (c record)))=2013265921*q at hq
  zs hq [nextWithin,done,ha,he,Codec.nx hn]
  have h0:=Codec.lt (tr:=tr) (t:=t) r record
  have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) record
  omega

/-- Every byte in a complete record has the same record ordinal, and occupies
its canonical offset; arbitrary traces cannot splice different records. -/
theorem record_bytes (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hc:cv tr t r rec=1) (ho:cv tr t r offset=0) (j:Nat) (hj:j<24) :
    r+j<tr.height t ∧ cv tr t (r+j) rec=1 ∧ cv tr t (r+j) offset=j ∧
      cv tr t (r+j) record=cv tr t r record := by
  have hk:=kinds hL hr hs
  have hb:=flag hL hr hs act (by simp)
  have ha:cv tr t r act=1:=by omega
  have he:23=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash:=by omega
  have all (i:Nat) (hi:i<24):=ProcPriorRawPhase.traverse hL hr hs ha ho 23 he i (by omega)
  have hrecord:cv tr t (r+j) record=cv tr t r record := by
    induction j with
    | zero=>rfl
    | succ j ih=>
      obtain ⟨hrj,hsj,haj,_,_⟩:=all j (by omega)
      have hf:=ProcPriorRawPhase.boundary_flag hL hr hs ha ho 23 he j (by omega)
      have hne:j≠23:=by omega
      simp only [hne,ite_false] at hf
      exact (interior_record hL hrj hsj haj hf).trans (ih (by omega))
  obtain ⟨hrj,_,_,hoj,hf⟩:=all j hj
  exact ⟨hrj,(hf rec (by simp)).trans hc,hoj,hrecord⟩
end ZkFormal.NearV3.Candidates.ProcPriorRawRecordBoundary
