import ZkFormal.NearV3.Candidates.ProcPriorRawFrameExtent
namespace ZkFormal.NearV3.Candidates.ProcPriorRawPosition
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

/-- Position advances across header/record boundaries too; field wrap is explicit. -/
theorem next (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (hd:cv tr t r hash=0 ∨ cv tr t r phaseEnd=0) :
    cv tr t (r+1) pos=cv tr t r pos+1 ∨
      (cv tr t r pos=2013265920 ∧ cv tr t (r+1) pos=0) := by
  have hn:=(ProcPriorRawTransitions.active_not_last hL hr hs ha).2
  obtain ⟨q,hq⟩:=zdvd hL hr hs (.mul nextWithin (sub (n pos) (.add (c pos) (k 1))))
    (by simp [constraints])
  change zev (tenv tr t r pub) (.mul nextWithin (sub (n pos) (.add (c pos) (k 1))))=2013265921*q at hq
  have h0:=Codec.lt (tr:=tr) (t:=t) r pos
  have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) pos
  rcases hd with hd|hd <;> zs hq [nextWithin,done,ha,hd,Codec.nx hn] <;> omega

/-- A natural position bound excludes field wrap throughout a phase. -/
theorem phase (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (ho:cv tr t r offset=0)
    (e:Nat) (he:e=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash)
    (hb:cv tr t r pos+e<2013265921) (j:Nat) (hj:j≤e) :
    cv tr t (r+j) pos=cv tr t r pos+j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp:=ih (by omega)
    obtain ⟨hrj,hsj,haj,_,_⟩:=ProcPriorRawPhase.traverse hL hr hs ha ho e he j (by omega)
    have hend:=ProcPriorRawPhase.boundary_flag hL hr hs ha ho e he j (by omega)
    have hne:j≠e:=by omega
    simp only [hne,ite_false] at hend
    have hn:=next hL hrj hsj haj (Or.inr hend)
    simp only [Nat.add_succ, Nat.add_zero] at *
    omega

/-- The first byte of the next phase has the consecutive natural position. -/
theorem boundary (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv tr t r act=1) (hh:cv tr t r hash=0) (ho:cv tr t r offset=0)
    (e:Nat) (he:e=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash)
    (hb:cv tr t r pos+e+1<2013265921) :
    cv tr t (r+e+1) pos=cv tr t r pos+e+1 := by
  have hp:=phase hL hr hs ha ho e he (by omega) e (by omega)
  obtain ⟨hre,hse,hae,_,hfe⟩:=ProcPriorRawPhase.traverse hL hr hs ha ho e he e (by omega)
  have hn:=next hL hre hse hae (Or.inl ((hfe hash (by simp)).trans hh))
  omega
theorem header (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) :
    (∀j≤4,cv tr t (r+j) pos=j) ∧ cv tr t (r+5) pos=5 := by
  obtain ⟨hh,ha,ho⟩:=ProcPriorRawPhase.first_header hL hr hs hf
  have hk:=kinds hL hr hs
  have hz:cv tr t r hash=0:=by omega
  have he:4=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash:=by omega
  have hp:=(ProcPriorRawEndpoints.first_fields hL hr hs hf).1
  constructor
  · intro j hj
    have hjp:=phase hL hr hs ha ho 4 he (by omega) j hj
    omega
  · have hbp:=boundary hL hr hs ha hz ho 4 he (by omega)
    simpa only [Nat.reduceAdd, Nat.add_assoc, hp, Nat.zero_add] using hbp

/-- All record positions are natural offsets when the entire record interval
fits below the field modulus. This bound can come from the physical extent. -/
theorem record_starts (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hc:cv tr t r rec=1) (ho:cv tr t r offset=0) (hord:cv tr t r record=0)
    (hb:cv tr t r pos+24*cv tr t r count<2013265921)
    (k:Nat) (hk:k≤cv tr t r count) :
    cv tr t (r+24*k) pos=cv tr t r pos+24*k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp:=ih (by omega)
    obtain ⟨hrk,hsk,hck,hok,_,_⟩:=ProcPriorRawRecordSequence.starts hL hr hs hc ho hord k (by omega)
    have hkinds:=kinds hL hrk hsk
    have hab:=flag hL hrk hsk act (by simp)
    have hak:cv tr t (r+24*k) act=1:=by omega
    have hhash:cv tr t (r+24*k) hash=0:=by omega
    have he:23=4*cv tr t (r+24*k) hdr+23*cv tr t (r+24*k) rec+31*cv tr t (r+24*k) hash:=by omega
    have hn:=boundary hL hrk hsk hak hhash hok 23 he (by omega)
    have hrow:r+24*k+23+1=r+24*(k+1):=by omega
    rw [hrow] at hn
    omega
theorem hash_start (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) (ht:tr.height t≤2013265921) :
    cv tr t (r+5+24*cv tr t r count) pos=5+24*cv tr t r count := by
  have hp:=(header hL hr hs hf).2
  have hext:=ProcPriorRawFrameExtent.rows hL hr hs hf
  obtain ⟨hr5,hs5,_,ho5,hor5,hrec5,_,hf5⟩:=ProcPriorRawHeaderStart.next hL hr hs hf
  have hc5:=hf5 count (by simp)
  by_cases hz:cv tr t r count=0
  · simpa only [hz,Nat.mul_zero,Nat.add_zero] using hp
  · simp only [hz,ite_false] at hrec5
    have hn:=record_starts hL hr5 hs5 hrec5 ho5 hor5 (by omega) (cv tr t r count) (by omega)
    omega

theorem sanity (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) (ht:tr.height t≤2013265921)
    (j:Nat) (hj:j<32) :
    cv tr t (r+5+24*cv tr t r count+j) pos=5+24*cv tr t r count+j := by
  have hp:=hash_start hL hr hs hf ht
  have hext:=ProcPriorRawFrameExtent.rows hL hr hs hf
  obtain ⟨hz,hsz,haz,hhz,hoz,_⟩:=ProcPriorRawHashStart.start hL hr hs hf
  have hk:=kinds hL hz hsz
  have he:31=4*cv tr t (r+5+24*cv tr t r count) hdr+
      23*cv tr t (r+5+24*cv tr t r count) rec+31*cv tr t (r+5+24*cv tr t r count) hash:=by omega
  have hn:=phase hL hz hsz haz hoz 31 he (by omega) j (by omega)
  omega
end ZkFormal.NearV3.Candidates.ProcPriorRawPosition
