import ZkFormal.NearV3.Candidates.ProcPriorRawPosition
namespace ZkFormal.NearV3.Candidates.ProcPriorRawRecordPosition
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

/-- Every record byte has its serialized offset, with count bounded by the
actual frame extent rather than an external well-formedness assumption. -/
theorem bytes (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) (ht:tr.height t≤2013265921)
    (k j:Nat) (hk:k<cv tr t r count) (hj:j<24) :
    let z:=r+5+24*k+j
    z<tr.height t ∧ cv tr t z (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t z act=1 ∧ cv tr t z rec=1 ∧
      cv tr t z offset=j ∧ cv tr t z record=k ∧
      cv tr t z pos=5+24*k+j ∧
      (∀x∈[tau,vid,present,count],cv tr t z x=cv tr t r x) := by
  have hp:=(ProcPriorRawPosition.header hL hr hs hf).2
  have hext:=ProcPriorRawFrameExtent.rows hL hr hs hf
  obtain ⟨hr5,hs5,_,ho5,hor5,hrec5,_,hf5⟩:=ProcPriorRawHeaderStart.next hL hr hs hf
  have hc5:=hf5 count (by simp)
  have hnz:cv tr t r count≠0:=by omega
  simp only [hnz,ite_false] at hrec5
  have hpk:=ProcPriorRawPosition.record_starts hL hr5 hs5 hrec5 ho5 hor5 (by omega) k (by omega)
  obtain ⟨hrk,hsk,hck,hok,hork,hfk⟩:=ProcPriorRawRecordSequence.starts hL hr5 hs5 hrec5 ho5 hor5 k (by omega)
  have hkind:=kinds hL hrk hsk
  have hab:=flag hL hrk hsk act (by simp)
  have hak:cv tr t (r+5+24*k) act=1:=by omega
  have he:23=4*cv tr t (r+5+24*k) hdr+23*cv tr t (r+5+24*k) rec+31*cv tr t (r+5+24*k) hash:=by omega
  obtain ⟨hrj,hsj,haj,hoj,hfj⟩:=ProcPriorRawPhase.traverse hL hrk hsk hak hok 23 he j (by omega)
  have hpos:=ProcPriorRawPosition.phase hL hrk hsk hak hok 23 he (by omega) j (by omega)
  have hord:=(ProcPriorRawRecordBoundary.record_bytes hL hrk hsk hck hok j hj).2.2.2.trans hork
  refine ⟨hrj,hsj,haj,(hfj rec (by simp)).trans hck,hoj,hord,by omega,?_⟩
  intro x hx
  exact (hfj x (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rcases hx with rfl|rfl|rfl|rfl <;> simp)).trans ((hfk x hx).trans (hf5 x hx))
/-- Complete physical coverage of a declared frame, including every byte
position and stable instance/value identity. -/
theorem frame (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) (ht:tr.height t≤2013265921)
    (j:Nat) (hj:j<37+24*cv tr t r count) :
    r+j<tr.height t ∧ cv tr t (r+j) (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t (r+j) act=1 ∧ cv tr t (r+j) pos=j ∧
      (∀x∈[tau,vid,present,count],cv tr t (r+j) x=cv tr t r x) := by
  by_cases hh:j<5
  · obtain ⟨hhdr,ha,ho⟩:=ProcPriorRawPhase.first_header hL hr hs hf
    have hk:=kinds hL hr hs
    have he:4=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash:=by omega
    obtain ⟨hrj,hsj,haj,_,hfj⟩:=ProcPriorRawPhase.traverse hL hr hs ha ho 4 he j (by omega)
    refine ⟨hrj,hsj,haj,(ProcPriorRawPosition.header hL hr hs hf).1 j (by omega),?_⟩
    intro x hx
    exact hfj x (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      rcases hx with rfl|rfl|rfl|rfl <;> simp)
  · by_cases hrec:j<5+24*cv tr t r count
    · have hdiv:(j-5)/24<cv tr t r count:=by omega
      have hmod:(j-5)%24<24:=Nat.mod_lt _ (by decide)
      have heq:r+5+24*((j-5)/24)+(j-5)%24=r+j:=by omega
      obtain ⟨hrj,hsj,haj,_,_,_,hpj,hfj⟩:=bytes hL hr hs hf ht ((j-5)/24) ((j-5)%24) hdiv hmod
      rw [heq] at hrj hsj haj hpj hfj
      exact ⟨hrj,hsj,haj,by omega,hfj⟩
    · have hhash:j-(5+24*cv tr t r count)<32:=by omega
      have heq:r+5+24*cv tr t r count+(j-(5+24*cv tr t r count))=r+j:=by omega
      obtain ⟨hrj,hsj,haj,_,_,hfj⟩:=ProcPriorRawFrameExtent.sanity_rows hL hr hs hf _ hhash
      have hpj:=ProcPriorRawPosition.sanity hL hr hs hf ht _ hhash
      rw [heq] at hrj hsj haj hfj hpj
      exact ⟨hrj,hsj,haj,by omega,hfj⟩
end ZkFormal.NearV3.Candidates.ProcPriorRawRecordPosition
