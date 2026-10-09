import ZkFormal.NearV3.Candidates.ProcPriorRawHeaderStart
namespace ZkFormal.NearV3.Candidates.ProcPriorRawHashStart
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem start (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) :
    let z:=r+5+24*cv tr t r count
    z<tr.height t ∧ cv tr t z (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t z act=1 ∧ cv tr t z hash=1 ∧ cv tr t z offset=0 ∧
      (∀x∈[tau,vid,present,count],cv tr t z x=cv tr t r x) := by
  obtain ⟨hr5,hs5,ha5,ho5,hor5,hrec5,hhash5,hfields5⟩:=ProcPriorRawHeaderStart.next hL hr hs hf
  have hc5:=hfields5 count (by simp)
  dsimp only
  by_cases hz:cv tr t r count=0
  · simp only [hz,Nat.mul_zero,Nat.add_zero,ite_true] at *
    exact ⟨hr5,hs5,ha5,hhash5,ho5,hfields5⟩
  · simp only [hz,ite_false] at hrec5
    obtain ⟨hrk,hsk,hck,hok,hork,hfk⟩:=ProcPriorRawRecordSequence.starts hL hr5 hs5 hrec5 ho5 hor5
      (cv tr t r count-1) (by omega)
    have hh:=kinds hL hrk hsk
    have ha:=flag hL hrk hsk act (by simp)
    have hak:cv tr t (r+5+24*(cv tr t r count-1)) act=1:=by omega
    have hhk:cv tr t (r+5+24*(cv tr t r count-1)) hash=0:=by omega
    have he:23=4*cv tr t (r+5+24*(cv tr t r count-1)) hdr+
      23*cv tr t (r+5+24*(cv tr t r count-1)) rec+31*cv tr t (r+5+24*(cv tr t r count-1)) hash:=by omega
    obtain ⟨hre,hse,hae,_,hfe⟩:=ProcPriorRawPhase.traverse hL hrk hsk hak hok 23 he 23 (by decide)
    have hce:cv tr t (r+5+24*(cv tr t r count-1)+23) rec=1:=(hfe rec (by simp)).trans hck
    have hcnt:=(hfe count (by simp)).trans ((hfk count (by simp)).trans hc5)
    have horde:=(ProcPriorRawRecordBoundary.record_bytes hL hrk hsk hck hok 23 (by decide)).2.2.2.trans hork
    have hend:=ProcPriorRawRecordBoundary.record_end hL hre hse hce (by omega)
    have hp:=ProcPriorRawPhase.boundary_flag hL hrk hsk hak hok 23 he 23 (by decide)
    simp only [ite_true] at hp
    obtain ⟨hna,_,hnh,hno,_⟩:=ProcPriorRawRecordBoundary.next_record hL hre hse hce hp
    have hnr:=(ProcPriorRawTransitions.active_not_last hL hre hse hae).2
    have hns:=ProcPriorRawTransitions.stage_next hL hre hse hae
    have hnf:=ProcPriorRawWithin.phase_fields hL hrk hsk hak hhk hok 23 he
    have hrow:r+5+24*(cv tr t r count-1)+23+1=r+5+24*cv tr t r count:=by omega
    rw [hrow] at hna hnh hno hnr hns hnf
    refine ⟨hnr,hns,hna,hnh.trans hend,hno,?_⟩
    intro x hx
    exact (hnf x hx).trans ((hfk x hx).trans (hfields5 x hx))
end ZkFormal.NearV3.Candidates.ProcPriorRawHashStart
