import ZkFormal.NearV3.Candidates.ProcPriorRawWithin
namespace ZkFormal.NearV3.Candidates.ProcPriorRawRecordSequence
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

/-- Every declared record occurs in order. The count and identity are retained
from the first record; no generated rows or supplied record bound are used. -/
theorem starts (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hc:cv tr t r rec=1) (ho:cv tr t r offset=0) (hord:cv tr t r record=0)
    (k:Nat) (hk:k<cv tr t r count) :
    r+24*k<tr.height t ∧ cv tr t (r+24*k) (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t (r+24*k) rec=1 ∧ cv tr t (r+24*k) offset=0 ∧
      cv tr t (r+24*k) record=k ∧
      (∀x∈[tau,vid,present,count],cv tr t (r+24*k) x=cv tr t r x) := by
  have hcount:=Codec.lt (tr:=tr) (t:=t) r count
  induction k with
  | zero=>exact ⟨hr,hs,hc,ho,hord,fun _ _=>rfl⟩
  | succ k ih=>
    obtain ⟨hrk,hsk,hck,hok,hordk,hfields⟩:=ih (by omega)
    have hkind:=kinds hL hrk hsk
    have hab:=flag hL hrk hsk act (by simp)
    have hak:cv tr t (r+24*k) act=1:=by omega
    have hhash:cv tr t (r+24*k) hash=0:=by omega
    have hend:23=4*cv tr t (r+24*k) hdr+23*cv tr t (r+24*k) rec+31*cv tr t (r+24*k) hash:=by omega
    obtain ⟨hre,hse,hae,_,hfe⟩:=ProcPriorRawPhase.traverse hL hrk hsk hak hok 23 hend 23 (by omega)
    have hce:cv tr t (r+24*k+23) rec=1:=(hfe rec (by simp)).trans hck
    have hore:cv tr t (r+24*k+23) record=k:=
      (ProcPriorRawRecordBoundary.record_bytes hL hrk hsk hck hok 23 (by decide)).2.2.2.trans hordk
    have hcnt:cv tr t (r+24*k+23) count=cv tr t r count:=
      (hfe count (by simp)).trans (hfields count (by simp))
    have hpe:=ProcPriorRawPhase.boundary_flag hL hrk hsk hak hok 23 hend 23 (by omega)
    simp only [ite_true] at hpe
    have hreb:=flag hL hre hse recordEnd (by simp)
    have hrez:cv tr t (r+24*k+23) recordEnd=0 := by
      by_cases h1:cv tr t (r+24*k+23) recordEnd=1
      · have hlast:=ProcPriorRawRecordBoundary.last_record hL hre hse hce h1
        omega
      · omega
    have hn:=(ProcPriorRawTransitions.active_not_last hL hre hse hae).2
    have hsn:=ProcPriorRawTransitions.stage_next hL hre hse hae
    obtain ⟨_,hcn,_,hon,horn⟩:=ProcPriorRawRecordBoundary.next_record hL hre hse hce hpe
    have hfn:=ProcPriorRawWithin.phase_fields hL hrk hsk hak hhash hok 23 hend
    have heq:r+24*k+23+1=r+24*(k+1):=by omega
    rw [heq] at hn hsn hcn hon horn hfn
    refine ⟨hn,hsn,by omega,hon,by omega,?_⟩
    intro x hx
    exact (hfn x hx).trans (hfields x hx)

/-- Every declared record consumes24 physical rows, so an arbitrary satisfying
trace itself bounds the count, independently of byte-range assumptions. -/
theorem rows (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hc:cv tr t r rec=1) (ho:cv tr t r offset=0) (hord:cv tr t r record=0) :
    r+24*cv tr t r count≤tr.height t := by
  by_cases hz:cv tr t r count=0
  · omega
  · have hn:0<cv tr t r count:=by omega
    obtain ⟨hrk,hsk,hck,hok,_,_⟩:=starts hL hr hs hc ho hord (cv tr t r count-1) (by omega)
    have hb:=ProcPriorRawRecordBoundary.record_bytes hL hrk hsk hck hok 23 (by decide)
    omega

theorem bytes (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hc:cv tr t r rec=1) (ho:cv tr t r offset=0) (hord:cv tr t r record=0)
    (k j:Nat) (hk:k<cv tr t r count) (hj:j<24) :
    r+24*k+j<tr.height t ∧ cv tr t (r+24*k+j) rec=1 ∧
      cv tr t (r+24*k+j) offset=j ∧ cv tr t (r+24*k+j) record=k := by
  obtain ⟨hrk,hsk,hck,hok,hordk,_⟩:=starts hL hr hs hc ho hord k hk
  obtain ⟨hrj,hcj,hoj,horj⟩:=ProcPriorRawRecordBoundary.record_bytes hL hrk hsk hck hok j hj
  exact ⟨hrj,hcj,hoj,horj.trans hordk⟩
end ZkFormal.NearV3.Candidates.ProcPriorRawRecordSequence
