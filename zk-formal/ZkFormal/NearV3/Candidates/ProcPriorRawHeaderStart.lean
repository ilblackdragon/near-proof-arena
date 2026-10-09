import ZkFormal.NearV3.Candidates.ProcPriorRawRecordSequence
namespace ZkFormal.NearV3.Candidates.ProcPriorRawHeaderStart
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem next (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) :
    r+5<tr.height t ∧ cv tr t (r+5) (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t (r+5) act=1 ∧ cv tr t (r+5) offset=0 ∧ cv tr t (r+5) record=0 ∧
      cv tr t (r+5) rec=(if cv tr t r count=0 then 0 else 1) ∧
      cv tr t (r+5) hash=(if cv tr t r count=0 then 1 else 0) ∧
      (∀x∈[tau,vid,present,count],cv tr t (r+5) x=cv tr t r x) := by
  obtain ⟨hh,ha,ho⟩:=ProcPriorRawPhase.first_header hL hr hs hf
  have hk:=kinds hL hr hs
  have hhash:cv tr t r hash=0:=by omega
  have he:4=4*cv tr t r hdr+23*cv tr t r rec+31*cv tr t r hash:=by omega
  obtain ⟨hr4,hs4,ha4,_,hfields⟩:=ProcPriorRawPhase.traverse hL hr hs ha ho 4 he 4 (by decide)
  have hh4:cv tr t (r+4) hdr=1:=(hfields hdr (by simp)).trans hh
  have hcnt:cv tr t (r+4) count=cv tr t r count:=hfields count (by simp)
  have hp:=ProcPriorRawPhase.boundary_flag hL hr hs ha ho 4 he 4 (by decide)
  simp only [ite_true] at hp
  have hnext:=(ProcPriorRawTransitions.active_not_last hL hr4 hs4 ha4).2
  have hstage:=ProcPriorRawTransitions.stage_next hL hr4 hs4 ha4
  have hoff:=ProcPriorRawPhase.reset_offset hL hr4 hs4 ha4 hp
  obtain ⟨hnact,hnrec,hnhash,hnord⟩:=ProcPriorRawPhase.header_next hL hr4 hs4 hh4 hp
  have hfields':=ProcPriorRawWithin.phase_fields hL hr hs ha hhash ho 4 he
  have he0:cv tr t (r+4) empty=if cv tr t r count=0 then 1 else 0 := by
    by_cases hz:cv tr t r count=0
    · simp only [hz,ite_true]
      exact ProcPriorRawEndpoints.count_empty hL hr4 hs4 ha4 (hcnt.trans hz)
    · simp only [hz,ite_false]
      have hb:=flag hL hr4 hs4 empty (by simp)
      by_cases h1:cv tr t (r+4) empty=1
      · have hh:=ProcPriorRawEndpoints.empty_count hL hr4 hs4 ha4 h1
        omega
      · omega
  simp only [Nat.add_assoc,Nat.reduceAdd] at hnrec
  have hrec:cv tr t (r+5) rec=if cv tr t r count=0 then 0 else 1:=by split <;> split at he0 <;> omega
  exact ⟨hnext,hstage,hnact,hoff,hnord,hrec,hnhash.trans he0,hfields'⟩
end ZkFormal.NearV3.Candidates.ProcPriorRawHeaderStart
