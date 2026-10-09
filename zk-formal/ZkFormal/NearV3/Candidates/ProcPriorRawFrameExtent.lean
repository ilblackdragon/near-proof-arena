import ZkFormal.NearV3.Candidates.ProcPriorRawHashStart
namespace ZkFormal.NearV3.Candidates.ProcPriorRawFrameExtent
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRawFrame ProcPriorRawSound
variable {tr:Trace Fp} {t r:Nat} {pub:List Fp}

theorem sanity_rows (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) (j:Nat) (hj:j<32) :
    let z:=r+5+24*cv tr t r count+j
    z<tr.height t ∧ cv tr t z (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv tr t z act=1 ∧ cv tr t z hash=1 ∧ cv tr t z offset=j ∧
      (∀x∈[tau,vid,present,count],cv tr t z x=cv tr t r x) := by
  obtain ⟨hz,hsz,haz,hhz,hoz,hfz⟩:=ProcPriorRawHashStart.start hL hr hs hf
  have hk:=kinds hL hz hsz
  have he:31=4*cv tr t (r+5+24*cv tr t r count) hdr+
      23*cv tr t (r+5+24*cv tr t r count) rec+
      31*cv tr t (r+5+24*cv tr t r count) hash:=by omega
  obtain ⟨hrj,hsj,haj,hoj,hfj⟩:=ProcPriorRawPhase.traverse hL hz hsz haz hoz 31 he j (by omega)
  refine ⟨hrj,hsj,haj,(hfj hash (by simp)).trans hhz,hoj,?_⟩
  intro x hx
  exact (hfj x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h|h|h|h <;> simp [h])).trans (hfz x hx)

theorem rows (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv tr t r first=1) :
    r+37+24*cv tr t r count ≤ tr.height t := by
  have h:=(sanity_rows hL hr hs hf 31 (by decide)).1
  omega
end ZkFormal.NearV3.Candidates.ProcPriorRawFrameExtent
