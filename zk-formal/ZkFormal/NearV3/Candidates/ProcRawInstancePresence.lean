import ZkFormal.NearV3.Candidates.ProcCodecPresencePhysical
namespace ZkFormal.NearV3.Candidates.ProcRawInstancePresence
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open NearSpec.Bandwidth ProcPriorRawGen ProcPriorRawSlots

/-- Instance stamping changes only tau; physical padding remains zero. -/
def traceAt (tauV : Nat) (st : State) (vid : Nat) (present : Bool) : Trace Fp :=
  {trace st vid present with cell:=fun t r c=>
    if c=ProcPriorRawFrame.tau then
      (trace st vid present).cell t r ProcPriorRawFrame.act * Fp.ofNat tauV
    else (trace st vid present).cell t r c}

theorem row (tauV : Nat) (st : State) (vid t r : Nat) (present : Bool) (pub : List Fp) :
    rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (traceAt tauV st vid present) t r pub B_SPOST false =
      if r=0 then [[Fp.ofNat tauV,ProcPriorCells.bit present,Fp.ofNat vid]] else [] := by
  rw [ProcCodecPresenceTraffic.raw_row]
  by_cases hr:r<length st.links.length
  · rcases coverage st.links.length r hr with ⟨g,hg,rfl,he⟩|⟨j,g,hj,hg,rfl,he⟩|⟨g,hg,rfl,he⟩
    · by_cases hz:r=0
      · subst r; simp [traceAt,trace,he,cells,ProcPriorCells.bit,ProcPriorRawFrame.first,
          ProcPriorRawFrame.tau,ProcPriorRawFrame.present,ProcPriorRawFrame.vid,
          ProcPriorRawFrame.act,isHeader,offset]
        all_goals grind
      · simp [traceAt,trace,he,cells,ProcPriorCells.bit,ProcPriorRawFrame.first,
          ProcPriorRawFrame.tau,isHeader,offset,hz]
    · simp [traceAt,trace,he,cells,ProcPriorCells.bit,ProcPriorRawFrame.first,ProcPriorRawFrame.tau,isHeader]
    · simp [traceAt,trace,he,cells,ProcPriorCells.bit,ProcPriorRawFrame.first,ProcPriorRawFrame.tau,isHeader]
  · have he:=padding st.links.length r (by omega)
    have hn:r≠0 := by unfold length at hr; omega
    simp [traceAt,trace,he,cells,ProcPriorRawFrame.first,ProcPriorRawFrame.tau,hn]

theorem physical (tauV : Nat) (st : State) (vid t : Nat) (present : Bool) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (traceAt tauV st vid present) t r pub B_SPOST false) =
      [[Fp.ofNat tauV,ProcPriorCells.bit present,Fp.ofNat vid]] := by
  simp only [row]
  exact ProcRawPresencePhysical.singleton_range _ (by decide +kernel) _

theorem count (tauV : Nat) (st : State) (vid t : Nat) (present : Bool) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (traceAt tauV st vid present) t pub B_SPOST false msg =
      [[Fp.ofNat tauV,ProcPriorCells.bit present,Fp.ofNat vid]].count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical tauV st vid t present pub)

theorem bytes_row (tauV : Nat) (st : State) (vid t r : Nat) (present : Bool) (pub : List Fp) :
    rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (traceAt tauV st vid present) t r pub B_VBYTES true =
    rowTraffic (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace st vid present) t r pub B_VBYTES true := by
  change rowTraffic (ProcPriorRawFrame.interactions ZkFormal.NearV3.Sched.B_SPOST 73 B_VBYTES 74 75)
    (traceAt tauV st vid present) t r pub B_VBYTES true =
    rowTraffic (ProcPriorRawFrame.interactions ZkFormal.NearV3.Sched.B_SPOST 73 B_VBYTES 74 75)
    (trace st vid present) t r pub B_VBYTES true
  rw [ProcPriorRawByteTraffic.row,ProcPriorRawByteTraffic.row]
  rfl

theorem bytes_count (tauV : Nat) (st : State) (vid t : Nat) (present : Bool) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (traceAt tauV st vid present) t pub B_VBYTES true msg =
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace st vid present) t pub B_VBYTES true msg := by
  rw [tableBusCount_eq,tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=((List.range (2^22)).flatMap _).count msg
  simp only [bytes_row]
end ZkFormal.NearV3.Candidates.ProcRawInstancePresence
