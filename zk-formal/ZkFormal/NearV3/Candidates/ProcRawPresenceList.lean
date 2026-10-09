import ZkFormal.NearV3.Candidates.ProcRawConcatTraffic
namespace ZkFormal.NearV3.Candidates.ProcRawPresenceList
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ProcRawConcatGeometry

def packet (b : NativeBlock) : List Fp :=
  [Fp.ofNat b.run.tau,ProcPriorCells.bit b.prior.isSome,Fp.ofNat b.vid]

theorem active_cell (b : NativeBlock) (i : Nat) (hi:i<blockLength b) :
    blockCell b i=(ProcRawInstancePresence.traceAt b.run.tau b.old b.vid b.prior.isSome).cell 0 i := by
  have ha:(ProcPriorRawGen.trace b.old b.vid b.prior.isSome).cell 0 i ProcPriorRawFrame.act=1 := by
    rcases ProcPriorRawSlots.coverage b.old.links.length i hi with
      ⟨g,hg,rfl,he⟩|⟨j,g,hj,hg,rfl,he⟩|⟨g,hg,rfl,he⟩
    all_goals simp [ProcPriorRawGen.trace,he,ProcPriorRawGen.cells,ProcPriorRawFrame.act]
  funext c
  unfold blockCell ProcRawConcatBoundary.stamp ProcRawInstancePresence.traceAt
  dsimp only
  split
  · rw [ha]; grind
  · rfl

theorem block_messages (b : NativeBlock) :
    (blockRows b).flatMap (fun row=>ProcRawConcatTraffic.messages row B_SPOST false)=[packet b] := by
  simp only [blockRows,List.flatMap_map]
  have he:(List.range (blockLength b)).flatMap
      (fun i=>ProcRawConcatTraffic.messages (blockCell b i) B_SPOST false)=
      (List.range (blockLength b)).flatMap (fun i=>if i=0 then [packet b] else []) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    rw [active_cell b i (List.mem_range.mp hi)]
    rw [←ProcRawConcatTraffic.row_messages _ 0 i [] B_SPOST false]
    exact ProcRawInstancePresence.row b.run.tau b.old b.vid 0 i b.prior.isSome []
  rw [he]
  exact ProcRawPresencePhysical.singleton_range _ (block_pos b) _

theorem physical (bs : List NativeBlock) (hcap:(rows bs).length≤2^22)
    (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic
      (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75) (trace bs) t r pub B_SPOST false)=
      bs.map packet := by
  rw [ProcRawConcatTraffic.physical bs hcap]
  simp only [block_messages,←List.map_eq_flatMap]

theorem count (bs : List NativeBlock) (hcap:(rows bs).length≤2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorRawFrame.interactions B_SPOST 73 B_VBYTES 74 75)
      (trace bs) t pub B_SPOST false msg=(bs.map packet).count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical bs hcap t pub)
end ZkFormal.NearV3.Candidates.ProcRawPresenceList
