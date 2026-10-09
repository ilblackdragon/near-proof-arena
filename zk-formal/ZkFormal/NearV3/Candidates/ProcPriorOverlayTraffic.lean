import ZkFormal.NearV3.Candidates.ProcPriorOverlayRowInventory
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorVertical4Linear ProcPriorVertical4Clock ProcPriorOverlayCuts ProcPriorOverlayGeometry

def sourceTraffic (source : Nat→Trace Fp) (i bus : Nat) (sd : Bool) : List (List Fp):=
  (List.range (2^22)).flatMap (fun r=>rowTraffic
    (ProcPriorCodecActualFamily.components[i]!).interactions (source i) 0 r [] bus sd)

/-- Full physical all-bus inventory of the installed overlay. This preserves
natural multiplicities, including next-row comparator requests, and uses the
actual presence-bus-60 component inventory. -/
theorem physical (bs : List NativeBlock)
    (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧ cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (source : Nat→Trace Fp) (used : Nat→Nat)
    (hs:∀T i,(T,i)∈ProcPriorCodecActualFamily.components.zipIdx→
      (source i).log 0=22 ∧ used i<stop bs i-start bs i ∧
      ∀j,used i≤j→(source i).cell 0 j=fun _=>0)
    (t : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActualFamily.overlay.interactions
      (trace bs (fun n=>(source n).cell 0)) t r pub bus sd)=
      sourceTraffic source 0 bus sd++sourceTraffic source 1 bus sd++
      sourceTraffic source 2 bus sd++sourceTraffic source 3 bus sd := by
  let f:=fun i j=>rowTraffic (ProcPriorCodecActualFamily.components[i]!).interactions (source i) 0 j [] bus sd
  have rows:(List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActualFamily.overlay.interactions
      (trace bs (fun n=>(source n).cell 0)) t r pub bus sd)=
    (List.range (2^22)).flatMap (fun r=>if r<cutMemory bs then f 0 r
      else if r<cutIds bs then f 1 (r-cutMemory bs)
      else if r<cutRaw bs then f 2 (r-cutIds bs) else f 3 (r-cutRaw bs)):=by
    apply flatMap_congr'
    intro r hr
    rw [ProcPriorOverlayRowInventory.row bs hc source used hs r t (List.mem_range.mp hr) pub bus sd,
      ProcPriorOverlayRowInventory.select]
  rw [rows,ProcPriorOverlayTrafficRanges.four _ _ _ _ (by omega) (by omega) (by omega)]
  have full (i : Nat) (hi:i<4) : sourceTraffic source i bus sd=
      (List.range (stop bs i-start bs i)).flatMap (f i) := by
    have hg:ProcPriorCodecActualFamily.components[i]?=some (ProcPriorCodecActualFamily.components[i]!):=by
      rw [getElem!_pos ProcPriorCodecActualFamily.components i (show i<ProcPriorCodecActualFamily.components.length from hi)]
      exact List.getElem?_eq_getElem _
    have hT:=List.mem_of_getElem? hg
    obtain ⟨hl,hu,hz⟩:=hs _ i (List.mk_mem_zipIdx_iff_getElem?.mpr hg)
    have hn:stop bs i-start bs i≤2^22:=by
      have hh:i=0∨i=1∨i=2∨i=3:=by omega
      rcases hh with rfl|rfl|rfl|rfl <;> simp [start,stop] <;> omega
    apply ProcPriorOverlayTrafficRanges.truncate _ _ hn
    intro r hr hrf
    exact ProcPriorOverlayActualRows.source_zero _ hT (source i) r (hz r (by omega)) bus sd
  rw [full 0 (by omega),full 1 (by omega),full 2 (by omega),full 3 (by omega)]
  rfl
end ZkFormal.NearV3.Candidates.ProcPriorOverlayTraffic
