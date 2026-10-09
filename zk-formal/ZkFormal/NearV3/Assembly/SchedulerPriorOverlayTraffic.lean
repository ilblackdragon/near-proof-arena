import ZkFormal.NearV3.Candidates.ProcPriorOverlayTraffic
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorOverlayNativeSources

theorem native_overlay_traffic {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActualFamily.overlay.interactions
      (priorOverlay bs) t r pub bus sd)=
      ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 0 bus sd++
      ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 1 bus sd++
      ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 2 bus sd++
      ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 3 bus sd := by
  have hpub:∀b∈bs,b.pub∈p.sched:=by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    exact List.mem_iff_getElem?.mpr ⟨i,(hc.indexed i b hi).1.1⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hb=>(prepD0_sched hp b.pub (hpub b hb)).n64
  have hraw:(ProcRawConcatGeometry.rows bs).length≤2001184:=by have :=hc.raw_bound;omega
  have hh:=ProcPriorOverlayCuts.cuts bs hn hc.length hraw
  apply ProcPriorOverlayTraffic.physical bs ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩ (priorSource bs) (used bs) ?_
  intro T i hi
  have hi4:i<4:=by
    have :=(List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hi)).1
    exact this
  have hr:=room bs hn hc.length hraw i hi4
  change (T,i)∈[(_,0),(_,1),(_,2),(_,3)] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hi
  rcases hi with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨rfl,hr,memory_padding bs⟩
  · refine ⟨rfl,hr,?_⟩
    intro j hj
    apply ProcIdNativeLocal.suffix
    simpa [used,ProcPriorOverlayBudget.idRows,ProcIdConcatTraffic.rows,
      ProcIdConcatTraffic.blockRows,List.length_flatMap] using hj
  · exact ⟨rfl,hr,raw_padding bs⟩
  · exact ⟨rfl,hr,record_padding bs⟩

/-- Every bus and direction conserves natural counts under actual native
vertical installation. Existing component balances can be composed by addition. -/
theorem native_overlay_count {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub : List Fp) (bus : Nat) (sd : Bool) (msg : List Fp) :
    tableBusCount ProcPriorCodecActualFamily.overlay.interactions (priorOverlay bs) t pub bus sd msg=
      (ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 0 bus sd).count msg+
      (ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 1 bus sd).count msg+
      (ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 2 bus sd).count msg+
      (ProcPriorOverlayTraffic.sourceTraffic (priorSource bs) 3 bus sd).count msg := by
  rw [tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [native_overlay_traffic hp bs hc hB t pub bus sd]
  simp only [List.count_append]
end ZkFormal.NearV3.Assembly.CodecDigest
