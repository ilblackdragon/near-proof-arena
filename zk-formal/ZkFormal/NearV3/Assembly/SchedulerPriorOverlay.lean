import ZkFormal.NearV3.Candidates.ProcPriorOverlayNativeSources
import ZkFormal.NearV3.Candidates.ProcIdNativeLocal
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ProcPriorOverlayNativeSources

def priorSource (bs : List NativeBlock) (i : Nat) : Trace Fp :=
  if i=0 then memory bs
  else if i=1 then ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)
  else if i=2 then raw bs else records bs

def priorOverlay (bs : List NativeBlock) : Trace Fp :=
  ProcPriorOverlayCuts.trace bs (fun i=>(priorSource bs i).cell 0)

theorem prior_overlay_local {B : Nat} {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (hB:B≤2000000) (t : Nat) (pub : List Fp) :
    TableLocal ProcPriorVertical4Linear.table (priorOverlay bs) t pub := by
  have hpub:∀b∈bs,b.pub∈p.sched:=by
    intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    exact List.mem_iff_getElem?.mpr ⟨i,(hc.indexed i b hi).1.1⟩
  have hn:∀b∈bs,b.pub.ids.length≤64:=fun b hb=>(prepD0_sched hp b.pub (hpub b hb)).n64
  have hraw:(ProcRawConcatGeometry.rows bs).length≤2001184:=by have :=hc.raw_bound;omega
  have hid: (ProcIdConcatTraffic.rows (fun b=>b.pub.ids) bs).length<2^22:=
    ProcNativeIdBalance.native_capacity _ bs hn hc.length hraw
  have hlid:=ProcIdNativeLocal.prepared hp bs (fun b hb=>(hc.valid b hb).1) hpub
    (fun i b hi=>(hc.indexed i b hi).2.1) hc.length hid 0 []
  apply ProcPriorOverlayLocal.local_table bs hn hc.length hraw (priorSource bs) (used bs) ?_ t pub
  intro T i hi
  have hi4:i<4:=by
    have :=(List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hi)).1
    exact this
  have hr:=room bs hn hc.length hraw i hi4
  simp only [ProcPriorVertical4Linear.components,List.zipIdx_cons,List.zipIdx_nil,
    List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hi
  rcases hi with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨rfl,hc.memory_local 0 [],hr,memory_padding bs⟩
  · refine ⟨rfl,hlid,hr,?_⟩
    intro j hj
    apply ProcIdNativeLocal.suffix
    simpa [used,ProcPriorOverlayBudget.idRows,ProcIdConcatTraffic.rows,
      ProcIdConcatTraffic.blockRows,List.length_flatMap] using hj
  · exact ⟨rfl,ProcRawNativeLocal.table bs (fun b hb=>(hc.valid b hb).1)
      (fun i b hi=>(hc.indexed i b hi).2.1) (by omega) 0 59 73 _ 74 75 [],hr,raw_padding bs⟩
  · exact ⟨rfl,hc.record_local 0 [],hr,record_padding bs⟩

theorem accepted_prior_overlay {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧ ∀t pub,
      TableLocal ProcPriorVertical4Linear.table (priorOverlay bs) t pub := by
  obtain ⟨bs,hc⟩:=accepted_prior_core hp hk hw h hB
  exact ⟨bs,hc,prior_overlay_local hp bs hc hB⟩
end ZkFormal.NearV3.Assembly.CodecDigest
