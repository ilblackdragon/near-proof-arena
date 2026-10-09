import ZkFormal.NearV3.Candidates.ProcessRepairBalance
import ZkFormal.NearV3.Candidates.ProcPriorRoutedRawBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched
open ProcPriorRoutedRawSource (raw)
open ProcPriorRoutedRawBytes
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem overlay_local {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :
    ProcPriorVerticalMemorySound.LocalV (raw tr) 0 pub := by
  have h:=v.component 19 (by decide +kernel) (by decide)
  change ZkFormal.Near.TableLocal (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActualFamily.overlay)
    (raw tr) 0 pub at h
  intro r hr e he
  apply h.constr r hr e
  change e ∈ ProcPriorCodecActualFamily.overlay.constraints
  rw [ProcPriorCodecFamilyProjection.overlay_constraints]
  exact he

theorem byte_source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (ha:cv (raw tr) 0 r ProcPriorRawFrame.act=1) (hpres:cv (raw tr) 0 r ProcPriorRawFrame.present=1) :
    ∃q,q<tr.height 0 ∧ cv (value tr) 0 q ValV3.gb=1 ∧
      cv (value tr) 0 q ValV3.vid=cv (raw tr) 0 r ProcPriorRawFrame.vid ∧
      cv (value tr) 0 q ValV3.pos=cv (raw tr) 0 r ProcPriorRawFrame.pos ∧
      cv (value tr) 0 q ValV3.b=cv (raw tr) 0 r ProcPriorRawFrame.byte := by
  have ht:0<AP.tables.length := by rw [v.length];decide +kernel
  have hi:bytes∈AP.tables[0]!.interactions := by rw [v.wires];exact bytes_member
  have hv:=overlay_local v
  have hg:=ProcPriorRawSound.byte_gate hv hr hs ha hpres
  have hm:bytes.multNat tr 0 r pub≠0 := by
    rw [bytes_mult]
    have hcell (x:Nat) (hx:cv (raw tr) 0 r x=1):(raw tr).cell 0 r x=Fp.ofNat 1 := by
      rw [←hx];exact (Fp.ofNat_toNat _).symm
    have h1:=hcell _ hs
    have h2:=hcell _ hg
    change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 2)*(raw tr).cell 0 r ProcPriorRawFrame.byteGate=1 then 1 else 0)+0≠0
    rw [h1,h2]
    decide +kernel
  have ho:∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=B_VBYTES→i.send=true := by
    intro t ht hn i hi hb
    cases hs:i.send with
    | false=>exact (other_tables (AP:=ProcessRepairBalance.reference AP) rfl t (by simpa [ProcessRepairBalance.reference, ←v.length] using ht) hn i (by simpa only [v.wires t, ProcessRepairBalance.reference] using hi) hs hb).elim
    | true=>rfl
  obtain ⟨q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=send_matched v.valid ht ho hpub ht hr hi
    (show bytes.bus=B_VBYTES from rfl) (show bytes.send=true from rfl) hm
  rw [v.wires] at hj
  have hej:=receiver_eq hj hjb hjs
  subst j
  rw [receiver_message,bytes_message] at hmsg
  rw [receiver_mult] at hjm
  have hgb:cv (value tr) 0 q ValV3.gb=1 := by
    have he:(value tr).cell 0 q ValV3.gb=1 := by
      by_cases he:(value tr).cell 0 q ValV3.gb=1
      · exact he
      · change (if (value tr).cell 0 q ValV3.gb=1 then 1 else 0)+0≠0 at hjm
        simp only [he,ite_false,Nat.zero_add] at hjm
        exact (hjm rfl).elim
    unfold cv;rw [he];rfl
  have e0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
  have e1:=congrArg (fun xs:List Fp=>xs[1]!.toNat) hmsg
  have e2:=congrArg (fun xs:List Fp=>xs[2]!.toNat) hmsg
  exact ⟨q,hq,hgb,e0,e1,e2⟩
end ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
