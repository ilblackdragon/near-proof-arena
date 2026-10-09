import ZkFormal.NearV3.Candidates.ProcPriorRecordWriteGate
import ZkFormal.NearV3.Candidates.ProcessRepairMemoryWriteConsumer
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordWriteCoverage
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRoutedFamilyWrite
open ProcPriorRoutedRawSource (raw)
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem write_member:write∈ProcPriorComparatorRoutedFamily.fused.interactions:=by
  have hraw:write∈ProcPriorComparatorRoutedFamily.raw.interactions:=by
    have h:write∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==67 && i.send):=by
      rw [raw_senders];exact List.mem_singleton_self _
    exact (List.mem_filter.mp h).1
  have hp:write∈ProcPriorComparatorRoutedFamily.paired.interactions:=(InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀i∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,i≠write:=by
    intro i hi he;exact hn (he ▸ hi)
  have hd (b:Bool):InteractionTriples.dummy b≠write:=by
    intro he
    have hb:=congrArg Interaction.bus he
    exact (by decide : 0≠67) hb
  exact ((InteractionTriples.forall_iff _ (fun i=>i≠write) (hd true) (hd false)).mp hall) _ hp rfl

theorem live {tr:Trace Fp} {r:Nat} {pub:List Fp}
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hg:cv (raw tr) 0 r ProcPriorRecordTable.writeGate=1):write.multNat tr 0 r pub≠0:=by
  rw [projected_mult]
  have hc (x:Nat):(raw tr).cell 0 r x=Fp.ofNat (cv (raw tr) 0 r x):=(Fp.ofNat_toNat _).symm
  change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 3)*(raw tr).cell 0 r ProcPriorRecordTable.writeGate=1 then 1 else 0)+0≠0
  rw [hc _,hc _,hs,hg]
  decide +kernel

/-- A covered native record with both IDs found cannot be silently omitted:
its actual amount/top row forces a matching physical memory write. -/
theorem emitted {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠67)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (ha:cv (raw tr) 0 r ProcPriorRecordTable.amount=1)
    (htop:cv (raw tr) 0 r ProcPriorRecordTable.topLimb=1)
    (hsf:cv (raw tr) 0 r ProcPriorRecordTable.senderFound=1)
    (hrf:cv (raw tr) 0 r ProcPriorRecordTable.receiverFound=1):
    ∃q,q<tr.height 0 ∧ ProcPriorVerticalLastWrite.Live (memory tr) 0 q ∧
      cv (memory tr) 0 q ProcPriorMemoryTable.query=0 ∧
      cv (memory tr) 0 q ProcPriorMemoryTable.tau=cv (raw tr) 0 r ProcPriorRecordTable.tau ∧
      cv (memory tr) 0 q ProcPriorMemoryTable.link=(ProcPriorRecordTable.link.eval (raw tr) 0 r pub).toNat ∧
      cv (memory tr) 0 q ProcPriorMemoryTable.stamp=cv (raw tr) 0 r ProcPriorRecordTable.record ∧
      cv (memory tr) 0 q ProcPriorMemoryTable.lo=cv (raw tr) 0 r ProcPriorRecordTable.lo ∧
      cv (memory tr) 0 q ProcPriorMemoryTable.hi=cv (raw tr) 0 r ProcPriorRecordTable.big:=by
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hg:=ProcPriorRecordWriteGate.enabled hv hr hs ha htop hsf hrf
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:write∈AP.tables[0]!.interactions:=by rw [view.wires];exact write_member
  obtain ⟨q,hq,hqa,hqq,hmsg⟩:=ProcessRepairMemoryWriteConsumer.matched view hpub ht hr hi
    (show write.bus=67 from rfl) (show write.send=true from rfl) (live hs hg)
  rw [projected_message] at hmsg
  have he:=congrArg (List.map Fp.toNat) hmsg
  change [cv (memory tr) 0 q ProcPriorMemoryTable.tau,cv (memory tr) 0 q ProcPriorMemoryTable.link,
    cv (memory tr) 0 q ProcPriorMemoryTable.stamp,cv (memory tr) 0 q ProcPriorMemoryTable.lo,cv (memory tr) 0 q ProcPriorMemoryTable.hi]=
    [cv (raw tr) 0 r ProcPriorRecordTable.tau,(ProcPriorRecordTable.link.eval (raw tr) 0 r pub).toNat,
    cv (raw tr) 0 r ProcPriorRecordTable.record,cv (raw tr) 0 r ProcPriorRecordTable.lo,cv (raw tr) 0 r ProcPriorRecordTable.big] at he
  simp only [List.cons.injEq] at he
  exact ⟨q,hq,hqa,hqq,he.1,he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2.1⟩
end ZkFormal.NearV3.Candidates.ProcessRepairRecordWriteCoverage
