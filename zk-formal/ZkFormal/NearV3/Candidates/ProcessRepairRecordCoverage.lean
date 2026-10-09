import ZkFormal.NearV3.Candidates.ProcessRepairRecordByteCoverage
import ZkFormal.NearV3.Candidates.ProcPriorRecordLastByte
import ZkFormal.NearV3.Candidates.ProcessRepairTrieViews
import ZkFormal.NearV3.Candidates.ProcPriorRawRecordPosition
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordCoverage
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRoutedRawSource
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem read_member:read∈ProcPriorComparatorRoutedFamily.fused.interactions:=by
  have hraw:read∈ProcPriorComparatorRoutedFamily.raw.interactions:=by
    have h:read∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==75 && i.send):=by
      rw [raw_senders];exact List.mem_singleton_self _
    exact (List.mem_filter.mp h).1
  have hp:read∈ProcPriorComparatorRoutedFamily.paired.interactions:=(InteractionPairing.reorder_perm _).mem_iff.mpr hraw
  apply Classical.byContradiction
  intro hn
  have hall:∀i∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,i≠read:=by
    intro i hi he;exact hn (he ▸ hi)
  have hd (b:Bool):InteractionTriples.dummy b≠read:=by
    intro he
    have hb:=congrArg Interaction.bus he
    exact (by decide : 0≠75) hb
  exact ((InteractionTriples.forall_iff _ (fun i=>i≠read) (hd true) (hd false)).mp hall) _ hp rfl

theorem read_live {tr:Trace Fp} {r:Nat} {pub:List Fp}
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hr:cv (raw tr) 0 r ProcPriorRawFrame.rec=1):read.multNat tr 0 r pub≠0:=by
  rw [projected_mult]
  have hc (x:Nat):(raw tr).cell 0 r x=Fp.ofNat (cv (raw tr) 0 r x):=(Fp.ofNat_toNat _).symm
  change (if (raw tr).cell 0 r (ProcPriorVertical4Linear.stage 2)*(raw tr).cell 0 r ProcPriorRawFrame.rec=1 then 1 else 0)+0≠0
  rw [hc _,hc _,hs,hr]
  decide +kernel

/-- Each actual raw record's final byte forces a physical amount/top row
with the same original instance and record ordinal. Found flags and native
shard lookup decide whether that row emits a write. -/
theorem last_byte {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠75)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hrec:cv (raw tr) 0 r ProcPriorRawFrame.rec=1)
    (hoff:cv (raw tr) 0 r ProcPriorRawFrame.offset=23):
    ∃q,q<tr.height 0 ∧ cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv (raw tr) 0 q ProcPriorRecordTable.amount=1 ∧ cv (raw tr) 0 q ProcPriorRecordTable.topLimb=1 ∧
      cv (raw tr) 0 q ProcPriorRecordTable.tau=cv (raw tr) 0 r ProcPriorRawFrame.tau ∧
      cv (raw tr) 0 q ProcPriorRecordTable.record=cv (raw tr) 0 r ProcPriorRawFrame.record ∧
      cv (raw tr) 0 q ProcPriorRecordTable.byte1=cv (raw tr) 0 r ProcPriorRawFrame.byte := by
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:read∈AP.tables[0]!.interactions:=by rw [view.wires];exact read_member
  obtain ⟨q,j,hq,hj,hstage,hword,htop,hbound,hmsg⟩:=ProcessRepairRecordByteCoverage.matched view hpub ht hr hi
    (show read.bus=75 from rfl) (show read.send=true from rfl) (read_live hs hrec)
  rw [projected_message] at hmsg
  have he:=congrArg (List.map Fp.toNat) hmsg
  have hc (x:Nat):cv (raw tr) 0 q x<P:=by rw [P_val];exact Codec.lt (tr:=raw tr) (t:=0) q x
  have hp:ProcPriorRecordByteMessage.offsetNat (raw tr) 0 q+j<P:=by rw [P_val];omega
  change _=[cv (raw tr) 0 r ProcPriorRawFrame.tau,cv (raw tr) 0 r ProcPriorRawFrame.record,
    cv (raw tr) 0 r ProcPriorRawFrame.offset,cv (raw tr) 0 r ProcPriorRawFrame.byte] at he
  simp only [List.map_cons,List.map_nil,Fp.toNat_ofNat,Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt (hc ProcPriorRecordTable.tau),Nat.mod_eq_of_lt (hc ProcPriorRecordTable.record),
    Nat.mod_eq_of_lt (hc (ProcPriorRecordTable.byte0+j)),List.cons.injEq] at he
  have hoffq:=he.2.2.1.trans hoff
  obtain ⟨ha,htopq,hj1⟩:=ProcPriorRecordLastByte.shape (ProcessRepairRawBytes.overlay_local view) hq hstage hword hj htop hoffq
  subst j
  exact ⟨q,hq,hstage,ha,htopq,he.1,he.2.1,he.2.2.2.1⟩
theorem frame {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠75)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r ProcPriorRawFrame.first=1) :
    ∀k,k<cv (raw tr) 0 r ProcPriorRawFrame.count→∃q,q<tr.height 0 ∧
      cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv (raw tr) 0 q ProcPriorRecordTable.amount=1 ∧ cv (raw tr) 0 q ProcPriorRecordTable.topLimb=1 ∧
      cv (raw tr) 0 q ProcPriorRecordTable.tau=cv (raw tr) 0 r ProcPriorRawFrame.tau ∧
      cv (raw tr) 0 q ProcPriorRecordTable.record=k := by
  intro k hk
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hh:(raw tr).height 0≤2013265921:=by
    have h:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
    exact Nat.le_trans h (by decide)
  obtain ⟨hz,hzs,_,hzr,hzo,hzk,_,hfields⟩:=ProcPriorRawRecordPosition.bytes hv hr hs hf hh k 23 hk (by decide)
  obtain ⟨q,hq,hqs,hqa,hqt,htau,hrecord,_⟩:=last_byte view hpub hz hzs hzr hzo
  exact ⟨q,hq,hqs,hqa,hqt,htau.trans (hfields _ (by simp)),hrecord.trans hzk⟩

end ZkFormal.NearV3.Candidates.ProcessRepairRecordCoverage
