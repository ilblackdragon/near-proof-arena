import ZkFormal.NearV3.Candidates.ProcessRepairRawSource
import ZkFormal.NearV3.Candidates.ProcPriorRecordByteMessage
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordByteSource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRecordTable
open ProcPriorRoutedRawSource (raw)
open ProcPriorRecordPhysicalBytes

theorem source {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀msg,pubCount AP pub 75 true msg=0)
    {r j:Nat} (hr:r<tr.height 0) (hj:j<3)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv (raw tr) 0 r sender+cv (raw tr) 0 r receiver+cv (raw tr) 0 r amount=1)
    (ht:j=2→cv (raw tr) 0 r topLimb=0) :
    ∃q,q<tr.height 0 ∧ cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv (raw tr) 0 q ProcPriorRawFrame.rec=1 ∧ cv (raw tr) 0 q ProcPriorRawFrame.act=1 ∧
      cv (raw tr) 0 q ProcPriorRawFrame.tau=cv (raw tr) 0 r tau ∧
      cv (raw tr) 0 q ProcPriorRawFrame.record=cv (raw tr) 0 r record ∧
      cv (raw tr) 0 q ProcPriorRawFrame.offset=ProcPriorRecordByteMessage.offsetNat (raw tr) 0 r+j ∧
      cv (raw tr) 0 q ProcPriorRawFrame.byte=cv (raw tr) 0 r (byte0+j) := by
  have hlen:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:request j∈AP.tables[0]!.interactions:=by rw [view.wires];exact member j hj
  have casesj:j=0 ∨ j=1 ∨ j=2:=by omega
  have hb:(request j).bus=75:=by rcases casesj with rfl|rfl|rfl <;> rfl
  have hsend:(request j).send=false:=by rcases casesj with rfl|rfl|rfl <;> rfl
  obtain ⟨q,hq,hstage,hrec,hact,hmsg⟩:=ProcessRepairRawSource.record_source view hpub hlen hr hi hb hsend (live hj hs hw ht)
  rw [message,ProcPriorRecordByteMessage.message _ _ _ _ _ hj] at hmsg
  have he:=congrArg (List.map Fp.toNat) hmsg
  have ho:=ProcPriorRecordByteMessage.offset_bound (ProcessRepairRawBytes.overlay_local view) hr hs j hj ht
  have hp:ProcPriorRecordByteMessage.offsetNat (raw tr) 0 r+j<P:=by rw [P_val];omega
  change [cv (raw tr) 0 q ProcPriorRawFrame.tau,cv (raw tr) 0 q ProcPriorRawFrame.record,
    cv (raw tr) 0 q ProcPriorRawFrame.offset,cv (raw tr) 0 q ProcPriorRawFrame.byte]=_ at he
  have hc (x:Nat):cv (raw tr) 0 r x<P:=by
    rw [P_val];exact Codec.lt (tr:=raw tr) (t:=0) r x
  simp only [List.map_cons,List.map_nil,Fp.toNat_ofNat,Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt (hc tau),
    Nat.mod_eq_of_lt (hc record),
    Nat.mod_eq_of_lt (hc (byte0+j)),List.cons.injEq] at he
  exact ⟨q,hq,hstage,hrec,hact,he.1,he.2.1,he.2.2.1,he.2.2.2.1⟩
end ZkFormal.NearV3.Candidates.ProcessRepairRecordByteSource
