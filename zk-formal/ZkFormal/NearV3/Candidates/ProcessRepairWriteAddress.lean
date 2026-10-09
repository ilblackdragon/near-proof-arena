import ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteAddress
import ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordIndices
import ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordParameters
import ZkFormal.NearV3.Candidates.ProcPriorPublicSenderBound
import ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteStamp
import ZkFormal.NearV3.Candidates.ProcessRepairRecordIndices
import ZkFormal.NearV3.Candidates.ProcessRepairRecordParameters
import ZkFormal.NearV3.Candidates.ProcessRepairPublicSenderBound
import ZkFormal.NearV3.Candidates.ProcessRepairFamilyWrite
namespace ZkFormal.NearV3.Candidates.ProcessRepairWriteAddress
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable ProcPriorRoutedWriteAddress
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
theorem consumer_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpar:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h67:∀msg,pubCount AP pub 67 true msg=0)
    (h70:∀msg,pubCount AP pub 70 true msg=0)
    (h72:∀msg,pubCount AP pub 72 true msg=0)
    (h76:∀msg,pubCount AP pub 76 true msg=0)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=67) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    (i.msgVal tr t r pub)[0]!.toNat<33 ∧ (i.msgVal tr t r pub)[1]!.toNat<4096 ∧
    4096*(i.msgVal tr t r pub)[0]!.toNat+(i.msgVal tr t r pub)[1]!.toNat<2^29 := by
  obtain ⟨q,hq,hstage,hgate,hmsg,_⟩:=ProcessRepairFamilyWrite.family_write_source view h67 ht hr hi hb hs hm
  have ht0:0<AP.tables.length := by rw [view.length];decide +kernel
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hact:=(ProcPriorRecordGeometry.write_shape hv hq hstage hgate).1
  have hparams:=ProcessRepairRecordParameters.prepared_active_bounds view hpar h76 I hp fwd hrec hq hstage hact
  have hpublic:=ProcessRepairPublicSenderBound.prepared_public64 view hpar I hp fwd hrec
  have hind:=ProcessRepairRecordIndices.write_indices view hpublic h70 h72 hq hstage hgate
  have hlink:=link_nat (pub:=pub) hind.1 hind.2 hparams.2.2
  have he0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
  have he1:=congrArg (fun xs:List Fp=>xs[1]!.toNat) hmsg
  change cv (HorizontalTrace.project ProcPriorRoutedFamilyWrite.offset tr) 0 q ProcPriorRecordTable.tau=
    (i.msgVal tr t r pub)[0]!.toNat at he0
  change (ProcPriorRecordTable.link.eval (HorizontalTrace.project ProcPriorRoutedFamilyWrite.offset tr) 0 q pub).toNat=
    (i.msgVal tr t r pub)[1]!.toNat at he1
  change cv (HorizontalTrace.project ProcPriorRoutedFamilyWrite.offset tr) 0 q ProcPriorRecordTable.tau<33 ∧ _ at hparams
  change (ProcPriorRecordTable.link.eval (HorizontalTrace.project ProcPriorRoutedFamilyWrite.offset tr) 0 q pub).toNat<4096 at hlink
  omega

theorem write_address {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpar:∀seg∈AP.pubSegs,seg.bus=B_SPAR→seg.send=true)
    (h67:∀msg,pubCount AP pub 67 true msg=0)
    (h70:∀msg,pubCount AP pub 70 true msg=0)
    (h72:∀msg,pubCount AP pub 72 true msg=0)
    (h76:∀msg,pubCount AP pub 76 true msg=0)
    (I:PubIdx AP pub Fp.ofNat)
    {cb:NearSpec.Bytes} {hint:NearSpecV3.Hint} {p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (fwd:List (Nat×Nat))
    (hrec:I.recs B_SPAR true=(render (p.sched.map instOf) fwd).par)
    {r:Nat} (hr:r<tr.height 0) (ha:ProcPriorVerticalLastWrite.Live (memory tr) 0 r)
    (hq:cv (memory tr) 0 r ProcPriorMemoryTable.query=0) :
    cv (memory tr) 0 r ProcPriorMemoryTable.tau<33 ∧ cv (memory tr) 0 r ProcPriorMemoryTable.link<4096 ∧
    ProcPriorAddressOrder.address (memory tr) 0 r<2^29 := by
  have ht:0<AP.tables.length := by rw [view.length];decide +kernel
  have hi:ProcPriorRoutedWriteStamp.write∈AP.tables[0]!.interactions := by rw [view.wires];exact ProcPriorRoutedWriteStamp.write_member
  have hh:=consumer_bounds view hpar h67 h70 h72 h76 I hp fwd hrec ht hr hi
    (show ProcPriorRoutedWriteStamp.write.bus=67 from rfl) (show ProcPriorRoutedWriteStamp.write.send=false from rfl)
    (ProcPriorRoutedWriteStamp.write_live ha hq)
  rw [ProcPriorRoutedWriteStamp.write_message] at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcessRepairWriteAddress
