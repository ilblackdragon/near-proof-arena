import ZkFormal.NearV3.Candidates.ProcPriorRawClassify
import ZkFormal.NearV3.Candidates.ProcessRepairFamilyWrite
import ZkFormal.NearV3.Candidates.ProcessRepairWriteStamp
import ZkFormal.NearV3.Candidates.ProcessRepairRecordWordSources
import ZkFormal.NearV3.Candidates.ProcPriorRecordBackwardBoundary
import ZkFormal.NearV3.Candidates.ProcPriorRawTauUnique
namespace ZkFormal.NearV3.Candidates.ProcessRepairWriteFrame
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
open ProcPriorCodecFamilyLastWrite (memory)

theorem origin {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (h67:∀msg,pubCount AP pub 67 true msg=0)
    (h75:∀msg,pubCount AP pub 75 true msg=0)
    {r:Nat} (hr:r<tr.height 0)
    (ha:ProcPriorVerticalLastWrite.Live (memory tr) 0 r)
    (hq:cv (memory tr) 0 r ProcPriorMemoryTable.query=0):
    ∃f,f<tr.height 0 ∧ cv (raw tr) 0 f (ProcPriorVertical4Linear.stage 2)=1 ∧
      cv (raw tr) 0 f first=1 ∧ cv (raw tr) 0 f tau=cv (memory tr) 0 r ProcPriorMemoryTable.tau ∧
      cv (memory tr) 0 r ProcPriorMemoryTable.stamp<cv (raw tr) 0 f count := by
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:ProcPriorRoutedWriteStamp.write∈AP.tables[0]!.interactions:=by rw [view.wires];exact ProcPriorRoutedWriteStamp.write_member
  obtain ⟨q,hqh,hqs,hqg,hmsg,_⟩:=ProcessRepairFamilyWrite.family_write_source view h67 ht hr hi
    (show ProcPriorRoutedWriteStamp.write.bus=67 from rfl) (show ProcPriorRoutedWriteStamp.write.send=false from rfl)
    (ProcPriorRoutedWriteStamp.write_live ha hq)
  rw [ProcPriorRoutedWriteStamp.write_message] at hmsg
  have he0:=congrArg (fun xs:List Fp=>xs[0]!.toNat) hmsg
  have he2:=congrArg (fun xs:List Fp=>xs[2]!.toNat) hmsg
  change cv (raw tr) 0 q ProcPriorRecordTable.tau=cv (memory tr) 0 r ProcPriorMemoryTable.tau at he0
  change cv (raw tr) 0 q ProcPriorRecordTable.record=cv (memory tr) 0 r ProcPriorMemoryTable.stamp at he2
  have hv:=ProcessRepairRawBytes.overlay_local view
  obtain ⟨_,htop,_,_⟩:=ProcPriorRecordSound.write_flags hv hqh hqs hqg
  obtain ⟨a,haq,hah,has,haf⟩:=ProcPriorRecordBackwardBoundary.top_origin hv hqh hqs htop
  have hid:=ProcPriorRecordWordIdentity.limb_identity hv hah has haf 2 (by decide)
  rw [←haq] at hid
  obtain ⟨b,hbh,hbs,hbr,_,hbt,hbk,_,_⟩:=ProcessRepairRecordWordSources.bytes view h75 hah has haf 0 (by decide)
  have hh:(raw tr).height 0≤2013265921:=by
    have h:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
    exact Nat.le_trans h (by decide)
  obtain ⟨f,_,hfh,hfs,hff,_,hfk,_,hfields⟩:=ProcPriorRawClassify.record_row hv hh hbh hbs hbr
  have hft:cv (raw tr) 0 f tau=cv (memory tr) 0 r ProcPriorMemoryTable.tau:=
    (hfields tau (by simp)).symm.trans (hbt.trans (hid.1.symm.trans he0))
  have hstamp:cv (raw tr) 0 b record=cv (memory tr) 0 r ProcPriorMemoryTable.stamp:=hbk.trans (hid.2.symm.trans he2)
  exact ⟨f,hfh,hfs,hff,hft,by rw [←hstamp];exact hfk⟩

theorem empty {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (h67:∀msg,pubCount AP pub 67 true msg=0)
    (h75:∀msg,pubCount AP pub 75 true msg=0)
    {f:Nat} (hf:f<tr.height 0)
    (hfs:cv (raw tr) 0 f (ProcPriorVertical4Linear.stage 2)=1)
    (hff:cv (raw tr) 0 f first=1) (hzero:cv (raw tr) 0 f count=0):
    ∀r,r<tr.height 0→ProcPriorVerticalLastWrite.Live (memory tr) 0 r→
      cv (memory tr) 0 r ProcPriorMemoryTable.tau=cv (raw tr) 0 f tau→
      cv (memory tr) 0 r ProcPriorMemoryTable.query≠0 := by
  intro r hr ha ht hq
  obtain ⟨g,hg,hgs,hgf,hgt,hcount⟩:=origin view h67 h75 hr ha hq
  have hh:(raw tr).height 0≤2013265921:=by
    have h:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
    exact Nat.le_trans h (by decide)
  have he:g=f:=ProcPriorRawTauUnique.first_unique (ProcessRepairRawBytes.overlay_local view) hh hg hf hgs hfs hgf hff (hgt.trans ht)
  rw [he,hzero] at hcount
  omega

theorem absent {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (h67:∀msg,pubCount AP pub 67 true msg=0)
    (h75:∀msg,pubCount AP pub 75 true msg=0)
    {f:Nat} (hf:f<tr.height 0)
    (hfs:cv (raw tr) 0 f (ProcPriorVertical4Linear.stage 2)=1)
    (hff:cv (raw tr) 0 f first=1) (hzero:cv (raw tr) 0 f present=0):
    ∀r,r<tr.height 0→ProcPriorVerticalLastWrite.Live (memory tr) 0 r→
      cv (memory tr) 0 r ProcPriorMemoryTable.tau=cv (raw tr) 0 f tau→
      cv (memory tr) 0 r ProcPriorMemoryTable.query≠0 := by
  exact empty view h67 h75 hf hfs hff (ProcPriorRawSound.absent_zero (ProcessRepairRawBytes.overlay_local view) hf hfs hzero).2
end ZkFormal.NearV3.Candidates.ProcessRepairWriteFrame
