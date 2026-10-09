import ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordIndices
import ZkFormal.NearV3.Candidates.ProcPriorRoutedRecordParameters
import ZkFormal.NearV3.Candidates.ProcPriorPublicSenderBound
import ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteStamp
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteAddress
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Natural endpoint arithmetic is below 4096 before conversion to the field. -/
theorem link_nat {tr:Trace Fp} {t r:Nat} {pub:List Fp}
    (hs:cv tr t r ProcPriorRecordTable.senderIndex<64)
    (hr:cv tr t r ProcPriorRecordTable.receiverIndex<64)
    (hn:cv tr t r ProcPriorRecordTable.shards≤64) :
    (ProcPriorRecordTable.link.eval tr t r pub).toNat<4096 := by
  have hp:=Nat.mul_le_mul (show cv tr t r ProcPriorRecordTable.senderIndex≤63 by omega) hn
  have hb:cv tr t r ProcPriorRecordTable.senderIndex*cv tr t r ProcPriorRecordTable.shards+
      cv tr t r ProcPriorRecordTable.receiverIndex<4096 := by omega
  have hcell (x:Nat):tr.cell t r x=Fp.ofNat (cv tr t r x) := (Fp.ofNat_toNat _).symm
  change (tr.cell t r ProcPriorRecordTable.senderIndex*tr.cell t r ProcPriorRecordTable.shards+
    tr.cell t r ProcPriorRecordTable.receiverIndex).toNat<4096
  rw [hcell _,hcell _,hcell _,ZkFormal.Near.ofNat_mul',ZkFormal.Near.ofNat_add',Fp.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show cv tr t r ProcPriorRecordTable.senderIndex*cv tr t r ProcPriorRecordTable.shards+
      cv tr t r ProcPriorRecordTable.receiverIndex<P by rw [P_val];omega)]
  exact hb

theorem consumer_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
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
  obtain ⟨q,hq,hstage,hgate,hmsg,_⟩:=ProcPriorRoutedFamilyWrite.family_write_source hH htables h67 ht hr hi hb hs hm
  have ht0:0<AP.tables.length := by rw [htables];decide +kernel
  have hL:=local_of_holdsP hH ht0
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  have hact:=(ProcPriorRecordGeometry.write_shape hv hq hstage hgate).1
  have hparams:=ProcPriorRoutedRecordParameters.prepared_active_bounds hH htables hpar h76 I hp fwd hrec hq hstage hact
  have hpublic:=ProcPriorPublicSenderBound.prepared_public64 hH htables hpar I hp fwd hrec
  have hind:=ProcPriorRoutedRecordIndices.write_indices hH htables hpublic h70 h72 hq hstage hgate
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
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
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
  have ht:0<AP.tables.length := by rw [htables];decide +kernel
  have hi:ProcPriorRoutedWriteStamp.write∈AP.tables[0]!.interactions := by rw [htables];exact ProcPriorRoutedWriteStamp.write_member
  have hh:=consumer_bounds hH htables hpar h67 h70 h72 h76 I hp fwd hrec ht hr hi
    (show ProcPriorRoutedWriteStamp.write.bus=67 from rfl) (show ProcPriorRoutedWriteStamp.write.send=false from rfl)
    (ProcPriorRoutedWriteStamp.write_live ha hq)
  rw [ProcPriorRoutedWriteStamp.write_message] at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcPriorRoutedWriteAddress
