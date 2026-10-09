import ZkFormal.NearV3.Candidates.ProcessRepairNativeDecode
import ZkFormal.NearV3.Candidates.ProcPriorBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairDecodedRecords
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRawFrame
open ProcPriorRoutedRawSource (raw)
open ProcPriorRoutedRawBytes (value)

theorem mapped_byte (bs:NearSpec.Bytes) (data:List Nat)
    (he:bs.map UInt8.toNat=data) (j:Nat) :
    (bs.getD j 0).toNat=data.getD j 0 := by
  have h:=congrArg (fun xs:List Nat=>xs.getD j 0) he
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map] at h ⊢
  cases hj:bs[j]? with
  | none=>simpa [hj] using h
  | some b=>simpa [hj] using h

/-- A parser record row contains the corresponding byte of the exact native
record, including original IDs and allowance, without a generated-row premise. -/
theorem record_byte {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r first=1) (hp:cv (raw tr) 0 r present=1)
    {bs:NearSpec.Bytes} {st:NearSpec.Bandwidth.State}
    (hbytes:bs.map UInt8.toNat=(es[cv (raw tr) 0 r vid]!).bytes)
    (hd:NearSpec.Bandwidth.State.decode bs=some st)
    (hc:st.links.length=cv (raw tr) 0 r count)
    (k j:Nat) {link:NearSpec.Bandwidth.LinkAllowance}
    (hk:st.links[k]?=some link) (hj:j<24) :
    cv (raw tr) 0 (r+5+24*k+j) byte=(link.encode.getD j 0).toNat := by
  have hkn:k<st.links.length:=(List.getElem?_eq_some_iff.mp hk).1
  have hpj:5+24*k+j<37+24*cv (raw tr) 0 r count:=by omega
  have hb:=(ProcessRepairRawFrameBytes.byte_at view hpubV hw hT hr hs hf hp (5+24*k+j) hpj).2.2.2
  have hm:=mapped_byte bs _ hbytes (5+24*k+j)
  have hslice:=ProcPriorBytes.decoded_record_slice bs st hd k link hk
  have he:=congrArg (fun xs:NearSpec.Bytes=>(xs.getD j 0).toNat) hslice
  simp only [List.getD_eq_getElem?_getD,List.getElem?_take,hj,ite_true,List.getElem?_drop] at he
  have hb':cv (raw tr) 0 (r+5+24*k+j) byte=(bs.getD (5+24*k+j) 0).toNat:=by
    simpa only [Nat.add_assoc] using hb.trans hm.symm
  exact hb'.trans he
theorem sanity_slice (bs:NearSpec.Bytes) (st:NearSpec.Bandwidth.State)
    (hd:NearSpec.Bandwidth.State.decode bs=some st) :
    bs.drop (5+24*st.links.length)=st.sanityHash := by
  rw [(ProcPriorDecode.decode_exact bs st hd).2.2.2]
  have hprefix:(([0]++NearSpec.u32 st.links.length)++NearSpec.concatAll (st.links.map NearSpec.Bandwidth.LinkAllowance.encode)).length=5+24*st.links.length:=by
    simp only [List.length_append,List.length_cons,List.length_nil,NearSpec.u32,canon_leN_length,
      ProcPriorDecode.links_encoded_length]
  change ((([0]++NearSpec.u32 st.links.length)++NearSpec.concatAll (st.links.map NearSpec.Bandwidth.LinkAllowance.encode))++st.sanityHash).drop _=_
  rw [←hprefix,List.drop_left]

theorem sanity_byte {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (value tr) 0 pub (valTraffic es))
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 2)=1)
    (hf:cv (raw tr) 0 r first=1) (hp:cv (raw tr) 0 r present=1)
    {bs:NearSpec.Bytes} {st:NearSpec.Bandwidth.State}
    (hbytes:bs.map UInt8.toNat=(es[cv (raw tr) 0 r vid]!).bytes)
    (hd:NearSpec.Bandwidth.State.decode bs=some st)
    (hc:st.links.length=cv (raw tr) 0 r count)
    (j:Nat) (hj:j<32) :
    cv (raw tr) 0 (r+5+24*cv (raw tr) 0 r count+j) byte=(st.sanityHash.getD j 0).toNat := by
  have hpj:5+24*cv (raw tr) 0 r count+j<37+24*cv (raw tr) 0 r count:=by omega
  have hb:=(ProcessRepairRawFrameBytes.byte_at view hpubV hw hT hr hs hf hp
    (5+24*cv (raw tr) 0 r count+j) hpj).2.2.2
  have hm:=mapped_byte bs _ hbytes (5+24*cv (raw tr) 0 r count+j)
  have he:=congrArg (fun xs:NearSpec.Bytes=>(xs.getD j 0).toNat) (sanity_slice bs st hd)
  simp only [List.getD_eq_getElem?_getD,List.getElem?_drop,hc] at he
  have hb':cv (raw tr) 0 (r+5+24*cv (raw tr) 0 r count+j) byte=
      (bs.getD (5+24*cv (raw tr) 0 r count+j) 0).toNat:=by
    simpa only [Nat.add_assoc] using hb.trans hm.symm
  exact hb'.trans he
end ZkFormal.NearV3.Candidates.ProcessRepairDecodedRecords
