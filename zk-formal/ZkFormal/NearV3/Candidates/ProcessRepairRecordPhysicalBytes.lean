import ZkFormal.NearV3.Candidates.ProcPriorRecordPhysicalBytes
import ZkFormal.NearV3.Candidates.ProcessRepairRawSource
import ZkFormal.NearV3.Candidates.ProcessRepairValueBytes
import ZkFormal.NearV3.Candidates.ProcessRepairRecordByteRange
import ZkFormal.NearV3.Candidates.ProcPriorRecordWordTraversal
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordPhysicalBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
open ProcPriorRoutedRawSource (raw)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open ProcPriorRecordPhysicalBytes
theorem byte_bound {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hbytes:∀e∈es,∀b∈e.bytes,b<256)
    {r j:Nat} (hr:r<tr.height 0) (hj:j<3)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hword:cv (raw tr) 0 r sender+cv (raw tr) 0 r receiver+cv (raw tr) 0 r amount=1)
    (htop:j=2→cv (raw tr) 0 r topLimb=0) :
    cv (raw tr) 0 r (byte0+j)<256 := by
  have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
  have hi:request j∈AP.tables[0]!.interactions:=by rw [view.wires];exact member j hj
  have hjc:j=0∨j=1∨j=2:=by omega
  have hb:(request j).bus=75:=by rcases hjc with rfl|rfl|rfl <;> rfl
  have hsend:(request j).send=false:=by rcases hjc with rfl|rfl|rfl <;> rfl
  have h:=ProcessRepairRecordByteRange.received view hpubV hpubR hw hT hbytes ht hr hi hb hsend (live hj hs hword htop)
  rw [message] at h
  rcases hjc with rfl|rfl|rfl <;> exact h
theorem row_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hbytes:∀e∈es,∀b∈e.bytes,b<256)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hword:cv (raw tr) 0 r sender+cv (raw tr) 0 r receiver+cv (raw tr) 0 r amount=1) :
    ∀x∈[byte0,byte1,byte2],cv (raw tr) 0 r x<256 := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  change ProcPriorVerticalMemorySound.LocalV (raw tr) 0 pub at hv
  have hb:=ProcPriorRecordSound.flag hv hr hs topLimb (by simp)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl
  · exact byte_bound view hpubV hpubR hw hT hbytes hr (j:=0) (by decide) hs hword (by omega)
  · exact byte_bound view hpubV hpubR hw hT hbytes hr (j:=1) (by decide) hs hword (by omega)
  · by_cases ht1:cv (raw tr) 0 r topLimb=1
    · have hz:=ProcPriorRecordPacked.top_zero hv hr hs ht1
      omega
    · exact byte_bound view hpubV hpubR hw hT hbytes hr (j:=2) (by decide) hs hword (by omega)
theorem word_bounds {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpubV:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubR:∀msg,pubCount AP pub 75 true msg=0)
    {es:List ValE} (hw:ValWf es)
    (hT:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hbytes:∀e∈es,∀b∈e.bytes,b<256)
    {r:Nat} (hr:r<tr.height 0)
    (hs:cv (raw tr) 0 r (ProcPriorVertical4Linear.stage 3)=1)
    (hf:cv (raw tr) 0 r firstLimb=1) :
    cv (raw tr) 0 r lo<16777216 ∧ cv (raw tr) 0 r mid<16777216 ∧
      cv (raw tr) 0 r hi<65536 ∧
      cv (raw tr) 0 r lo+16777216*cv (raw tr) 0 r mid+281474976710656*cv (raw tr) 0 r hi<18446744073709551616 := by
  have hv:=ProcessRepairRawBytes.overlay_local view
  change ProcPriorVerticalMemorySound.LocalV (raw tr) 0 pub at hv
  have word (q g:Nat) (hq:q<tr.height 0) (hst:cv (raw tr) 0 q (ProcPriorVertical4Linear.stage 3)=1)
      (hg:g∈[firstLimb,midLimb,topLimb]) (hflag:cv (raw tr) 0 q g=1):
      cv (raw tr) 0 q sender+cv (raw tr) 0 q receiver+cv (raw tr) 0 q amount=1:=by
    have hl:=ProcPriorRecordGeometry.limbs_eq hv hq hst
    have hw:=ProcPriorRecordGeometry.words_bound hv hq hst
    have ha:=ProcPriorRecordSound.flag hv hq hst act (by simp)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl <;> omega
  obtain ⟨hr1,hs1,_,hm1,_⟩:=ProcPriorRecordWordTraversal.limb_next hv hr hs firstLimb midLimb (by simp) hf
  obtain ⟨hr2,hs2,_,ht2,_⟩:=ProcPriorRecordWordTraversal.limb_next hv hr1 hs1 midLimb topLimb (by simp) hm1
  simp only [Nat.add_assoc,Nat.reduceAdd] at hr2 hs2 ht2
  have hb0:=row_bounds view hpubV hpubR hw hT hbytes hr hs (word r firstLimb hr hs (by simp) hf)
  have hb1:=row_bounds view hpubV hpubR hw hT hbytes hr1 hs1 (word (r+1) midLimb hr1 hs1 (by simp) hm1)
  have hb2:=row_bounds view hpubV hpubR hw hT hbytes hr2 hs2 (word (r+2) topLimb hr2 hs2 (by simp) ht2)
  apply (ProcPriorRecordWordTraversal.word_bounds hv hr hs hf ?_).2
  intro j hj x hx
  have h:j=0∨j=1∨j=2:=by omega
  rcases h with rfl|rfl|rfl
  · exact hb0 x hx
  · exact hb1 x hx
  · exact hb2 x hx
end ZkFormal.NearV3.Candidates.ProcessRepairRecordPhysicalBytes
